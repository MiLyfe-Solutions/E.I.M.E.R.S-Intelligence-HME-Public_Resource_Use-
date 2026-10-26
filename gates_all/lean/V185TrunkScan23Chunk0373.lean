import V185TrunkScan23Chunk0372

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2205241 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_2205241 : Nat := 118140960795 + 2205241 * 2 ^ 59
def prefixEnd_2205241 : Nat := 4983230072969 + 3 ^ 40 * 2205241 * 2
def baseEnd_2205241 : Nat := 377449530667237239381929

theorem tailTrace_2205241 : CollatzResearch.WordTrace tailWord_2205241 prefixEnd_2205241 377449530667237239381929 := by
  unfold tailWord_2205241
  simp only [CollatzResearch.WordTrace]
  refine ⟨80431747003795957023247577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53621164669197304682165051 80431747003795957023247577)
  ·
    refine ⟨60323810252846967767435683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80431747003795957023247577 60323810252846967767435683)
    ·
      refine ⟨90485715379270451651153525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60323810252846967767435683 90485715379270451651153525)
      ·
        refine ⟨8483035816806604842295643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90485715379270451651153525 8483035816806604842295643)
        ·
          refine ⟨12724553725209907263443465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8483035816806604842295643 12724553725209907263443465)
          ·
            refine ⟨9543415293907430447582599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12724553725209907263443465 9543415293907430447582599)
            ·
              refine ⟨14315122940861145671373899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9543415293907430447582599 14315122940861145671373899)
              ·
                refine ⟨21472684411291718507060849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14315122940861145671373899 21472684411291718507060849)
                ·
                  refine ⟨16104513308468788880295637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21472684411291718507060849 16104513308468788880295637)
                  ·
                    refine ⟨377449530667237239381929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16104513308468788880295637 377449530667237239381929)
                    ·
                      rfl

theorem cell23_2205241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_2205241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205241 prefixEnd_2205241 := by exact prefixLift 2205241
  have htrace : WordTrace (prefixWord ++ tailWord_2205241) baseStart_2205241 baseEnd_2205241 := by
    simpa [prefixWord, tailWord_2205241, baseEnd_2205241] using wordTrace_append hprefix tailTrace_2205241
  have hstable : (prefixWord ++ tailWord_2205241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205241).length < 2 ^ (prefixWord ++ tailWord_2205241).sum := by decide
  have hdescent : baseEnd_2205241 < baseStart_2205241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205245 : List Nat := [1, 4, 1, 3, 4, 1, 1, 8]
def baseStart_2205245 : Nat := 118140960795 + 2205245 * 2 ^ 59
def prefixEnd_2205245 : Nat := 4983230072969 + 3 ^ 40 * 2205245 * 2
def baseEnd_2205245 : Nat := 41938912812012211203547

theorem tailTrace_2205245 : CollatzResearch.WordTrace tailWord_2205245 prefixEnd_2205245 41938912812012211203547 := by
  unfold tailWord_2205245
  simp only [CollatzResearch.WordTrace]
  refine ⟨80431892895781465706393189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53621261930520977137595459 80431892895781465706393189)
  ·
    refine ⟨15080979917959024819948723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80431892895781465706393189 15080979917959024819948723)
    ·
      refine ⟨22621469876938537229923085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15080979917959024819948723 22621469876938537229923085)
      ·
        refine ⟨8483051203851951461221157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22621469876938537229923085 8483051203851951461221157)
        ·
          refine ⟨1590572100722240898978967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8483051203851951461221157 1590572100722240898978967)
          ·
            refine ⟨2385858151083361348468451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590572100722240898978967 2385858151083361348468451)
            ·
              refine ⟨3578787226625042022702677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385858151083361348468451 3578787226625042022702677)
              ·
                refine ⟨41938912812012211203547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3578787226625042022702677 41938912812012211203547)
                ·
                  rfl

theorem cell23_2205245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 8].length) (baseStart_2205245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205245 prefixEnd_2205245 := by exact prefixLift 2205245
  have htrace : WordTrace (prefixWord ++ tailWord_2205245) baseStart_2205245 baseEnd_2205245 := by
    simpa [prefixWord, tailWord_2205245, baseEnd_2205245] using wordTrace_append hprefix tailTrace_2205245
  have hstable : (prefixWord ++ tailWord_2205245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205245).length < 2 ^ (prefixWord ++ tailWord_2205245).sum := by decide
  have hdescent : baseEnd_2205245 < baseStart_2205245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205255 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_2205255 : Nat := 118140960795 + 2205255 * 2 ^ 59
def prefixEnd_2205255 : Nat := 4983230072969 + 3 ^ 40 * 2205255 * 2
def baseEnd_2205255 : Nat := 1132355780730874663370723

theorem tailTrace_2205255 : CollatzResearch.WordTrace tailWord_2205255 prefixEnd_2205255 1132355780730874663370723 := by
  unfold tailWord_2205255
  simp only [CollatzResearch.WordTrace]
  refine ⟨80432257625745237414257219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53621505083830158276171479 80432257625745237414257219)
  ·
    refine ⟨120648386438617856121385829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80432257625745237414257219 120648386438617856121385829)
    ·
      refine ⟨22621572457240848022759843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120648386438617856121385829 22621572457240848022759843)
      ·
        refine ⟨33932358685861272034139765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22621572457240848022759843 33932358685861272034139765)
        ·
          refine ⟨3181158626799494253200603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33932358685861272034139765 3181158626799494253200603)
          ·
            refine ⟨4771737940199241379800905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181158626799494253200603 4771737940199241379800905)
            ·
              refine ⟨3578803455149431034850679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4771737940199241379800905 3578803455149431034850679)
              ·
                refine ⟨5368205182724146552276019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578803455149431034850679 5368205182724146552276019)
                ·
                  refine ⟨8052307774086219828414029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5368205182724146552276019 8052307774086219828414029)
                  ·
                    refine ⟨3019615415282332435655261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8052307774086219828414029 3019615415282332435655261)
                    ·
                      refine ⟨1132355780730874663370723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019615415282332435655261 1132355780730874663370723)
                      ·
                        rfl

theorem cell23_2205255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_2205255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205255 prefixEnd_2205255 := by exact prefixLift 2205255
  have htrace : WordTrace (prefixWord ++ tailWord_2205255) baseStart_2205255 baseEnd_2205255 := by
    simpa [prefixWord, tailWord_2205255, baseEnd_2205255] using wordTrace_append hprefix tailTrace_2205255
  have hstable : (prefixWord ++ tailWord_2205255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205255).length < 2 ^ (prefixWord ++ tailWord_2205255).sum := by decide
  have hdescent : baseEnd_2205255 < baseStart_2205255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205265 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_2205265 : Nat := 118140960795 + 2205265 * 2 ^ 59
def prefixEnd_2205265 : Nat := 4983230072969 + 3 ^ 40 * 2205265 * 2
def baseEnd_2205265 : Nat := 1132360915537419624245677

theorem tailTrace_2205265 : CollatzResearch.WordTrace tailWord_2205265 prefixEnd_2205265 1132360915537419624245677 := by
  unfold tailWord_2205265
  simp only [CollatzResearch.WordTrace]
  refine ⟨80432622355709009122121249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53621748237139339414747499 80432622355709009122121249)
  ·
    refine ⟨60324466766781756841590937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80432622355709009122121249 60324466766781756841590937)
    ·
      refine ⟨45243350075086317631193203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60324466766781756841590937 45243350075086317631193203)
      ·
        refine ⟨67865025112629476446789805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45243350075086317631193203 67865025112629476446789805)
        ·
          refine ⟨25449384417236053667546177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67865025112629476446789805 25449384417236053667546177)
          ·
            refine ⟨19087038312927040250659633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25449384417236053667546177 19087038312927040250659633)
            ·
              refine ⟨14315278734695280187994725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19087038312927040250659633 14315278734695280187994725)
              ·
                refine ⟨2684114762755365035249011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14315278734695280187994725 2684114762755365035249011)
                ·
                  refine ⟨4026172144133047552873517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684114762755365035249011 4026172144133047552873517)
                  ·
                    refine ⟨1509814554049892832327569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4026172144133047552873517 1509814554049892832327569)
                    ·
                      refine ⟨1132360915537419624245677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509814554049892832327569 1132360915537419624245677)
                      ·
                        rfl

theorem cell23_2205265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_2205265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205265 prefixEnd_2205265 := by exact prefixLift 2205265
  have htrace : WordTrace (prefixWord ++ tailWord_2205265) baseStart_2205265 baseEnd_2205265 := by
    simpa [prefixWord, tailWord_2205265, baseEnd_2205265] using wordTrace_append hprefix tailTrace_2205265
  have hstable : (prefixWord ++ tailWord_2205265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205265).length < 2 ^ (prefixWord ++ tailWord_2205265).sum := by decide
  have hdescent : baseEnd_2205265 < baseStart_2205265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205281 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2205281 : Nat := 118140960795 + 2205281 * 2 ^ 59
def prefixEnd_2205281 : Nat := 4983230072969 + 3 ^ 40 * 2205281 * 2
def baseEnd_2205281 : Nat := 1132369131227891561645603

theorem tailTrace_2205281 : CollatzResearch.WordTrace tailWord_2205281 prefixEnd_2205281 1132369131227891561645603 := by
  unfold tailWord_2205281
  simp only [CollatzResearch.WordTrace]
  refine ⟨80433205923651043854703697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53622137282434029236469131 80433205923651043854703697)
  ·
    refine ⟨60324904442738282891027773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80433205923651043854703697 60324904442738282891027773)
    ·
      refine ⟨22621839166026856084135415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60324904442738282891027773 22621839166026856084135415)
      ·
        refine ⟨33932758749040284126203123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22621839166026856084135415 33932758749040284126203123)
        ·
          refine ⟨50899138123560426189304685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33932758749040284126203123 50899138123560426189304685)
          ·
            refine ⟨19087176796335159820989257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50899138123560426189304685 19087176796335159820989257)
            ·
              refine ⟨14315382597251369865741943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19087176796335159820989257 14315382597251369865741943)
              ·
                refine ⟨21473073895877054798612915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14315382597251369865741943 21473073895877054798612915)
                ·
                  refine ⟨32209610843815582197919373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21473073895877054798612915 32209610843815582197919373)
                  ·
                    refine ⟨12078604066430843324219765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32209610843815582197919373 12078604066430843324219765)
                    ·
                      refine ⟨1132369131227891561645603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12078604066430843324219765 1132369131227891561645603)
                      ·
                        rfl

theorem cell23_2205281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2205281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205281 prefixEnd_2205281 := by exact prefixLift 2205281
  have htrace : WordTrace (prefixWord ++ tailWord_2205281) baseStart_2205281 baseEnd_2205281 := by
    simpa [prefixWord, tailWord_2205281, baseEnd_2205281] using wordTrace_append hprefix tailTrace_2205281
  have hstable : (prefixWord ++ tailWord_2205281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205281).length < 2 ^ (prefixWord ++ tailWord_2205281).sum := by decide
  have hdescent : baseEnd_2205281 < baseStart_2205281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205288 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2205288 : Nat := 118140960795 + 2205288 * 2 ^ 59
def prefixEnd_2205288 : Nat := 4983230072969 + 3 ^ 40 * 2205288 * 2
def baseEnd_2205288 : Nat := 377457575197491011419357

theorem tailTrace_2205288 : CollatzResearch.WordTrace tailWord_2205288 prefixEnd_2205288 377457575197491011419357 := by
  unfold tailWord_2205288
  simp only [CollatzResearch.WordTrace]
  refine ⟨40216730617312842025104259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53622307489750456033472345 40216730617312842025104259)
  ·
    refine ⟨60325095925969263037656389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40216730617312842025104259 60325095925969263037656389)
    ·
      refine ⟨11310955486119236819560573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60325095925969263037656389 11310955486119236819560573)
      ·
        refine ⟨4241608307294713807335215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11310955486119236819560573 4241608307294713807335215)
        ·
          refine ⟨6362412460942070711002823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241608307294713807335215 6362412460942070711002823)
          ·
            refine ⟨9543618691413106066504235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6362412460942070711002823 9543618691413106066504235)
            ·
              refine ⟨14315428037119659099756353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9543618691413106066504235 14315428037119659099756353)
              ·
                refine ⟨10736571027839744324817265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14315428037119659099756353 10736571027839744324817265)
                ·
                  refine ⟨8052428270879808243612949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10736571027839744324817265 8052428270879808243612949)
                  ·
                    refine ⟨377457575197491011419357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8052428270879808243612949 377457575197491011419357)
                    ·
                      rfl

theorem cell23_2205288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2205288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205288 prefixEnd_2205288 := by exact prefixLift 2205288
  have htrace : WordTrace (prefixWord ++ tailWord_2205288) baseStart_2205288 baseEnd_2205288 := by
    simpa [prefixWord, tailWord_2205288, baseEnd_2205288] using wordTrace_append hprefix tailTrace_2205288
  have hstable : (prefixWord ++ tailWord_2205288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205288).length < 2 ^ (prefixWord ++ tailWord_2205288).sum := by decide
  have hdescent : baseEnd_2205288 < baseStart_2205288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205335 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 5]
def baseStart_2205335 : Nat := 118140960795 + 2205335 * 2 ^ 59
def prefixEnd_2205335 : Nat := 4983230072969 + 3 ^ 40 * 2205335 * 2
def baseEnd_2205335 : Nat := 125821873242581594485595

theorem tailTrace_2205335 : CollatzResearch.WordTrace tailWord_2205335 prefixEnd_2205335 125821873242581594485595 := by
  unfold tailWord_2205335
  simp only [CollatzResearch.WordTrace]
  refine ⟨80435175465455411077169459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53623450310303607384779639 80435175465455411077169459)
  ·
    refine ⟨120652763198183116615754189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80435175465455411077169459 120652763198183116615754189)
    ·
      refine ⟨45244786199318668730907821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120652763198183116615754189 45244786199318668730907821)
      ·
        refine ⟨16966794824744500774090433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45244786199318668730907821 16966794824744500774090433)
        ·
          refine ⟨12725096118558375580567825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16966794824744500774090433 12725096118558375580567825)
          ·
            refine ⟨9543822088918781685425869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12725096118558375580567825 9543822088918781685425869)
            ·
              refine ⟨3578933283344543132034701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9543822088918781685425869 3578933283344543132034701)
              ·
                refine ⟨1342099981254203674513013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3578933283344543132034701 1342099981254203674513013)
                ·
                  refine ⟨125821873242581594485595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1342099981254203674513013 125821873242581594485595)
                  ·
                    rfl

theorem cell23_2205335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 5].length) (baseStart_2205335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205335 prefixEnd_2205335 := by exact prefixLift 2205335
  have htrace : WordTrace (prefixWord ++ tailWord_2205335) baseStart_2205335 baseEnd_2205335 := by
    simpa [prefixWord, tailWord_2205335, baseEnd_2205335] using wordTrace_append hprefix tailTrace_2205335
  have hstable : (prefixWord ++ tailWord_2205335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205335).length < 2 ^ (prefixWord ++ tailWord_2205335).sum := by decide
  have hdescent : baseEnd_2205335 < baseStart_2205335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205348 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_2205348 : Nat := 118140960795 + 2205348 * 2 ^ 59
def prefixEnd_2205348 : Nat := 4983230072969 + 3 ^ 40 * 2205348 * 2
def baseEnd_2205348 : Nat := 377467844810580933169265

theorem tailTrace_2205348 : CollatzResearch.WordTrace tailWord_2205348 prefixEnd_2205348 377467844810580933169265 := by
  unfold tailWord_2205348
  simp only [CollatzResearch.WordTrace]
  refine ⟨40217824807204157148696349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53623766409605542864928465 40217824807204157148696349)
  ·
    refine ⟨15081684302701558930761131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40217824807204157148696349 15081684302701558930761131)
    ·
      refine ⟨22622526454052338396141697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15081684302701558930761131 22622526454052338396141697)
      ·
        refine ⟨16966894840539253797106273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22622526454052338396141697 16966894840539253797106273)
        ·
          refine ⟨12725171130404440347829705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16966894840539253797106273 12725171130404440347829705)
          ·
            refine ⟨9543878347803330260872279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12725171130404440347829705 9543878347803330260872279)
            ·
              refine ⟨14315817521704995391308419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9543878347803330260872279 14315817521704995391308419)
              ·
                refine ⟨21473726282557493086962629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14315817521704995391308419 21473726282557493086962629)
                ·
                  refine ⟨4026323677979529953805493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21473726282557493086962629 4026323677979529953805493)
                  ·
                    refine ⟨377467844810580933169265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4026323677979529953805493 377467844810580933169265)
                    ·
                      rfl

theorem cell23_2205348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_2205348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205348 prefixEnd_2205348 := by exact prefixLift 2205348
  have htrace : WordTrace (prefixWord ++ tailWord_2205348) baseStart_2205348 baseEnd_2205348 := by
    simpa [prefixWord, tailWord_2205348, baseEnd_2205348] using wordTrace_append hprefix tailTrace_2205348
  have hstable : (prefixWord ++ tailWord_2205348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205348).length < 2 ^ (prefixWord ++ tailWord_2205348).sum := by decide
  have hdescent : baseEnd_2205348 < baseStart_2205348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205371 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_2205371 : Nat := 118140960795 + 2205371 * 2 ^ 59
def prefixEnd_2205371 : Nat := 4983230072969 + 3 ^ 40 * 2205371 * 2
def baseEnd_2205371 : Nat := 1132415344486796209520189

theorem tailTrace_2205371 : CollatzResearch.WordTrace tailWord_2205371 prefixEnd_2205371 1132415344486796209520189 := by
  unfold tailWord_2205371
  simp only [CollatzResearch.WordTrace]
  refine ⟨80436488493324989225479967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53624325662216659483653311 80436488493324989225479967)
  ·
    refine ⟨120654732739987483838219951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80436488493324989225479967 120654732739987483838219951)
    ·
      refine ⟨180982099109981225757329927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120654732739987483838219951 180982099109981225757329927)
      ·
        refine ⟨271473148664971838635994891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180982099109981225757329927 271473148664971838635994891)
        ·
          refine ⟨407209722997457757953992337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271473148664971838635994891 407209722997457757953992337)
          ·
            refine ⟨305407292248093318465494253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407209722997457757953992337 305407292248093318465494253)
            ·
              refine ⟨114527734593034994424560345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305407292248093318465494253 114527734593034994424560345)
              ·
                refine ⟨85895800944776245818420259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114527734593034994424560345 85895800944776245818420259)
                ·
                  refine ⟨128843701417164368727630389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85895800944776245818420259 128843701417164368727630389)
                  ·
                    refine ⟨12079097007859159568215349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128843701417164368727630389 12079097007859159568215349)
                    ·
                      refine ⟨1132415344486796209520189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12079097007859159568215349 1132415344486796209520189)
                      ·
                        rfl

theorem cell23_2205371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_2205371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205371 prefixEnd_2205371 := by exact prefixLift 2205371
  have htrace : WordTrace (prefixWord ++ tailWord_2205371) baseStart_2205371 baseEnd_2205371 := by
    simpa [prefixWord, tailWord_2205371, baseEnd_2205371] using wordTrace_append hprefix tailTrace_2205371
  have hstable : (prefixWord ++ tailWord_2205371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205371).length < 2 ^ (prefixWord ++ tailWord_2205371).sum := by decide
  have hdescent : baseEnd_2205371 < baseStart_2205371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205391 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 10]
def baseStart_2205391 : Nat := 118140960795 + 2205391 * 2 ^ 59
def prefixEnd_2205391 : Nat := 4983230072969 + 3 ^ 40 * 2205391 * 2
def baseEnd_2205391 : Nat := 125825068233320681252233

theorem tailTrace_2205391 : CollatzResearch.WordTrace tailWord_2205391 prefixEnd_2205391 125825068233320681252233 := by
  unfold tailWord_2205391
  simp only [CollatzResearch.WordTrace]
  refine ⟨80437217953252532641208027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53624811968835021760805351 80437217953252532641208027)
  ·
    refine ⟨120655826929878798961812041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80437217953252532641208027 120655826929878798961812041)
    ·
      refine ⟨90491870197409099221359031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120655826929878798961812041 90491870197409099221359031)
      ·
        refine ⟨135737805296113648832038547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90491870197409099221359031 135737805296113648832038547)
        ·
          refine ⟨203606707944170473248057821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135737805296113648832038547 203606707944170473248057821)
          ·
            refine ⟨76352515479063927468021683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203606707944170473248057821 76352515479063927468021683)
            ·
              refine ⟨114528773218595891202032525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76352515479063927468021683 114528773218595891202032525)
              ·
                refine ⟨42948289956973459200762197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114528773218595891202032525 42948289956973459200762197)
                ·
                  refine ⟨125825068233320681252233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42948289956973459200762197 125825068233320681252233)
                  ·
                    rfl

theorem cell23_2205391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 10].length) (baseStart_2205391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205391 prefixEnd_2205391 := by exact prefixLift 2205391
  have htrace : WordTrace (prefixWord ++ tailWord_2205391) baseStart_2205391 baseEnd_2205391 := by
    simpa [prefixWord, tailWord_2205391, baseEnd_2205391] using wordTrace_append hprefix tailTrace_2205391
  have hstable : (prefixWord ++ tailWord_2205391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205391).length < 2 ^ (prefixWord ++ tailWord_2205391).sum := by decide
  have hdescent : baseEnd_2205391 < baseStart_2205391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205408 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 6]
def baseStart_2205408 : Nat := 118140960795 + 2205408 * 2 ^ 59
def prefixEnd_2205408 : Nat := 4983230072969 + 3 ^ 40 * 2205408 * 2
def baseEnd_2205408 : Nat := 125826038141223618306391

theorem tailTrace_2205408 : CollatzResearch.WordTrace tailWord_2205408 prefixEnd_2205408 125826038141223618306391 := by
  unfold tailWord_2205408
  simp only [CollatzResearch.WordTrace]
  refine ⟨40218918997095472272288439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53625225329460629696384585 40218918997095472272288439)
  ·
    refine ⟨60328378495643208408432659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40218918997095472272288439 60328378495643208408432659)
    ·
      refine ⟨90492567743464812612648989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60328378495643208408432659 90492567743464812612648989)
      ·
        refine ⟨33934712903799304729743371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90492567743464812612648989 33934712903799304729743371)
        ·
          refine ⟨50902069355698957094615057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33934712903799304729743371 50902069355698957094615057)
          ·
            refine ⟨38176552016774217820961293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50902069355698957094615057 38176552016774217820961293)
            ·
              refine ⟨14316207006290331682860485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38176552016774217820961293 14316207006290331682860485)
              ·
                refine ⟨2684288813679437190536341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14316207006290331682860485 2684288813679437190536341)
                ·
                  refine ⟨125826038141223618306391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2684288813679437190536341 125826038141223618306391)
                  ·
                    rfl

theorem cell23_2205408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_2205408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205408 prefixEnd_2205408 := by exact prefixLift 2205408
  have htrace : WordTrace (prefixWord ++ tailWord_2205408) baseStart_2205408 baseEnd_2205408 := by
    simpa [prefixWord, tailWord_2205408, baseEnd_2205408] using wordTrace_append hprefix tailTrace_2205408
  have hstable : (prefixWord ++ tailWord_2205408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205408).length < 2 ^ (prefixWord ++ tailWord_2205408).sum := by decide
  have hdescent : baseEnd_2205408 < baseStart_2205408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205412 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_2205412 : Nat := 118140960795 + 2205412 * 2 ^ 59
def prefixEnd_2205412 : Nat := 4983230072969 + 3 ^ 40 * 2205412 * 2
def baseEnd_2205412 : Nat := 377478799064543516369167

theorem tailTrace_2205412 : CollatzResearch.WordTrace tailWord_2205412 prefixEnd_2205412 377478799064543516369167 := by
  unfold tailWord_2205412
  simp only [CollatzResearch.WordTrace]
  refine ⟨40218991943088226613861245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53625322590784302151814993 40218991943088226613861245)
  ·
    refine ⟨15082121978658084980197967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40218991943088226613861245 15082121978658084980197967)
    ·
      refine ⟨22623182967987127470296951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15082121978658084980197967 22623182967987127470296951)
      ·
        refine ⟨33934774451980691205445427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22623182967987127470296951 33934774451980691205445427)
        ·
          refine ⟨50902161677971036808168141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33934774451980691205445427 50902161677971036808168141)
          ·
            refine ⟨19088310629239138803063053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50902161677971036808168141 19088310629239138803063053)
            ·
              refine ⟨7158116485964677051148645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19088310629239138803063053 7158116485964677051148645)
              ·
                refine ⟨1342146841118376947090371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7158116485964677051148645 1342146841118376947090371)
                ·
                  refine ⟨2013220261677565420635557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342146841118376947090371 2013220261677565420635557)
                  ·
                    refine ⟨377478799064543516369167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013220261677565420635557 377478799064543516369167)
                    ·
                      rfl

theorem cell23_2205412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_2205412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205412 prefixEnd_2205412 := by exact prefixLift 2205412
  have htrace : WordTrace (prefixWord ++ tailWord_2205412) baseStart_2205412 baseEnd_2205412 := by
    simpa [prefixWord, tailWord_2205412, baseEnd_2205412] using wordTrace_append hprefix tailTrace_2205412
  have hstable : (prefixWord ++ tailWord_2205412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205412).length < 2 ^ (prefixWord ++ tailWord_2205412).sum := by decide
  have hdescent : baseEnd_2205412 < baseStart_2205412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205502 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2205502 : Nat := 118140960795 + 2205502 * 2 ^ 59
def prefixEnd_2205502 : Nat := 4983230072969 + 3 ^ 40 * 2205502 * 2
def baseEnd_2205502 : Nat := 377494203484178398994029

theorem tailTrace_2205502 : CollatzResearch.WordTrace tailWord_2205502 prefixEnd_2205502 377494203484178398994029 := by
  unfold tailWord_2205502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055158306981299824812345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53627510970566932398999173 10055158306981299824812345)
  ·
    refine ⟨7541368730235974868609259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10055158306981299824812345 7541368730235974868609259)
    ·
      refine ⟨11312053095353962302913889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541368730235974868609259 11312053095353962302913889)
      ·
        refine ⟨8484039821515471727185417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11312053095353962302913889 8484039821515471727185417)
        ·
          refine ⟨6363029866136603795389063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8484039821515471727185417 6363029866136603795389063)
          ·
            refine ⟨9544544799204905693083595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363029866136603795389063 9544544799204905693083595)
            ·
              refine ⟨14316817198807358539625393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9544544799204905693083595 14316817198807358539625393)
              ·
                refine ⟨10737612899105518904719045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14316817198807358539625393 10737612899105518904719045)
                ·
                  refine ⟨2013302418582284794634821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10737612899105518904719045 2013302418582284794634821)
                  ·
                    refine ⟨377494203484178398994029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013302418582284794634821 377494203484178398994029)
                    ·
                      rfl

theorem cell23_2205502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2205502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205502 prefixEnd_2205502 := by exact prefixLift 2205502
  have htrace : WordTrace (prefixWord ++ tailWord_2205502) baseStart_2205502 baseEnd_2205502 := by
    simpa [prefixWord, tailWord_2205502, baseEnd_2205502] using wordTrace_append hprefix tailTrace_2205502
  have hstable : (prefixWord ++ tailWord_2205502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205502).length < 2 ^ (prefixWord ++ tailWord_2205502).sum := by decide
  have hdescent : baseEnd_2205502 < baseStart_2205502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205503 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 1, 1, 3]
def baseStart_2205503 : Nat := 118140960795 + 2205503 * 2 ^ 59
def prefixEnd_2205503 : Nat := 4983230072969 + 3 ^ 40 * 2205503 * 2
def baseEnd_2205503 : Nat := 1132483123933189693069583

theorem tailTrace_2205503 : CollatzResearch.WordTrace tailWord_2205503 prefixEnd_2205503 1132483123933189693069583 := by
  unfold tailWord_2205503
  simp only [CollatzResearch.WordTrace]
  refine ⟨80441302928846775769285163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53627535285897850512856775 80441302928846775769285163)
  ·
    refine ⟨120661954393270163653927745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80441302928846775769285163 120661954393270163653927745)
    ·
      refine ⟨90496465794952622740445809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120661954393270163653927745 90496465794952622740445809)
      ·
        refine ⟨67872349346214467055334357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90496465794952622740445809 67872349346214467055334357)
        ·
          refine ⟨1590758187801901571609399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 67872349346214467055334357 1590758187801901571609399)
          ·
            refine ⟨2386137281702852357414099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590758187801901571609399 2386137281702852357414099)
            ·
              refine ⟨3579205922554278536121149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386137281702852357414099 3579205922554278536121149)
              ·
                refine ⟨1342202220957854451045431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3579205922554278536121149 1342202220957854451045431)
                ·
                  refine ⟨2013303331436781676568147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342202220957854451045431 2013303331436781676568147)
                  ·
                    refine ⟨3019954997155172514852221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2013303331436781676568147 3019954997155172514852221)
                    ·
                      refine ⟨1132483123933189693069583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019954997155172514852221 1132483123933189693069583)
                      ·
                        rfl

theorem cell23_2205503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_2205503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205503 prefixEnd_2205503 := by exact prefixLift 2205503
  have htrace : WordTrace (prefixWord ++ tailWord_2205503) baseStart_2205503 baseEnd_2205503 := by
    simpa [prefixWord, tailWord_2205503, baseEnd_2205503] using wordTrace_append hprefix tailTrace_2205503
  have hstable : (prefixWord ++ tailWord_2205503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205503).length < 2 ^ (prefixWord ++ tailWord_2205503).sum := by decide
  have hdescent : baseEnd_2205503 < baseStart_2205503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205512 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_2205512 : Nat := 118140960795 + 2205512 * 2 ^ 59
def prefixEnd_2205512 : Nat := 4983230072969 + 3 ^ 40 * 2205512 * 2
def baseEnd_2205512 : Nat := 1132487745259080157857041

theorem tailTrace_2205512 : CollatzResearch.WordTrace tailWord_2205512 prefixEnd_2205512 1132487745259080157857041 := by
  unfold tailWord_2205512
  simp only [CollatzResearch.WordTrace]
  refine ⟨40220815592907085153181395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53627754123876113537575193 40220815592907085153181395)
  ·
    refine ⟨60331223389360627729772093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40220815592907085153181395 60331223389360627729772093)
    ·
      refine ⟨22624208771010235398664535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60331223389360627729772093 22624208771010235398664535)
      ·
        refine ⟨33936313156515353097996803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22624208771010235398664535 33936313156515353097996803)
        ·
          refine ⟨50904469734773029646995205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33936313156515353097996803 50904469734773029646995205)
          ·
            refine ⟨9544588075269943058811601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50904469734773029646995205 9544588075269943058811601)
            ·
              refine ⟨7158441056452457294108701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544588075269943058811601 7158441056452457294108701)
              ·
                refine ⟨2684415396169671485290763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7158441056452457294108701 2684415396169671485290763)
                ·
                  refine ⟨4026623094254507227936145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684415396169671485290763 4026623094254507227936145)
                  ·
                    refine ⟨3019967320690880420952109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4026623094254507227936145 3019967320690880420952109)
                    ·
                      refine ⟨1132487745259080157857041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019967320690880420952109 1132487745259080157857041)
                      ·
                        rfl

theorem cell23_2205512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_2205512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205512 prefixEnd_2205512 := by exact prefixLift 2205512
  have htrace : WordTrace (prefixWord ++ tailWord_2205512) baseStart_2205512 baseEnd_2205512 := by
    simpa [prefixWord, tailWord_2205512, baseEnd_2205512] using wordTrace_append hprefix tailTrace_2205512
  have hstable : (prefixWord ++ tailWord_2205512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205512).length < 2 ^ (prefixWord ++ tailWord_2205512).sum := by decide
  have hdescent : baseEnd_2205512 < baseStart_2205512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205532 : List Nat := [2, 2, 4, 2, 2, 1, 2, 8]
def baseStart_2205532 : Nat := 118140960795 + 2205532 * 2 ^ 59
def prefixEnd_2205532 : Nat := 4983230072969 + 3 ^ 40 * 2205532 * 2
def baseEnd_2205532 : Nat := 41944370921191484429887

theorem tailTrace_2205532 : CollatzResearch.WordTrace tailWord_2205532 prefixEnd_2205532 41944370921191484429887 := by
  unfold tailWord_2205532
  simp only [CollatzResearch.WordTrace]
  refine ⟨40221180322870856861045425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53628240430494475814727233 40221180322870856861045425)
  ·
    refine ⟨30165885242153142645784069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40221180322870856861045425 30165885242153142645784069)
    ·
      refine ⟨5656103482903714246084513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30165885242153142645784069 5656103482903714246084513)
      ·
        refine ⟨4242077612177785684563385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5656103482903714246084513 4242077612177785684563385)
        ·
          refine ⟨3181558209133339263422539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4242077612177785684563385 3181558209133339263422539)
          ·
            refine ⟨4772337313700008895133809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181558209133339263422539 4772337313700008895133809)
            ·
              refine ⟨3579252985275006671350357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772337313700008895133809 3579252985275006671350357)
              ·
                refine ⟨41944370921191484429887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3579252985275006671350357 41944370921191484429887)
                ·
                  rfl

theorem cell23_2205532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 8].length) (baseStart_2205532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205532 prefixEnd_2205532 := by exact prefixLift 2205532
  have htrace : WordTrace (prefixWord ++ tailWord_2205532) baseStart_2205532 baseEnd_2205532 := by
    simpa [prefixWord, tailWord_2205532, baseEnd_2205532] using wordTrace_append hprefix tailTrace_2205532
  have hstable : (prefixWord ++ tailWord_2205532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205532).length < 2 ^ (prefixWord ++ tailWord_2205532).sum := by decide
  have hdescent : baseEnd_2205532 < baseStart_2205532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205576 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2205576 : Nat := 118140960795 + 2205576 * 2 ^ 59
def prefixEnd_2205576 : Nat := 4983230072969 + 3 ^ 40 * 2205576 * 2
def baseEnd_2205576 : Nat := 1132520608020967907456747

theorem tailTrace_2205576 : CollatzResearch.WordTrace tailWord_2205576 prefixEnd_2205576 1132520608020967907456747 := by
  unfold tailWord_2205576
  simp only [CollatzResearch.WordTrace]
  refine ⟨40221982728791154618346291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53629310305054872824461721 40221982728791154618346291)
  ·
    refine ⟨60332974093186731927519437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40221982728791154618346291 60332974093186731927519437)
    ·
      refine ⟨22624865284945024472819789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60332974093186731927519437 22624865284945024472819789)
      ·
        refine ⟨8484324481854384177307421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22624865284945024472819789 8484324481854384177307421)
        ·
          refine ⟨3181621680695394066490283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8484324481854384177307421 3181621680695394066490283)
          ·
            refine ⟨4772432521043091099735425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181621680695394066490283 4772432521043091099735425)
            ·
              refine ⟨3579324390782318324801569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772432521043091099735425 3579324390782318324801569)
              ·
                refine ⟨2684493293086738743601177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579324390782318324801569 2684493293086738743601177)
                ·
                  refine ⟨2013369969815054057700883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684493293086738743601177 2013369969815054057700883)
                  ·
                    refine ⟨3020054954722581086551325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2013369969815054057700883 3020054954722581086551325)
                    ·
                      refine ⟨1132520608020967907456747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020054954722581086551325 1132520608020967907456747)
                      ·
                        rfl

theorem cell23_2205576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2205576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205576 prefixEnd_2205576 := by exact prefixLift 2205576
  have htrace : WordTrace (prefixWord ++ tailWord_2205576) baseStart_2205576 baseEnd_2205576 := by
    simpa [prefixWord, tailWord_2205576, baseEnd_2205576] using wordTrace_append hprefix tailTrace_2205576
  have hstable : (prefixWord ++ tailWord_2205576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205576).length < 2 ^ (prefixWord ++ tailWord_2205576).sum := by decide
  have hdescent : baseEnd_2205576 < baseStart_2205576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205585 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_2205585 : Nat := 118140960795 + 2205585 * 2 ^ 59
def prefixEnd_2205585 : Nat := 4983230072969 + 3 ^ 40 * 2205585 * 2
def baseEnd_2205585 : Nat := 1132525229346858372244205

theorem tailTrace_2205585 : CollatzResearch.WordTrace tailWord_2205585 prefixEnd_2205585 1132525229346858372244205 := by
  unfold tailWord_2205585
  simp only [CollatzResearch.WordTrace]
  refine ⟨80444293714549703773770209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53629529143033135849180139 80444293714549703773770209)
  ·
    refine ⟨60333220285912277830327657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80444293714549703773770209 60333220285912277830327657)
    ·
      refine ⟨45249915214434208372745743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60333220285912277830327657 45249915214434208372745743)
      ·
        refine ⟨67874872821651312559118615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45249915214434208372745743 67874872821651312559118615)
        ·
          refine ⟨101812309232476968838677923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67874872821651312559118615 101812309232476968838677923)
          ·
            refine ⟨152718463848715453258016885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101812309232476968838677923 152718463848715453258016885)
            ·
              refine ⟨14317355985817073742939083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152718463848715453258016885 14317355985817073742939083)
              ·
                refine ⟨21476033978725610614408625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14317355985817073742939083 21476033978725610614408625)
                ·
                  refine ⟨16107025484044207960806469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21476033978725610614408625 16107025484044207960806469)
                  ·
                    refine ⟨3020067278258288992651213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16107025484044207960806469 3020067278258288992651213)
                    ·
                      refine ⟨1132525229346858372244205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020067278258288992651213 1132525229346858372244205)
                      ·
                        rfl

theorem cell23_2205585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_2205585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205585 prefixEnd_2205585 := by exact prefixLift 2205585
  have htrace : WordTrace (prefixWord ++ tailWord_2205585) baseStart_2205585 baseEnd_2205585 := by
    simpa [prefixWord, tailWord_2205585, baseEnd_2205585] using wordTrace_append hprefix tailTrace_2205585
  have hstable : (prefixWord ++ tailWord_2205585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205585).length < 2 ^ (prefixWord ++ tailWord_2205585).sum := by decide
  have hdescent : baseEnd_2205585 < baseStart_2205585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205615 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_2205615 : Nat := 118140960795 + 2205615 * 2 ^ 59
def prefixEnd_2205615 : Nat := 4983230072969 + 3 ^ 40 * 2205615 * 2
def baseEnd_2205615 : Nat := 1132540633766493254869067

theorem tailTrace_2205615 : CollatzResearch.WordTrace tailWord_2205615 prefixEnd_2205615 1132540633766493254869067 := by
  unfold tailWord_2205615
  simp only [CollatzResearch.WordTrace]
  refine ⟨80445387904441018897362299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53630258602960679264908199 80445387904441018897362299)
  ·
    refine ⟨120668081856661528346043449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80445387904441018897362299 120668081856661528346043449)
    ·
      refine ⟨90501061392496146259532587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120668081856661528346043449 90501061392496146259532587)
      ·
        refine ⟨135751592088744219389298881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90501061392496146259532587 135751592088744219389298881)
        ·
          refine ⟨101813694066558164541974161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135751592088744219389298881 101813694066558164541974161)
          ·
            refine ⟨76360270549918623406480621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101813694066558164541974161 76360270549918623406480621)
            ·
              refine ⟨28635101456219483777430233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76360270549918623406480621 28635101456219483777430233)
              ·
                refine ⟨21476326092164612833072675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28635101456219483777430233 21476326092164612833072675)
                ·
                  refine ⟨32214489138246919249609013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21476326092164612833072675 32214489138246919249609013)
                  ·
                    refine ⟨3020108356710648679650845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32214489138246919249609013 3020108356710648679650845)
                    ·
                      refine ⟨1132540633766493254869067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020108356710648679650845 1132540633766493254869067)
                      ·
                        rfl

theorem cell23_2205615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_2205615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205615 prefixEnd_2205615 := by exact prefixLift 2205615
  have htrace : WordTrace (prefixWord ++ tailWord_2205615) baseStart_2205615 baseEnd_2205615 := by
    simpa [prefixWord, tailWord_2205615, baseEnd_2205615] using wordTrace_append hprefix tailTrace_2205615
  have hstable : (prefixWord ++ tailWord_2205615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205615).length < 2 ^ (prefixWord ++ tailWord_2205615).sum := by decide
  have hdescent : baseEnd_2205615 < baseStart_2205615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205642 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_2205642 : Nat := 118140960795 + 2205642 * 2 ^ 59
def prefixEnd_2205642 : Nat := 4983230072969 + 3 ^ 40 * 2205642 * 2
def baseEnd_2205642 : Nat := 1132554497744164649231443

theorem tailTrace_2205642 : CollatzResearch.WordTrace tailWord_2205642 prefixEnd_2205642 1132554497744164649231443 := by
  unfold tailWord_2205642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111593168835800627148795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53630915116895468339063453 20111593168835800627148795)
  ·
    refine ⟨30167389753253700940723193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20111593168835800627148795 30167389753253700940723193)
    ·
      refine ⟨22625542314940275705542395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30167389753253700940723193 22625542314940275705542395)
      ·
        refine ⟨33938313472410413558313593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22625542314940275705542395 33938313472410413558313593)
        ·
          refine ⟨25453735104307810168735195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33938313472410413558313593 25453735104307810168735195)
          ·
            refine ⟨38180602656461715253102793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25453735104307810168735195 38180602656461715253102793)
            ·
              refine ⟨28635451992346286439827095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38180602656461715253102793 28635451992346286439827095)
              ·
                refine ⟨42953177988519429659740643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28635451992346286439827095 42953177988519429659740643)
                ·
                  refine ⟨64429766982779144489610965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42953177988519429659740643 64429766982779144489610965)
                  ·
                    refine ⟨1510072663658886198975257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 64429766982779144489610965 1510072663658886198975257)
                    ·
                      refine ⟨1132554497744164649231443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510072663658886198975257 1132554497744164649231443)
                      ·
                        rfl

theorem cell23_2205642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_2205642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205642 prefixEnd_2205642 := by exact prefixLift 2205642
  have htrace : WordTrace (prefixWord ++ tailWord_2205642) baseStart_2205642 baseEnd_2205642 := by
    simpa [prefixWord, tailWord_2205642, baseEnd_2205642] using wordTrace_append hprefix tailTrace_2205642
  have hstable : (prefixWord ++ tailWord_2205642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205642).length < 2 ^ (prefixWord ++ tailWord_2205642).sum := by decide
  have hdescent : baseEnd_2205642 < baseStart_2205642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205650 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2205650 : Nat := 118140960795 + 2205650 * 2 ^ 59
def prefixEnd_2205650 : Nat := 4983230072969 + 3 ^ 40 * 2205650 * 2
def baseEnd_2205650 : Nat := 1132558605589400617931407

theorem tailTrace_2205650 : CollatzResearch.WordTrace tailWord_2205650 prefixEnd_2205650 1132558605589400617931407 := by
  unfold tailWord_2205650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111666114828554968721601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53631109639542813249924269 20111666114828554968721601)
  ·
    refine ⟨15083749586121416226541201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20111666114828554968721601 15083749586121416226541201)
    ·
      refine ⟨11312812189591062169905901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15083749586121416226541201 11312812189591062169905901)
      ·
        refine ⟨4242304571096648313714713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11312812189591062169905901 4242304571096648313714713)
        ·
          refine ⟨3181728428322486235286035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4242304571096648313714713 3181728428322486235286035)
          ·
            refine ⟨4772592642483729352929053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181728428322486235286035 4772592642483729352929053)
            ·
              refine ⟨1789722240931398507348395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4772592642483729352929053 1789722240931398507348395)
              ·
                refine ⟨2684583361397097761022593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789722240931398507348395 2684583361397097761022593)
                ·
                  refine ⟨2013437521047823320766945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684583361397097761022593 2013437521047823320766945)
                  ·
                    refine ⟨1510078140785867490575209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2013437521047823320766945 1510078140785867490575209)
                    ·
                      refine ⟨1132558605589400617931407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510078140785867490575209 1132558605589400617931407)
                      ·
                        rfl

theorem cell23_2205650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2205650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205650 prefixEnd_2205650 := by exact prefixLift 2205650
  have htrace : WordTrace (prefixWord ++ tailWord_2205650) baseStart_2205650 baseEnd_2205650 := by
    simpa [prefixWord, tailWord_2205650, baseEnd_2205650] using wordTrace_append hprefix tailTrace_2205650
  have hstable : (prefixWord ++ tailWord_2205650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205650).length < 2 ^ (prefixWord ++ tailWord_2205650).sum := by decide
  have hdescent : baseEnd_2205650 < baseStart_2205650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205655 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_2205655 : Nat := 118140960795 + 2205655 * 2 ^ 59
def prefixEnd_2205655 : Nat := 4983230072969 + 3 ^ 40 * 2205655 * 2
def baseEnd_2205655 : Nat := 1132561172992673098368883

theorem tailTrace_2205655 : CollatzResearch.WordTrace tailWord_2205655 prefixEnd_2205655 1132561172992673098368883 := by
  unfold tailWord_2205655
  simp only [CollatzResearch.WordTrace]
  refine ⟨80446846824296105728818419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53631231216197403819212279 80446846824296105728818419)
  ·
    refine ⟨120670270236444158593227629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80446846824296105728818419 120670270236444158593227629)
    ·
      refine ⟨45251351338666559472460361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120670270236444158593227629 45251351338666559472460361)
      ·
        refine ⟨33938513503999919604345271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45251351338666559472460361 33938513503999919604345271)
        ·
          refine ⟨50907770255999879406517907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33938513503999919604345271 50907770255999879406517907)
          ·
            refine ⟨76361655383999819109776861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50907770255999879406517907 76361655383999819109776861)
            ·
              refine ⟨28635620768999932166166323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76361655383999819109776861 28635620768999932166166323)
              ·
                refine ⟨42953431153499898249249485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28635620768999932166166323 42953431153499898249249485)
                ·
                  refine ⟨16107536682562461843468557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42953431153499898249249485 16107536682562461843468557)
                  ·
                    refine ⟨6040326255960923191300709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16107536682562461843468557 6040326255960923191300709)
                    ·
                      refine ⟨1132561172992673098368883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6040326255960923191300709 1132561172992673098368883)
                      ·
                        rfl

theorem cell23_2205655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_2205655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205655 prefixEnd_2205655 := by exact prefixLift 2205655
  have htrace : WordTrace (prefixWord ++ tailWord_2205655) baseStart_2205655 baseEnd_2205655 := by
    simpa [prefixWord, tailWord_2205655, baseEnd_2205655] using wordTrace_append hprefix tailTrace_2205655
  have hstable : (prefixWord ++ tailWord_2205655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205655).length < 2 ^ (prefixWord ++ tailWord_2205655).sum := by decide
  have hdescent : baseEnd_2205655 < baseStart_2205655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205672 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2205672 : Nat := 118140960795 + 2205672 * 2 ^ 59
def prefixEnd_2205672 : Nat := 4983230072969 + 3 ^ 40 * 2205672 * 2
def baseEnd_2205672 : Nat := 1132569902163799531856305

theorem tailTrace_2205672 : CollatzResearch.WordTrace tailWord_2205672 prefixEnd_2205672 1132569902163799531856305 := by
  unfold tailWord_2205672
  simp only [CollatzResearch.WordTrace]
  refine ⟨40223733432617258816093635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53631644576823011754791513 40223733432617258816093635)
  ·
    refine ⟨60335600148925888224140453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40223733432617258816093635 60335600148925888224140453)
    ·
      refine ⟨11312925027923604042026335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60335600148925888224140453 11312925027923604042026335)
      ·
        refine ⟨16969387541885406063039503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11312925027923604042026335 16969387541885406063039503)
        ·
          refine ⟨25454081312828109094559255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16969387541885406063039503 25454081312828109094559255)
          ·
            refine ⟨38181121969242163641838883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25454081312828109094559255 38181121969242163641838883)
            ·
              refine ⟨57271682953863245462758325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38181121969242163641838883 57271682953863245462758325)
              ·
                refine ⟨5369220276924679262133593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57271682953863245462758325 5369220276924679262133593)
                ·
                  refine ⟨4026915207693509446600195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5369220276924679262133593 4026915207693509446600195)
                  ·
                    refine ⟨6040372811540264169900293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026915207693509446600195 6040372811540264169900293)
                    ·
                      refine ⟨1132569902163799531856305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6040372811540264169900293 1132569902163799531856305)
                      ·
                        rfl

theorem cell23_2205672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2205672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205672 prefixEnd_2205672 := by exact prefixLift 2205672
  have htrace : WordTrace (prefixWord ++ tailWord_2205672) baseStart_2205672 baseEnd_2205672 := by
    simpa [prefixWord, tailWord_2205672, baseEnd_2205672] using wordTrace_append hprefix tailTrace_2205672
  have hstable : (prefixWord ++ tailWord_2205672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205672).length < 2 ^ (prefixWord ++ tailWord_2205672).sum := by decide
  have hdescent : baseEnd_2205672 < baseStart_2205672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205699 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 1, 4]
def baseStart_2205699 : Nat := 118140960795 + 2205699 * 2 ^ 59
def prefixEnd_2205699 : Nat := 4983230072969 + 3 ^ 40 * 2205699 * 2
def baseEnd_2205699 : Nat := 377527922047156975406227

theorem tailTrace_2205699 : CollatzResearch.WordTrace tailWord_2205699 prefixEnd_2205699 377527922047156975406227 := by
  unfold tailWord_2205699
  simp only [CollatzResearch.WordTrace]
  refine ⟨80448451636136701243420151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53632301090757800828946767 80448451636136701243420151)
  ·
    refine ⟨120672677454205051865130227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80448451636136701243420151 120672677454205051865130227)
    ·
      refine ⟨181009016181307577797695341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120672677454205051865130227 181009016181307577797695341)
      ·
        refine ⟨67878381067990341674135753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181009016181307577797695341 67878381067990341674135753)
        ·
          refine ⟨50908785800992756255601815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67878381067990341674135753 50908785800992756255601815)
          ·
            refine ⟨76363178701489134383402723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50908785800992756255601815 76363178701489134383402723)
            ·
              refine ⟨114544768052233701575104085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76363178701489134383402723 114544768052233701575104085)
              ·
                refine ⟨1342321500612113690333251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 114544768052233701575104085 1342321500612113690333251)
                ·
                  refine ⟨2013482250918170535499877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342321500612113690333251 2013482250918170535499877)
                  ·
                    refine ⟨377527922047156975406227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013482250918170535499877 377527922047156975406227)
                    ·
                      rfl

theorem cell23_2205699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 4].length) (baseStart_2205699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205699 prefixEnd_2205699 := by exact prefixLift 2205699
  have htrace : WordTrace (prefixWord ++ tailWord_2205699) baseStart_2205699 baseEnd_2205699 := by
    simpa [prefixWord, tailWord_2205699, baseEnd_2205699] using wordTrace_append hprefix tailTrace_2205699
  have hstable : (prefixWord ++ tailWord_2205699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205699).length < 2 ^ (prefixWord ++ tailWord_2205699).sum := by decide
  have hdescent : baseEnd_2205699 < baseStart_2205699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205715 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_2205715 : Nat := 118140960795 + 2205715 * 2 ^ 59
def prefixEnd_2205715 : Nat := 4983230072969 + 3 ^ 40 * 2205715 * 2
def baseEnd_2205715 : Nat := 1132591981831942863618607

theorem tailTrace_2205715 : CollatzResearch.WordTrace tailWord_2205715 prefixEnd_2205715 1132591981831942863618607 := by
  unfold tailWord_2205715
  simp only [CollatzResearch.WordTrace]
  refine ⟨80449035204078735976002599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53632690136052490650668399 80449035204078735976002599)
  ·
    refine ⟨120673552806118103964003899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80449035204078735976002599 120673552806118103964003899)
    ·
      refine ⟨181010329209177155946005849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120673552806118103964003899 181010329209177155946005849)
      ·
        refine ⟨135757746906882866959504387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181010329209177155946005849 135757746906882866959504387)
        ·
          refine ⟨203636620360324300439256581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135757746906882866959504387 203636620360324300439256581)
          ·
            refine ⟨38181866317560806332360609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203636620360324300439256581 38181866317560806332360609)
            ·
              refine ⟨28636399738170604749270457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38181866317560806332360609 28636399738170604749270457)
              ·
                refine ⟨21477299803627953561952843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28636399738170604749270457 21477299803627953561952843)
                ·
                  refine ⟨32215949705441930342929265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21477299803627953561952843 32215949705441930342929265)
                  ·
                    refine ⟨24161962279081447757196949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32215949705441930342929265 24161962279081447757196949)
                    ·
                      refine ⟨1132591981831942863618607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24161962279081447757196949 1132591981831942863618607)
                      ·
                        rfl

theorem cell23_2205715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_2205715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205715 prefixEnd_2205715 := by exact prefixLift 2205715
  have htrace : WordTrace (prefixWord ++ tailWord_2205715) baseStart_2205715 baseEnd_2205715 := by
    simpa [prefixWord, tailWord_2205715, baseEnd_2205715] using wordTrace_append hprefix tailTrace_2205715
  have hstable : (prefixWord ++ tailWord_2205715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205715).length < 2 ^ (prefixWord ++ tailWord_2205715).sum := by decide
  have hdescent : baseEnd_2205715 < baseStart_2205715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205772 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_2205772 : Nat := 118140960795 + 2205772 * 2 ^ 59
def prefixEnd_2205772 : Nat := 4983230072969 + 3 ^ 40 * 2205772 * 2
def baseEnd_2205772 : Nat := 377540416743083046868615

theorem tailTrace_2205772 : CollatzResearch.WordTrace tailWord_2205772 prefixEnd_2205772 377540416743083046868615 := by
  unfold tailWord_2205772
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225557082436117355413785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53634076109914823140551713 40225557082436117355413785)
  ·
    refine ⟨30169167811827088016560339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40225557082436117355413785 30169167811827088016560339)
    ·
      refine ⟨45253751717740632024840509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30169167811827088016560339 45253751717740632024840509)
      ·
        refine ⟨16970156894152737009315191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45253751717740632024840509 16970156894152737009315191)
        ·
          refine ⟨25455235341229105513972787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16970156894152737009315191 25455235341229105513972787)
          ·
            refine ⟨38182853011843658270959181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25455235341229105513972787 38182853011843658270959181)
            ·
              refine ⟨14318569879441371851609693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38182853011843658270959181 14318569879441371851609693)
              ·
                refine ⟨5369463704790514444353635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14318569879441371851609693 5369463704790514444353635)
                ·
                  refine ⟨8054195557185771666530453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5369463704790514444353635 8054195557185771666530453)
                  ·
                    refine ⟨377540416743083046868615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8054195557185771666530453 377540416743083046868615)
                    ·
                      rfl

theorem cell23_2205772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_2205772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205772 prefixEnd_2205772 := by exact prefixLift 2205772
  have htrace : WordTrace (prefixWord ++ tailWord_2205772) baseStart_2205772 baseEnd_2205772 := by
    simpa [prefixWord, tailWord_2205772, baseEnd_2205772] using wordTrace_append hprefix tailTrace_2205772
  have hstable : (prefixWord ++ tailWord_2205772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205772).length < 2 ^ (prefixWord ++ tailWord_2205772).sum := by decide
  have hdescent : baseEnd_2205772 < baseStart_2205772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205796 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_2205796 : Nat := 118140960795 + 2205796 * 2 ^ 59
def prefixEnd_2205796 : Nat := 4983230072969 + 3 ^ 40 * 2205796 * 2
def baseEnd_2205796 : Nat := 1132633573764957046705735

theorem tailTrace_2205796 : CollatzResearch.WordTrace tailWord_2205796 prefixEnd_2205796 1132633573764957046705735 := by
  unfold tailWord_2205796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225994758392643404850621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53634659677856857873134161 40225994758392643404850621)
  ·
    refine ⟨15084748034397241276818983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40225994758392643404850621 15084748034397241276818983)
    ·
      refine ⟨22627122051595861915228475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15084748034397241276818983 22627122051595861915228475)
      ·
        refine ⟨33940683077393792872842713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22627122051595861915228475 33940683077393792872842713)
        ·
          refine ⟨25455512308045344654632035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33940683077393792872842713 25455512308045344654632035)
          ·
            refine ⟨38183268462068016981948053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25455512308045344654632035 38183268462068016981948053)
            ·
              refine ⟨1789840709159438296028815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38183268462068016981948053 1789840709159438296028815)
              ·
                refine ⟨2684761063739157444043223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789840709159438296028815 2684761063739157444043223)
                ·
                  refine ⟨4027141595608736166064835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684761063739157444043223 4027141595608736166064835)
                  ·
                    refine ⟨6040712393413104249097253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4027141595608736166064835 6040712393413104249097253)
                    ·
                      refine ⟨1132633573764957046705735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6040712393413104249097253 1132633573764957046705735)
                      ·
                        rfl

theorem cell23_2205796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_2205796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205796 prefixEnd_2205796 := by exact prefixLift 2205796
  have htrace : WordTrace (prefixWord ++ tailWord_2205796) baseStart_2205796 baseEnd_2205796 := by
    simpa [prefixWord, tailWord_2205796, baseEnd_2205796] using wordTrace_append hprefix tailTrace_2205796
  have hstable : (prefixWord ++ tailWord_2205796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205796).length < 2 ^ (prefixWord ++ tailWord_2205796).sum := by decide
  have hdescent : baseEnd_2205796 < baseStart_2205796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205847 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 1, 2, 2]
def baseStart_2205847 : Nat := 118140960795 + 2205847 * 2 ^ 59
def prefixEnd_2205847 : Nat := 4983230072969 + 3 ^ 40 * 2205847 * 2
def baseEnd_2205847 : Nat := 1132659761278336347168001

theorem tailTrace_2205847 : CollatzResearch.WordTrace tailWord_2205847 prefixEnd_2205847 1132659761278336347168001 := by
  unfold tailWord_2205847
  simp only [CollatzResearch.WordTrace]
  refine ⟨80453849639600522519807795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53635899759733681679871863 80453849639600522519807795)
  ·
    refine ⟨120680774459400783779711693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80453849639600522519807795 120680774459400783779711693)
    ·
      refine ⟨45255290422275293917391885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120680774459400783779711693 45255290422275293917391885)
      ·
        refine ⟨16970733908353235219021957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45255290422275293917391885 16970733908353235219021957)
        ·
          refine ⟨3182012607816231603566617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16970733908353235219021957 3182012607816231603566617)
          ·
            refine ⟨2386509455862173702674963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3182012607816231603566617 2386509455862173702674963)
            ·
              refine ⟨3579764183793260554012445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386509455862173702674963 3579764183793260554012445)
              ·
                refine ⟨1342411568922472707754667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3579764183793260554012445 1342411568922472707754667)
                ·
                  refine ⟨2013617353383709061632001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342411568922472707754667 2013617353383709061632001)
                  ·
                    refine ⟨1510213015037781796224001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2013617353383709061632001 1510213015037781796224001)
                    ·
                      refine ⟨1132659761278336347168001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510213015037781796224001 1132659761278336347168001)
                      ·
                        rfl

theorem cell23_2205847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_2205847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205847 prefixEnd_2205847 := by exact prefixLift 2205847
  have htrace : WordTrace (prefixWord ++ tailWord_2205847) baseStart_2205847 baseEnd_2205847 := by
    simpa [prefixWord, tailWord_2205847, baseEnd_2205847] using wordTrace_append hprefix tailTrace_2205847
  have hstable : (prefixWord ++ tailWord_2205847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205847).length < 2 ^ (prefixWord ++ tailWord_2205847).sum := by decide
  have hdescent : baseEnd_2205847 < baseStart_2205847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205872 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_2205872 : Nat := 118140960795 + 2205872 * 2 ^ 59
def prefixEnd_2205872 : Nat := 4983230072969 + 3 ^ 40 * 2205872 * 2
def baseEnd_2205872 : Nat := 1132672598294698749355385

theorem tailTrace_2205872 : CollatzResearch.WordTrace tailWord_2205872 prefixEnd_2205872 1132672598294698749355385 := by
  unfold tailWord_2205872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40227380732254975894733935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53636507643006634526311913 40227380732254975894733935)
  ·
    refine ⟨60341071098382463842100903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40227380732254975894733935 60341071098382463842100903)
    ·
      refine ⟨90511606647573695763151355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60341071098382463842100903 90511606647573695763151355)
      ·
        refine ⟨135767409971360543644727033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90511606647573695763151355 135767409971360543644727033)
        ·
          refine ⟨101825557478520407733545275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135767409971360543644727033 101825557478520407733545275)
          ·
            refine ⟨152738336217780611600317913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101825557478520407733545275 152738336217780611600317913)
            ·
              refine ⟨114553752163335458700238435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152738336217780611600317913 114553752163335458700238435)
              ·
                refine ⟨171830628245003188050357653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114553752163335458700238435 171830628245003188050357653)
                ·
                  refine ⟨8054560698984524439860515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171830628245003188050357653 8054560698984524439860515)
                  ·
                    refine ⟨12081841048476786659790773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8054560698984524439860515 12081841048476786659790773)
                    ·
                      refine ⟨1132672598294698749355385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12081841048476786659790773 1132672598294698749355385)
                      ·
                        rfl

theorem cell23_2205872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_2205872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205872 prefixEnd_2205872 := by exact prefixLift 2205872
  have htrace : WordTrace (prefixWord ++ tailWord_2205872) baseStart_2205872 baseEnd_2205872 := by
    simpa [prefixWord, tailWord_2205872, baseEnd_2205872] using wordTrace_append hprefix tailTrace_2205872
  have hstable : (prefixWord ++ tailWord_2205872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205872).length < 2 ^ (prefixWord ++ tailWord_2205872).sum := by decide
  have hdescent : baseEnd_2205872 < baseStart_2205872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205919 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2205919 : Nat := 118140960795 + 2205919 * 2 ^ 59
def prefixEnd_2205919 : Nat := 4983230072969 + 3 ^ 40 * 2205919 * 2
def baseEnd_2205919 : Nat := 1132696731885460065467669

theorem tailTrace_2205919 : CollatzResearch.WordTrace tailWord_2205919 prefixEnd_2205919 1132696731885460065467669 := by
  unfold tailWord_2205919
  simp only [CollatzResearch.WordTrace]
  refine ⟨80456475695339678816428811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53637650463559785877619207 80456475695339678816428811)
  ·
    refine ⟨120684713543009518224643217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80456475695339678816428811 120684713543009518224643217)
    ·
      refine ⟨90513535157257138668482413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120684713543009518224643217 90513535157257138668482413)
      ·
        refine ⟨33942575683971427000680905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90513535157257138668482413 33942575683971427000680905)
        ·
          refine ⟨25456931762978570250510679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33942575683971427000680905 25456931762978570250510679)
          ·
            refine ⟨38185397644467855375766019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25456931762978570250510679 38185397644467855375766019)
            ·
              refine ⟨57278096466701783063649029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38185397644467855375766019 57278096466701783063649029)
              ·
                refine ⟨10739643087506584324434193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57278096466701783063649029 10739643087506584324434193)
                ·
                  refine ⟨8054732315629938243325645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10739643087506584324434193 8054732315629938243325645)
                  ·
                    refine ⟨3020524618361226841247117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8054732315629938243325645 3020524618361226841247117)
                    ·
                      refine ⟨1132696731885460065467669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020524618361226841247117 1132696731885460065467669)
                      ·
                        rfl

theorem cell23_2205919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2205919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205919 prefixEnd_2205919 := by exact prefixLift 2205919
  have htrace : WordTrace (prefixWord ++ tailWord_2205919) baseStart_2205919 baseEnd_2205919 := by
    simpa [prefixWord, tailWord_2205919, baseEnd_2205919] using wordTrace_append hprefix tailTrace_2205919
  have hstable : (prefixWord ++ tailWord_2205919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205919).length < 2 ^ (prefixWord ++ tailWord_2205919).sum := by decide
  have hdescent : baseEnd_2205919 < baseStart_2205919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205956 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_2205956 : Nat := 118140960795 + 2205956 * 2 ^ 59
def prefixEnd_2205956 : Nat := 4983230072969 + 3 ^ 40 * 2205956 * 2
def baseEnd_2205956 : Nat := 377571910223225473568333

theorem tailTrace_2205956 : CollatzResearch.WordTrace tailWord_2205956 prefixEnd_2205956 377571910223225473568333 := by
  unfold tailWord_2205956
  simp only [CollatzResearch.WordTrace]
  refine ⟨40228912598102817067762861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53638550130803756090350481 40228912598102817067762861)
  ·
    refine ⟨15085842224288556400411073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40228912598102817067762861 15085842224288556400411073)
    ·
      refine ⟨11314381668216417300308305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15085842224288556400411073 11314381668216417300308305)
      ·
        refine ⟨8485786251162312975231229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11314381668216417300308305 8485786251162312975231229)
        ·
          refine ⟨3182169844185867365711711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8485786251162312975231229 3182169844185867365711711)
          ·
            refine ⟨4773254766278801048567567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182169844185867365711711 4773254766278801048567567)
            ·
              refine ⟨7159882149418201572851351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773254766278801048567567 7159882149418201572851351)
              ·
                refine ⟨10739823224127302359277027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7159882149418201572851351 10739823224127302359277027)
                ·
                  refine ⟨16109734836190953538915541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10739823224127302359277027 16109734836190953538915541)
                  ·
                    refine ⟨377571910223225473568333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16109734836190953538915541 377571910223225473568333)
                    ·
                      rfl

theorem cell23_2205956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_2205956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205956 prefixEnd_2205956 := by exact prefixLift 2205956
  have htrace : WordTrace (prefixWord ++ tailWord_2205956) baseStart_2205956 baseEnd_2205956 := by
    simpa [prefixWord, tailWord_2205956, baseEnd_2205956] using wordTrace_append hprefix tailTrace_2205956
  have hstable : (prefixWord ++ tailWord_2205956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205956).length < 2 ^ (prefixWord ++ tailWord_2205956).sum := by decide
  have hdescent : baseEnd_2205956 < baseStart_2205956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205976 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2205976 : Nat := 118140960795 + 2205976 * 2 ^ 59
def prefixEnd_2205976 : Nat := 4983230072969 + 3 ^ 40 * 2205976 * 2
def baseEnd_2205976 : Nat := 1132726000282766342454907

theorem tailTrace_2205976 : CollatzResearch.WordTrace tailWord_2205976 prefixEnd_2205976 1132726000282766342454907 := by
  unfold tailWord_2205976
  simp only [CollatzResearch.WordTrace]
  refine ⟨40229277328066588775626891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53639036437422118367502521 40229277328066588775626891)
  ·
    refine ⟨60343915992099883163440337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40229277328066588775626891 60343915992099883163440337)
    ·
      refine ⟨45257936994074912372580253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60343915992099883163440337 45257936994074912372580253)
      ·
        refine ⟨16971726372778092139717595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45257936994074912372580253 16971726372778092139717595)
        ·
          refine ⟨25457589559167138209576393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16971726372778092139717595 25457589559167138209576393)
          ·
            refine ⟨19093192169375353657182295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25457589559167138209576393 19093192169375353657182295)
            ·
              refine ⟨28639788254063030485773443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19093192169375353657182295 28639788254063030485773443)
              ·
                refine ⟨42959682381094545728660165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28639788254063030485773443 42959682381094545728660165)
                ·
                  refine ⟨8054940446455227324123781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42959682381094545728660165 8054940446455227324123781)
                  ·
                    refine ⟨1510301333710355123273209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8054940446455227324123781 1510301333710355123273209)
                    ·
                      refine ⟨1132726000282766342454907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510301333710355123273209 1132726000282766342454907)
                      ·
                        rfl

theorem cell23_2205976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2205976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205976 prefixEnd_2205976 := by exact prefixLift 2205976
  have htrace : WordTrace (prefixWord ++ tailWord_2205976) baseStart_2205976 baseEnd_2205976 := by
    simpa [prefixWord, tailWord_2205976, baseEnd_2205976] using wordTrace_append hprefix tailTrace_2205976
  have hstable : (prefixWord ++ tailWord_2205976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205976).length < 2 ^ (prefixWord ++ tailWord_2205976).sum := by decide
  have hdescent : baseEnd_2205976 < baseStart_2205976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205999 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 6]
def baseStart_2205999 : Nat := 118140960795 + 2205999 * 2 ^ 59
def prefixEnd_2205999 : Nat := 4983230072969 + 3 ^ 40 * 2205999 * 2
def baseEnd_2205999 : Nat := 125859756704202194718589

theorem tailTrace_2205999 : CollatzResearch.WordTrace tailWord_2205999 prefixEnd_2205999 125859756704202194718589 := by
  unfold tailWord_2205999
  simp only [CollatzResearch.WordTrace]
  refine ⟨80459393535049852479341051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53639595690033234986227367 80459393535049852479341051)
  ·
    refine ⟨120689090302574778719011577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80459393535049852479341051 120689090302574778719011577)
    ·
      refine ⟨90516817726931084039258683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120689090302574778719011577 90516817726931084039258683)
      ·
        refine ⟨135775226590396626058888025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90516817726931084039258683 135775226590396626058888025)
        ·
          refine ⟨101831419942797469544166019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135775226590396626058888025 101831419942797469544166019)
          ·
            refine ⟨152747129914196204316249029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101831419942797469544166019 152747129914196204316249029)
            ·
              refine ⟨28640086858911788309296693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152747129914196204316249029 28640086858911788309296693)
              ·
                refine ⟨2685008143022980153996565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28640086858911788309296693 2685008143022980153996565)
                ·
                  refine ⟨125859756704202194718589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2685008143022980153996565 125859756704202194718589)
                  ·
                    rfl

theorem cell23_2205999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 6].length) (baseStart_2205999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205999 prefixEnd_2205999 := by exact prefixLift 2205999
  have htrace : WordTrace (prefixWord ++ tailWord_2205999) baseStart_2205999 baseEnd_2205999 := by
    simpa [prefixWord, tailWord_2205999, baseEnd_2205999] using wordTrace_append hprefix tailTrace_2205999
  have hstable : (prefixWord ++ tailWord_2205999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205999).length < 2 ^ (prefixWord ++ tailWord_2205999).sum := by decide
  have hdescent : baseEnd_2205999 < baseStart_2205999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206037 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_2206037 : Nat := 118140960795 + 2206037 * 2 ^ 59
def prefixEnd_2206037 : Nat := 4983230072969 + 3 ^ 40 * 2206037 * 2
def baseEnd_2206037 : Nat := 377585774200896867930709

theorem tailTrace_2206037 : CollatzResearch.WordTrace tailWord_2206037 prefixEnd_2206037 377585774200896867930709 := by
  unfold tailWord_2206037
  simp only [CollatzResearch.WordTrace]
  refine ⟨80460779508912184969224365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53640519672608123312816243 80460779508912184969224365)
  ·
    refine ⟨30172792315842069363459137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80460779508912184969224365 30172792315842069363459137)
    ·
      refine ⟨22629594236881552022594353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30172792315842069363459137 22629594236881552022594353)
      ·
        refine ⟨16972195677661164016945765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22629594236881552022594353 16972195677661164016945765)
        ·
          refine ⟨3182286689561468253177331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16972195677661164016945765 3182286689561468253177331)
          ·
            refine ⟨4773430034342202379765997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182286689561468253177331 4773430034342202379765997)
            ·
              refine ⟨1790036262878325892412249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4773430034342202379765997 1790036262878325892412249)
              ·
                refine ⟨1342527197158744419309187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790036262878325892412249 1342527197158744419309187)
                ·
                  refine ⟨2013790795738116628963781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342527197158744419309187 2013790795738116628963781)
                  ·
                    refine ⟨377585774200896867930709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013790795738116628963781 377585774200896867930709)
                    ·
                      rfl

theorem cell23_2206037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_2206037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206037 prefixEnd_2206037 := by exact prefixLift 2206037
  have htrace : WordTrace (prefixWord ++ tailWord_2206037) baseStart_2206037 baseEnd_2206037 := by
    simpa [prefixWord, tailWord_2206037, baseEnd_2206037] using wordTrace_append hprefix tailTrace_2206037
  have hstable : (prefixWord ++ tailWord_2206037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206037).length < 2 ^ (prefixWord ++ tailWord_2206037).sum := by decide
  have hdescent : baseEnd_2206037 < baseStart_2206037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206049 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_2206049 : Nat := 118140960795 + 2206049 * 2 ^ 59
def prefixEnd_2206049 : Nat := 4983230072969 + 3 ^ 40 * 2206049 * 2
def baseEnd_2206049 : Nat := 1132763484370544556842071

theorem tailTrace_2206049 : CollatzResearch.WordTrace tailWord_2206049 prefixEnd_2206049 1132763484370544556842071 := by
  unfold tailWord_2206049
  simp only [CollatzResearch.WordTrace]
  refine ⟨80461217184868711018661201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53640811456579140679107467 80461217184868711018661201)
  ·
    refine ⟨60345912888651533263995901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80461217184868711018661201 60345912888651533263995901)
    ·
      refine ⟨22629717333244324973998463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60345912888651533263995901 22629717333244324973998463)
      ·
        refine ⟨33944575999866487460997695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22629717333244324973998463 33944575999866487460997695)
        ·
          refine ⟨50916863999799731191496543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33944575999866487460997695 50916863999799731191496543)
          ·
            refine ⟨76375295999699596787244815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50916863999799731191496543 76375295999699596787244815)
            ·
              refine ⟨114562943999549395180867223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76375295999699596787244815 114562943999549395180867223)
              ·
                refine ⟨171844415999324092771300835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114562943999549395180867223 171844415999324092771300835)
                ·
                  refine ⟨257766623998986139156951253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171844415999324092771300835 257766623998986139156951253)
                  ·
                    refine ⟨6041405249976237636491045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 257766623998986139156951253 6041405249976237636491045)
                    ·
                      refine ⟨1132763484370544556842071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6041405249976237636491045 1132763484370544556842071)
                      ·
                        rfl

theorem cell23_2206049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_2206049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206049 prefixEnd_2206049 := by exact prefixLift 2206049
  have htrace : WordTrace (prefixWord ++ tailWord_2206049) baseStart_2206049 baseEnd_2206049 := by
    simpa [prefixWord, tailWord_2206049, baseEnd_2206049] using wordTrace_append hprefix tailTrace_2206049
  have hstable : (prefixWord ++ tailWord_2206049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206049).length < 2 ^ (prefixWord ++ tailWord_2206049).sum := by decide
  have hdescent : baseEnd_2206049 < baseStart_2206049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206050 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2206050 : Nat := 118140960795 + 2206050 * 2 ^ 59
def prefixEnd_2206050 : Nat := 4983230072969 + 3 ^ 40 * 2206050 * 2
def baseEnd_2206050 : Nat := 125862666427911005881063

theorem tailTrace_2206050 : CollatzResearch.WordTrace tailWord_2206050 prefixEnd_2206050 125862666427911005881063 := by
  unfold tailWord_2206050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115313414466272047361901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53640835771910058792965069 20115313414466272047361901)
  ·
    refine ⟨7543242530424852017760713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20115313414466272047361901 7543242530424852017760713)
    ·
      refine ⟨5657431897818639013320535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7543242530424852017760713 5657431897818639013320535)
      ·
        refine ⟨8486147846727958519980803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657431897818639013320535 8486147846727958519980803)
        ·
          refine ⟨12729221770091937779971205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486147846727958519980803 12729221770091937779971205)
          ·
            refine ⟨2386729081892238333744601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12729221770091937779971205 2386729081892238333744601)
            ·
              refine ⟨1790046811419178750308451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386729081892238333744601 1790046811419178750308451)
              ·
                refine ⟨2685070217128768125462677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790046811419178750308451 2685070217128768125462677)
                ·
                  refine ⟨125862666427911005881063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2685070217128768125462677 125862666427911005881063)
                  ·
                    rfl

theorem cell23_2206050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2206050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206050 prefixEnd_2206050 := by exact prefixLift 2206050
  have htrace : WordTrace (prefixWord ++ tailWord_2206050) baseStart_2206050 baseEnd_2206050 := by
    simpa [prefixWord, tailWord_2206050, baseEnd_2206050] using wordTrace_append hprefix tailTrace_2206050
  have hstable : (prefixWord ++ tailWord_2206050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206050).length < 2 ^ (prefixWord ++ tailWord_2206050).sum := by decide
  have hdescent : baseEnd_2206050 < baseStart_2206050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206076 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_2206076 : Nat := 118140960795 + 2206076 * 2 ^ 59
def prefixEnd_2206076 : Nat := 4983230072969 + 3 ^ 40 * 2206076 * 2
def baseEnd_2206076 : Nat := 377592449449405317068149

theorem tailTrace_2206076 : CollatzResearch.WordTrace tailWord_2206076 prefixEnd_2206076 377592449449405317068149 := by
  unfold tailWord_2206076
  simp only [CollatzResearch.WordTrace]
  refine ⟨40231100977885447314947041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53641467970513929753262721 40231100977885447314947041)
  ·
    refine ⟨30173325733414085486210281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40231100977885447314947041 30173325733414085486210281)
    ·
      refine ⟨22629994300060564114657711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30173325733414085486210281 22629994300060564114657711)
      ·
        refine ⟨33944991450090846171986567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22629994300060564114657711 33944991450090846171986567)
        ·
          refine ⟨50917487175136269257979851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33944991450090846171986567 50917487175136269257979851)
          ·
            refine ⟨76376230762704403886969777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50917487175136269257979851 76376230762704403886969777)
            ·
              refine ⟨57282173072028302915227333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76376230762704403886969777 57282173072028302915227333)
              ·
                refine ⟨10740407451005306796605125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57282173072028302915227333 10740407451005306796605125)
                ·
                  refine ⟨2013826397063495024363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10740407451005306796605125 2013826397063495024363461)
                  ·
                    refine ⟨377592449449405317068149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013826397063495024363461 377592449449405317068149)
                    ·
                      rfl

theorem cell23_2206076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_2206076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206076 prefixEnd_2206076 := by exact prefixLift 2206076
  have htrace : WordTrace (prefixWord ++ tailWord_2206076) baseStart_2206076 baseEnd_2206076 := by
    simpa [prefixWord, tailWord_2206076, baseEnd_2206076] using wordTrace_append hprefix tailTrace_2206076
  have hstable : (prefixWord ++ tailWord_2206076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206076).length < 2 ^ (prefixWord ++ tailWord_2206076).sum := by decide
  have hdescent : baseEnd_2206076 < baseStart_2206076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206089 : List Nat := [1, 2, 1, 1, 6, 12]
def baseStart_2206089 : Nat := 118140960795 + 2206089 * 2 ^ 59
def prefixEnd_2206089 : Nat := 4983230072969 + 3 ^ 40 * 2206089 * 2
def baseEnd_2206089 : Nat := 4661662648546190947909

theorem tailTrace_2206089 : CollatzResearch.WordTrace tailWord_2206089 prefixEnd_2206089 4661662648546190947909 := by
  unfold tailWord_2206089
  simp only [CollatzResearch.WordTrace]
  refine ⟨80462676104723797850117321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53641784069815865233411547 80462676104723797850117321)
  ·
    refine ⟨60347007078542848387587991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80462676104723797850117321 60347007078542848387587991)
    ·
      refine ⟨90520510617814272581381987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60347007078542848387587991 90520510617814272581381987)
      ·
        refine ⟨135780765926721408872072981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90520510617814272581381987 135780765926721408872072981)
        ·
          refine ⟨6364723402815066040878421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135780765926721408872072981 6364723402815066040878421)
          ·
            refine ⟨4661662648546190947909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6364723402815066040878421 4661662648546190947909)
            ·
              rfl

theorem cell23_2206089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 12].length) (baseStart_2206089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206089 prefixEnd_2206089 := by exact prefixLift 2206089
  have htrace : WordTrace (prefixWord ++ tailWord_2206089) baseStart_2206089 baseEnd_2206089 := by
    simpa [prefixWord, tailWord_2206089, baseEnd_2206089] using wordTrace_append hprefix tailTrace_2206089
  have hstable : (prefixWord ++ tailWord_2206089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206089).length < 2 ^ (prefixWord ++ tailWord_2206089).sum := by decide
  have hdescent : baseEnd_2206089 < baseStart_2206089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206094 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2206094 : Nat := 118140960795 + 2206094 * 2 ^ 59
def prefixEnd_2206094 : Nat := 4983230072969 + 3 ^ 40 * 2206094 * 2
def baseEnd_2206094 : Nat := 1132786590999996880779365

theorem tailTrace_2206094 : CollatzResearch.WordTrace tailWord_2206094 prefixEnd_2206094 1132786590999996880779365 := by
  unfold tailWord_2206094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057857308713210463006167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53641905646470455802699557 10057857308713210463006167)
  ·
    refine ⟨15086785963069815694509251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10057857308713210463006167 15086785963069815694509251)
    ·
      refine ⟨22630178944604723541763877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15086785963069815694509251 22630178944604723541763877)
      ·
        refine ⟨4243158552113385664080727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22630178944604723541763877 4243158552113385664080727)
        ·
          refine ⟨6364737828170078496121091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243158552113385664080727 6364737828170078496121091)
          ·
            refine ⟨9547106742255117744181637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6364737828170078496121091 9547106742255117744181637)
            ·
              refine ⟨1790082514172834577034057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9547106742255117744181637 1790082514172834577034057)
              ·
                refine ⟨1342561885629625932775543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790082514172834577034057 1342561885629625932775543)
                ·
                  refine ⟨2013842828444438899163315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342561885629625932775543 2013842828444438899163315)
                  ·
                    refine ⟨3020764242666658348744973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2013842828444438899163315 3020764242666658348744973)
                    ·
                      refine ⟨1132786590999996880779365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020764242666658348744973 1132786590999996880779365)
                      ·
                        rfl

theorem cell23_2206094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2206094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206094 prefixEnd_2206094 := by exact prefixLift 2206094
  have htrace : WordTrace (prefixWord ++ tailWord_2206094) baseStart_2206094 baseEnd_2206094 := by
    simpa [prefixWord, tailWord_2206094, baseEnd_2206094] using wordTrace_append hprefix tailTrace_2206094
  have hstable : (prefixWord ++ tailWord_2206094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206094).length < 2 ^ (prefixWord ++ tailWord_2206094).sum := by decide
  have hdescent : baseEnd_2206094 < baseStart_2206094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206106 : List Nat := [3, 1, 1, 4, 1, 2, 3, 8]
def baseStart_2206106 : Nat := 118140960795 + 2206106 * 2 ^ 59
def prefixEnd_2206106 : Nat := 4983230072969 + 3 ^ 40 * 2206106 * 2
def baseEnd_2206106 : Nat := 41955287139550030882567

theorem tailTrace_2206106 : CollatzResearch.WordTrace tailWord_2206106 prefixEnd_2206106 41955287139550030882567 := by
  unfold tailWord_2206106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115824036415552438371543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53642197430441473168990781 20115824036415552438371543)
  ·
    refine ⟨30173736054623328657557315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20115824036415552438371543 30173736054623328657557315)
    ·
      refine ⟨45260604081934992986335973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30173736054623328657557315 45260604081934992986335973)
      ·
        refine ⟨8486363265362811184937995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45260604081934992986335973 8486363265362811184937995)
        ·
          refine ⟨12729544898044216777406993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486363265362811184937995 12729544898044216777406993)
          ·
            refine ⟨9547158673533162583055245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12729544898044216777406993 9547158673533162583055245)
            ·
              refine ⟨3580184502574935968645717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9547158673533162583055245 3580184502574935968645717)
              ·
                refine ⟨41955287139550030882567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3580184502574935968645717 41955287139550030882567)
                ·
                  rfl

theorem cell23_2206106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_2206106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206106 prefixEnd_2206106 := by exact prefixLift 2206106
  have htrace : WordTrace (prefixWord ++ tailWord_2206106) baseStart_2206106 baseEnd_2206106 := by
    simpa [prefixWord, tailWord_2206106, baseEnd_2206106] using wordTrace_append hprefix tailTrace_2206106
  have hstable : (prefixWord ++ tailWord_2206106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206106).length < 2 ^ (prefixWord ++ tailWord_2206106).sum := by decide
  have hdescent : baseEnd_2206106 < baseStart_2206106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206110 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2206110 : Nat := 118140960795 + 2206110 * 2 ^ 59
def prefixEnd_2206110 : Nat := 4983230072969 + 3 ^ 40 * 2206110 * 2
def baseEnd_2206110 : Nat := 377598268896822939393097

theorem tailTrace_2206110 : CollatzResearch.WordTrace tailWord_2206110 prefixEnd_2206110 377598268896822939393097 := by
  unfold tailWord_2206110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057930254705964804578973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53642294691765145624421189 10057930254705964804578973)
  ·
    refine ⟨3771723845514736801717115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10057930254705964804578973 3771723845514736801717115)
    ·
      refine ⟨5657585768272105202575673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771723845514736801717115 5657585768272105202575673)
      ·
        refine ⟨4243189326204078901931755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5657585768272105202575673 4243189326204078901931755)
        ·
          refine ⟨6364783989306118352897633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243189326204078901931755 6364783989306118352897633)
          ·
            refine ⟨4773587991979588764673225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364783989306118352897633 4773587991979588764673225)
            ·
              refine ⟨3580190993984691573504919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4773587991979588764673225 3580190993984691573504919)
              ·
                refine ⟨5370286490977037360257379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580190993984691573504919 5370286490977037360257379)
                ·
                  refine ⟨8055429736465556040386069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5370286490977037360257379 8055429736465556040386069)
                  ·
                    refine ⟨377598268896822939393097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8055429736465556040386069 377598268896822939393097)
                    ·
                      rfl

theorem cell23_2206110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2206110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206110 prefixEnd_2206110 := by exact prefixLift 2206110
  have htrace : WordTrace (prefixWord ++ tailWord_2206110) baseStart_2206110 baseEnd_2206110 := by
    simpa [prefixWord, tailWord_2206110, baseEnd_2206110] using wordTrace_append hprefix tailTrace_2206110
  have hstable : (prefixWord ++ tailWord_2206110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206110).length < 2 ^ (prefixWord ++ tailWord_2206110).sum := by decide
  have hdescent : baseEnd_2206110 < baseStart_2206110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206120 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2206120 : Nat := 118140960795 + 2206120 * 2 ^ 59
def prefixEnd_2206120 : Nat := 4983230072969 + 3 ^ 40 * 2206120 * 2
def baseEnd_2206120 : Nat := 1132799941497013779054245

theorem tailTrace_2206120 : CollatzResearch.WordTrace tailWord_2206120 prefixEnd_2206120 1132799941497013779054245 := by
  unfold tailWord_2206120
  simp only [CollatzResearch.WordTrace]
  refine ⟨40231903383805745072247907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53642537845074326762997209 40231903383805745072247907)
  ·
    refine ⟨60347855075708617608371861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40231903383805745072247907 60347855075708617608371861)
    ·
      refine ⟨2828805706673841450392431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60347855075708617608371861 2828805706673841450392431)
      ·
        refine ⟨4243208560010762175588647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828805706673841450392431 4243208560010762175588647)
        ·
          refine ⟨6364812840016143263382971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243208560010762175588647 6364812840016143263382971)
          ·
            refine ⟨9547219260024214895074457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6364812840016143263382971 9547219260024214895074457)
            ·
              refine ⟨7160414445018161171305843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9547219260024214895074457 7160414445018161171305843)
              ·
                refine ⟨10740621667527241756958765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7160414445018161171305843 10740621667527241756958765)
                ·
                  refine ⟨4027733125322715658859537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10740621667527241756958765 4027733125322715658859537)
                  ·
                    refine ⟨3020799843992036744144653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4027733125322715658859537 3020799843992036744144653)
                    ·
                      refine ⟨1132799941497013779054245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020799843992036744144653 1132799941497013779054245)
                      ·
                        rfl

theorem cell23_2206120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2206120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206120 prefixEnd_2206120 := by exact prefixLift 2206120
  have htrace : WordTrace (prefixWord ++ tailWord_2206120) baseStart_2206120 baseEnd_2206120 := by
    simpa [prefixWord, tailWord_2206120, baseEnd_2206120] using wordTrace_append hprefix tailTrace_2206120
  have hstable : (prefixWord ++ tailWord_2206120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206120).length < 2 ^ (prefixWord ++ tailWord_2206120).sum := by decide
  have hdescent : baseEnd_2206120 < baseStart_2206120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206137 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2206137 : Nat := 118140960795 + 2206137 * 2 ^ 59
def prefixEnd_2206137 : Nat := 4983230072969 + 3 ^ 40 * 2206137 * 2
def baseEnd_2206137 : Nat := 1132808670668140212541667

theorem tailTrace_2206137 : CollatzResearch.WordTrace tailWord_2206137 prefixEnd_2206137 1132808670668140212541667 := by
  unfold tailWord_2206137
  simp only [CollatzResearch.WordTrace]
  refine ⟨80464426808549902047864665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53642951205699934698576443 80464426808549902047864665)
  ·
    refine ⟨60348320106412426535898499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80464426808549902047864665 60348320106412426535898499)
    ·
      refine ⟨90522480159618639803847749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60348320106412426535898499 90522480159618639803847749)
      ·
        refine ⟨16972965029928494963221453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90522480159618639803847749 16972965029928494963221453)
        ·
          refine ⟨6364861886223185611208045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16972965029928494963221453 6364861886223185611208045)
          ·
            refine ⟨2386823207333694604203017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6364861886223185611208045 2386823207333694604203017)
            ·
              refine ⟨1790117405500270953152263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386823207333694604203017 1790117405500270953152263)
              ·
                refine ⟨2685176108250406429728395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790117405500270953152263 2685176108250406429728395)
                ·
                  refine ⟨4027764162375609644592593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685176108250406429728395 4027764162375609644592593)
                  ·
                    refine ⟨3020823121781707233444445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4027764162375609644592593 3020823121781707233444445)
                    ·
                      refine ⟨1132808670668140212541667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3020823121781707233444445 1132808670668140212541667)
                      ·
                        rfl

theorem cell23_2206137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2206137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206137 prefixEnd_2206137 := by exact prefixLift 2206137
  have htrace : WordTrace (prefixWord ++ tailWord_2206137) baseStart_2206137 baseEnd_2206137 := by
    simpa [prefixWord, tailWord_2206137, baseEnd_2206137] using wordTrace_append hprefix tailTrace_2206137
  have hstable : (prefixWord ++ tailWord_2206137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206137).length < 2 ^ (prefixWord ++ tailWord_2206137).sum := by decide
  have hdescent : baseEnd_2206137 < baseStart_2206137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206139 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_2206139 : Nat := 118140960795 + 2206139 * 2 ^ 59
def prefixEnd_2206139 : Nat := 4983230072969 + 3 ^ 40 * 2206139 * 2
def baseEnd_2206139 : Nat := 1132809697629449204716657

theorem tailTrace_2206139 : CollatzResearch.WordTrace tailWord_2206139 prefixEnd_2206139 1132809697629449204716657 := by
  unfold tailWord_2206139
  simp only [CollatzResearch.WordTrace]
  refine ⟨80464499754542656389437471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53642999836361770926291647 80464499754542656389437471)
  ·
    refine ⟨120696749631813984584156207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80464499754542656389437471 120696749631813984584156207)
    ·
      refine ⟨181045124447720976876234311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120696749631813984584156207 181045124447720976876234311)
      ·
        refine ⟨271567686671581465314351467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181045124447720976876234311 271567686671581465314351467)
        ·
          refine ⟨407351530007372197971527201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271567686671581465314351467 407351530007372197971527201)
          ·
            refine ⟨305513647505529148478645401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407351530007372197971527201 305513647505529148478645401)
            ·
              refine ⟨229135235629146861358984051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305513647505529148478645401 229135235629146861358984051)
              ·
                refine ⟨343702853443720292038476077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229135235629146861358984051 343702853443720292038476077)
                ·
                  refine ⟨128888570041395109514428529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343702853443720292038476077 128888570041395109514428529)
                  ·
                    refine ⟨96666427531046332135821397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128888570041395109514428529 96666427531046332135821397)
                    ·
                      refine ⟨1132809697629449204716657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 96666427531046332135821397 1132809697629449204716657)
                      ·
                        rfl

theorem cell23_2206139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_2206139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206139 prefixEnd_2206139 := by exact prefixLift 2206139
  have htrace : WordTrace (prefixWord ++ tailWord_2206139) baseStart_2206139 baseEnd_2206139 := by
    simpa [prefixWord, tailWord_2206139, baseEnd_2206139] using wordTrace_append hprefix tailTrace_2206139
  have hstable : (prefixWord ++ tailWord_2206139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206139).length < 2 ^ (prefixWord ++ tailWord_2206139).sum := by decide
  have hdescent : baseEnd_2206139 < baseStart_2206139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206176 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2206176 : Nat := 118140960795 + 2206176 * 2 ^ 59
def prefixEnd_2206176 : Nat := 4983230072969 + 3 ^ 40 * 2206176 * 2
def baseEnd_2206176 : Nat := 1132828696413665559953987

theorem tailTrace_2206176 : CollatzResearch.WordTrace tailWord_2206176 prefixEnd_2206176 1132828696413665559953987 := by
  unfold tailWord_2206176
  simp only [CollatzResearch.WordTrace]
  refine ⟨40232924627704305854267191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53643899503605741139022921 40232924627704305854267191)
  ·
    refine ⟨60349386941556458781400787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40232924627704305854267191 60349386941556458781400787)
    ·
      refine ⟨90524080412334688172101181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60349386941556458781400787 90524080412334688172101181)
      ·
        refine ⟨33946530154625508064537943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90524080412334688172101181 33946530154625508064537943)
        ·
          refine ⟨50919795231938262096806915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33946530154625508064537943 50919795231938262096806915)
          ·
            refine ⟨76379692847907393145210373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50919795231938262096806915 76379692847907393145210373)
            ·
              refine ⟨14321192408982636214726945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76379692847907393145210373 14321192408982636214726945)
              ·
                refine ⟨10740894306736977161045209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14321192408982636214726945 10740894306736977161045209)
                ·
                  refine ⟨8055670730052732870783907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10740894306736977161045209 8055670730052732870783907)
                  ·
                    refine ⟨12083506095079099306175861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8055670730052732870783907 12083506095079099306175861)
                    ·
                      refine ⟨1132828696413665559953987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12083506095079099306175861 1132828696413665559953987)
                      ·
                        rfl

theorem cell23_2206176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2206176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206176 prefixEnd_2206176 := by exact prefixLift 2206176
  have htrace : WordTrace (prefixWord ++ tailWord_2206176) baseStart_2206176 baseEnd_2206176 := by
    simpa [prefixWord, tailWord_2206176, baseEnd_2206176] using wordTrace_append hprefix tailTrace_2206176
  have hstable : (prefixWord ++ tailWord_2206176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206176).length < 2 ^ (prefixWord ++ tailWord_2206176).sum := by decide
  have hdescent : baseEnd_2206176 < baseStart_2206176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206213 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 5]
def baseStart_2206213 : Nat := 118140960795 + 2206213 * 2 ^ 59
def prefixEnd_2206213 : Nat := 4983230072969 + 3 ^ 40 * 2206213 * 2
def baseEnd_2206213 : Nat := 125871966133097990576813

theorem tailTrace_2206213 : CollatzResearch.WordTrace tailWord_2206213 prefixEnd_2206213 125871966133097990576813 := by
  unfold tailWord_2206213
  simp only [CollatzResearch.WordTrace]
  refine ⟨80467198756274567027631293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53644799170849711351754195 80467198756274567027631293)
  ·
    refine ⟨30175199533602962635361735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80467198756274567027631293 30175199533602962635361735)
    ·
      refine ⟨45262799300404443953042603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30175199533602962635361735 45262799300404443953042603)
      ·
        refine ⟨67894198950606665929563905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45262799300404443953042603 67894198950606665929563905)
        ·
          refine ⟨50920649212954999447172929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67894198950606665929563905 50920649212954999447172929)
          ·
            refine ⟨38190486909716249585379697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50920649212954999447172929 38190486909716249585379697)
            ·
              refine ⟨28642865182287187189034773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38190486909716249585379697 28642865182287187189034773)
              ·
                refine ⟨1342634305419711899486005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28642865182287187189034773 1342634305419711899486005)
                ·
                  refine ⟨125871966133097990576813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1342634305419711899486005 125871966133097990576813)
                  ·
                    rfl

theorem cell23_2206213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_2206213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206213 prefixEnd_2206213 := by exact prefixLift 2206213
  have htrace : WordTrace (prefixWord ++ tailWord_2206213) baseStart_2206213 baseEnd_2206213 := by
    simpa [prefixWord, tailWord_2206213, baseEnd_2206213] using wordTrace_append hprefix tailTrace_2206213
  have hstable : (prefixWord ++ tailWord_2206213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206213).length < 2 ^ (prefixWord ++ tailWord_2206213).sum := by decide
  have hdescent : baseEnd_2206213 < baseStart_2206213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206233 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 5, 2]
def baseStart_2206233 : Nat := 118140960795 + 2206233 * 2 ^ 59
def prefixEnd_2206233 : Nat := 4983230072969 + 3 ^ 40 * 2206233 * 2
def baseEnd_2206233 : Nat := 1132857964810971836941225

theorem tailTrace_2206233 : CollatzResearch.WordTrace tailWord_2206233 prefixEnd_2206233 1132857964810971836941225 := by
  unfold tailWord_2206233
  simp only [CollatzResearch.WordTrace]
  refine ⟨80467928216202110443359353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53645285477468073628906235 80467928216202110443359353)
  ·
    refine ⟨60350946162151582832519515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80467928216202110443359353 60350946162151582832519515)
    ·
      refine ⟨90526419243227374248779273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60350946162151582832519515 90526419243227374248779273)
      ·
        refine ⟨67894814432420530686584455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90526419243227374248779273 67894814432420530686584455)
        ·
          refine ⟨101842221648630796029876683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67894814432420530686584455 101842221648630796029876683)
          ·
            refine ⟨152763332472946194044815025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101842221648630796029876683 152763332472946194044815025)
            ·
              refine ⟨114572499354709645533611269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152763332472946194044815025 114572499354709645533611269)
              ·
                refine ⟨21482343629008058537552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114572499354709645533611269 21482343629008058537552113)
                ·
                  refine ⟨16111757721756043903164085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21482343629008058537552113 16111757721756043903164085)
                  ·
                    refine ⟨1510477286414629115921633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16111757721756043903164085 1510477286414629115921633)
                    ·
                      refine ⟨1132857964810971836941225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510477286414629115921633 1132857964810971836941225)
                      ·
                        rfl

theorem cell23_2206233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_2206233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206233 prefixEnd_2206233 := by exact prefixLift 2206233
  have htrace : WordTrace (prefixWord ++ tailWord_2206233) baseStart_2206233 baseEnd_2206233 := by
    simpa [prefixWord, tailWord_2206233, baseEnd_2206233] using wordTrace_append hprefix tailTrace_2206233
  have hstable : (prefixWord ++ tailWord_2206233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206233).length < 2 ^ (prefixWord ++ tailWord_2206233).sum := by decide
  have hdescent : baseEnd_2206233 < baseStart_2206233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206243 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 2, 5]
def baseStart_2206243 : Nat := 118140960795 + 2206243 * 2 ^ 59
def prefixEnd_2206243 : Nat := 4983230072969 + 3 ^ 40 * 2206243 * 2
def baseEnd_2206243 : Nat := 377621033205838932605393

theorem tailTrace_2206243 : CollatzResearch.WordTrace tailWord_2206243 prefixEnd_2206243 377621033205838932605393 := by
  unfold tailWord_2206243
  simp only [CollatzResearch.WordTrace]
  refine ⟨80468292946165882151223383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53645528630777254767482255 80468292946165882151223383)
  ·
    refine ⟨120702439419248823226835075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80468292946165882151223383 120702439419248823226835075)
    ·
      refine ⟨181053659128873234840252613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120702439419248823226835075 181053659128873234840252613)
      ·
        refine ⟨33947561086663731532547365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181053659128873234840252613 33947561086663731532547365)
        ·
          refine ⟨6365167703749449662352631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33947561086663731532547365 6365167703749449662352631)
          ·
            refine ⟨9547751555624174493528947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6365167703749449662352631 9547751555624174493528947)
            ·
              refine ⟨14321627333436261740293421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9547751555624174493528947 14321627333436261740293421)
              ·
                refine ⟨5370610250038598152610033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14321627333436261740293421 5370610250038598152610033)
                ·
                  refine ⟨4027957687528948614457525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370610250038598152610033 4027957687528948614457525)
                  ·
                    refine ⟨377621033205838932605393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4027957687528948614457525 377621033205838932605393)
                    ·
                      rfl

theorem cell23_2206243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 5].length) (baseStart_2206243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206243 prefixEnd_2206243 := by exact prefixLift 2206243
  have htrace : WordTrace (prefixWord ++ tailWord_2206243) baseStart_2206243 baseEnd_2206243 := by
    simpa [prefixWord, tailWord_2206243, baseEnd_2206243] using wordTrace_append hprefix tailTrace_2206243
  have hstable : (prefixWord ++ tailWord_2206243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206243).length < 2 ^ (prefixWord ++ tailWord_2206243).sum := by decide
  have hdescent : baseEnd_2206243 < baseStart_2206243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206263 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_2206263 : Nat := 118140960795 + 2206263 * 2 ^ 59
def prefixEnd_2206263 : Nat := 4983230072969 + 3 ^ 40 * 2206263 * 2
def baseEnd_2206263 : Nat := 1132873369230606719566087

theorem tailTrace_2206263 : CollatzResearch.WordTrace tailWord_2206263 prefixEnd_2206263 1132873369230606719566087 := by
  unfold tailWord_2206263
  simp only [CollatzResearch.WordTrace]
  refine ⟨80469022406093425566951443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53646014937395617044634295 80469022406093425566951443)
  ·
    refine ⟨120703533609140138350427165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80469022406093425566951443 120703533609140138350427165)
    ·
      refine ⟨45263825103427551881410187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120703533609140138350427165 45263825103427551881410187)
      ·
        refine ⟨67895737655141327822115281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45263825103427551881410187 67895737655141327822115281)
        ·
          refine ⟨50921803241355995866586461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67895737655141327822115281 50921803241355995866586461)
          ·
            refine ⟨19095676215508498449969923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50921803241355995866586461 19095676215508498449969923)
            ·
              refine ⟨28643514323262747674954885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19095676215508498449969923 28643514323262747674954885)
              ·
                refine ⟨5370658935611765189054041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28643514323262747674954885 5370658935611765189054041)
                ·
                  refine ⟨4027994201708823891790531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370658935611765189054041 4027994201708823891790531)
                  ·
                    refine ⟨6041991302563235837685797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4027994201708823891790531 6041991302563235837685797)
                    ·
                      refine ⟨1132873369230606719566087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6041991302563235837685797 1132873369230606719566087)
                      ·
                        rfl

theorem cell23_2206263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_2206263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206263 prefixEnd_2206263 := by exact prefixLift 2206263
  have htrace : WordTrace (prefixWord ++ tailWord_2206263) baseStart_2206263 baseEnd_2206263 := by
    simpa [prefixWord, tailWord_2206263, baseEnd_2206263] using wordTrace_append hprefix tailTrace_2206263
  have hstable : (prefixWord ++ tailWord_2206263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206263).length < 2 ^ (prefixWord ++ tailWord_2206263).sum := by decide
  have hdescent : baseEnd_2206263 < baseStart_2206263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206283 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3]
def baseStart_2206283 : Nat := 118140960795 + 2206283 * 2 ^ 59
def prefixEnd_2206283 : Nat := 4983230072969 + 3 ^ 40 * 2206283 * 2
def baseEnd_2206283 : Nat := 1132883638843696641315995

theorem tailTrace_2206283 : CollatzResearch.WordTrace tailWord_2206283 prefixEnd_2206283 1132883638843696641315995 := by
  unfold tailWord_2206283
  simp only [CollatzResearch.WordTrace]
  refine ⟨80469751866020968982679503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53646501244013979321786335 80469751866020968982679503)
  ·
    refine ⟨120704627799031453474019255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80469751866020968982679503 120704627799031453474019255)
    ·
      refine ⟨181056941698547180211028883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120704627799031453474019255 181056941698547180211028883)
      ·
        refine ⟨271585412547820770316543325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181056941698547180211028883 271585412547820770316543325)
        ·
          refine ⟨101844529705432788868703747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271585412547820770316543325 101844529705432788868703747)
          ·
            refine ⟨152766794558149183303055621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101844529705432788868703747 152766794558149183303055621)
            ·
              refine ⟨28643773979652971869322929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152766794558149183303055621 28643773979652971869322929)
              ·
                refine ⟨21482830484739728901992197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28643773979652971869322929 21482830484739728901992197)
                ·
                  refine ⟨4028030715888699169123537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21482830484739728901992197 4028030715888699169123537)
                  ·
                    refine ⟨3021023036916524376842653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028030715888699169123537 3021023036916524376842653)
                    ·
                      refine ⟨1132883638843696641315995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021023036916524376842653 1132883638843696641315995)
                      ·
                        rfl

theorem cell23_2206283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3].length) (baseStart_2206283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206283 prefixEnd_2206283 := by exact prefixLift 2206283
  have htrace : WordTrace (prefixWord ++ tailWord_2206283) baseStart_2206283 baseEnd_2206283 := by
    simpa [prefixWord, tailWord_2206283, baseEnd_2206283] using wordTrace_append hprefix tailTrace_2206283
  have hstable : (prefixWord ++ tailWord_2206283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206283).length < 2 ^ (prefixWord ++ tailWord_2206283).sum := by decide
  have hdescent : baseEnd_2206283 < baseStart_2206283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206290 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2206290 : Nat := 118140960795 + 2206290 * 2 ^ 59
def prefixEnd_2206290 : Nat := 4983230072969 + 3 ^ 40 * 2206290 * 2
def baseEnd_2206290 : Nat := 377629077736092704642821

theorem tailTrace_2206290 : CollatzResearch.WordTrace tailWord_2206290 prefixEnd_2206290 377629077736092704642821 := by
  unfold tailWord_2206290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117501794248902294546081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53646671451330406118789549 20117501794248902294546081)
  ·
    refine ⟨15088126345686676720909561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20117501794248902294546081 15088126345686676720909561)
    ·
      refine ⟨11316094759265007540682171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15088126345686676720909561 11316094759265007540682171)
      ·
        refine ⟨16974142138897511311023257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11316094759265007540682171 16974142138897511311023257)
        ·
          refine ⟨12730606604173133483267443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16974142138897511311023257 12730606604173133483267443)
          ·
            refine ⟨19095909906259700224901165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12730606604173133483267443 19095909906259700224901165)
            ·
              refine ⟨7160966214847387584337937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19095909906259700224901165 7160966214847387584337937)
              ·
                refine ⟨5370724661135540688253453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7160966214847387584337937 5370724661135540688253453)
                ·
                  refine ⟨2014021747925827758095045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5370724661135540688253453 2014021747925827758095045)
                  ·
                    refine ⟨377629077736092704642821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014021747925827758095045 377629077736092704642821)
                    ·
                      rfl

theorem cell23_2206290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2206290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206290 prefixEnd_2206290 := by exact prefixLift 2206290
  have htrace : WordTrace (prefixWord ++ tailWord_2206290) baseStart_2206290 baseEnd_2206290 := by
    simpa [prefixWord, tailWord_2206290, baseEnd_2206290] using wordTrace_append hprefix tailTrace_2206290
  have hstable : (prefixWord ++ tailWord_2206290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206290).length < 2 ^ (prefixWord ++ tailWord_2206290).sum := by decide
  have hdescent : baseEnd_2206290 < baseStart_2206290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206307 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 1, 4]
def baseStart_2206307 : Nat := 118140960795 + 2206307 * 2 ^ 59
def prefixEnd_2206307 : Nat := 4983230072969 + 3 ^ 40 * 2206307 * 2
def baseEnd_2206307 : Nat := 377631987459801515805295

theorem tailTrace_2206307 : CollatzResearch.WordTrace tailWord_2206307 prefixEnd_2206307 377631987459801515805295 := by
  unfold tailWord_2206307
  simp only [CollatzResearch.WordTrace]
  refine ⟨80470627217934021081553175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53647084811956014054368783 80470627217934021081553175)
  ·
    refine ⟨120705940826901031622329763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80470627217934021081553175 120705940826901031622329763)
    ·
      refine ⟨181058911240351547433494645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120705940826901031622329763 181058911240351547433494645)
      ·
        refine ⟨16974272928782957571890123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181058911240351547433494645 16974272928782957571890123)
        ·
          refine ⟨25461409393174436357835185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16974272928782957571890123 25461409393174436357835185)
          ·
            refine ⟨19096057044880827268376389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25461409393174436357835185 19096057044880827268376389)
            ·
              refine ⟨3580510695915155112820573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19096057044880827268376389 3580510695915155112820573)
              ·
                refine ⟨1342691510968183167307715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3580510695915155112820573 1342691510968183167307715)
                ·
                  refine ⟨2014037266452274750961573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342691510968183167307715 2014037266452274750961573)
                  ·
                    refine ⟨377631987459801515805295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014037266452274750961573 377631987459801515805295)
                    ·
                      rfl

theorem cell23_2206307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 4].length) (baseStart_2206307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206307 prefixEnd_2206307 := by exact prefixLift 2206307
  have htrace : WordTrace (prefixWord ++ tailWord_2206307) baseStart_2206307 baseEnd_2206307 := by
    simpa [prefixWord, tailWord_2206307, baseEnd_2206307] using wordTrace_append hprefix tailTrace_2206307
  have hstable : (prefixWord ++ tailWord_2206307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206307).length < 2 ^ (prefixWord ++ tailWord_2206307).sum := by decide
  have hdescent : baseEnd_2206307 < baseStart_2206307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206353 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_2206353 : Nat := 118140960795 + 2206353 * 2 ^ 59
def prefixEnd_2206353 : Nat := 4983230072969 + 3 ^ 40 * 2206353 * 2
def baseEnd_2206353 : Nat := 1132919582489511367440673

theorem tailTrace_2206353 : CollatzResearch.WordTrace tailWord_2206353 prefixEnd_2206353 1132919582489511367440673 := by
  unfold tailWord_2206353
  simp only [CollatzResearch.WordTrace]
  refine ⟨80472304975767370937727713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53648203317178247291818475 80472304975767370937727713)
  ·
    refine ⟨60354228731825528203295785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80472304975767370937727713 60354228731825528203295785)
    ·
      refine ⟨45265671548869146152471839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60354228731825528203295785 45265671548869146152471839)
      ·
        refine ⟨67898507323303719228707759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45265671548869146152471839 67898507323303719228707759)
        ·
          refine ⟨101847760984955578843061639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67898507323303719228707759 101847760984955578843061639)
          ·
            refine ⟨152771641477433368264592459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101847760984955578843061639 152771641477433368264592459)
            ·
              refine ⟨229157462216150052396888689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152771641477433368264592459 229157462216150052396888689)
              ·
                refine ⟨171868096662112539297666517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229157462216150052396888689 171868096662112539297666517)
                ·
                  refine ⟨4028158515518262639789059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171868096662112539297666517 4028158515518262639789059)
                  ·
                    refine ⟨6042237773277393959683589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028158515518262639789059 6042237773277393959683589)
                    ·
                      refine ⟨1132919582489511367440673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6042237773277393959683589 1132919582489511367440673)
                      ·
                        rfl

theorem cell23_2206353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_2206353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206353 prefixEnd_2206353 := by exact prefixLift 2206353
  have htrace : WordTrace (prefixWord ++ tailWord_2206353) baseStart_2206353 baseEnd_2206353 := by
    simpa [prefixWord, tailWord_2206353, baseEnd_2206353] using wordTrace_append hprefix tailTrace_2206353
  have hstable : (prefixWord ++ tailWord_2206353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206353).length < 2 ^ (prefixWord ++ tailWord_2206353).sum := by decide
  have hdescent : baseEnd_2206353 < baseStart_2206353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206383 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_2206383 : Nat := 118140960795 + 2206383 * 2 ^ 59
def prefixEnd_2206383 : Nat := 4983230072969 + 3 ^ 40 * 2206383 * 2
def baseEnd_2206383 : Nat := 1132934986909146250065535

theorem tailTrace_2206383 : CollatzResearch.WordTrace tailWord_2206383 prefixEnd_2206383 1132934986909146250065535 := by
  unfold tailWord_2206383
  simp only [CollatzResearch.WordTrace]
  refine ⟨80473399165658686061319803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53648932777105790707546535 80473399165658686061319803)
  ·
    refine ⟨120710098748488029091979705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80473399165658686061319803 120710098748488029091979705)
    ·
      refine ⟨90532574061366021818984779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120710098748488029091979705 90532574061366021818984779)
      ·
        refine ⟨135798861092049032728477169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90532574061366021818984779 135798861092049032728477169)
        ·
          refine ⟨101849145819036774546357877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135798861092049032728477169 101849145819036774546357877)
          ·
            refine ⟨9548357420534697613721051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101849145819036774546357877 9548357420534697613721051)
            ·
              refine ⟨14322536130802046420581577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9548357420534697613721051 14322536130802046420581577)
              ·
                refine ⟨10741902098101534815436183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14322536130802046420581577 10741902098101534815436183)
                ·
                  refine ⟨16112853147152302223154275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10741902098101534815436183 16112853147152302223154275)
                  ·
                    refine ⟨24169279720728453334731413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16112853147152302223154275 24169279720728453334731413)
                    ·
                      refine ⟨1132934986909146250065535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24169279720728453334731413 1132934986909146250065535)
                      ·
                        rfl

theorem cell23_2206383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_2206383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206383 prefixEnd_2206383 := by exact prefixLift 2206383
  have htrace : WordTrace (prefixWord ++ tailWord_2206383) baseStart_2206383 baseEnd_2206383 := by
    simpa [prefixWord, tailWord_2206383, baseEnd_2206383] using wordTrace_append hprefix tailTrace_2206383
  have hstable : (prefixWord ++ tailWord_2206383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206383).length < 2 ^ (prefixWord ++ tailWord_2206383).sum := by decide
  have hdescent : baseEnd_2206383 < baseStart_2206383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206397 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2206397 : Nat := 118140960795 + 2206397 * 2 ^ 59
def prefixEnd_2206397 : Nat := 4983230072969 + 3 ^ 40 * 2206397 * 2
def baseEnd_2206397 : Nat := 377647391879436398430157

theorem tailTrace_2206397 : CollatzResearch.WordTrace tailWord_2206397 prefixEnd_2206397 377647391879436398430157 := by
  unfold tailWord_2206397
  simp only [CollatzResearch.WordTrace]
  refine ⟨80473909787607966452329445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53649273191738644301552963 80473909787607966452329445)
  ·
    refine ⟨15088858085176493709811771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80473909787607966452329445 15088858085176493709811771)
    ·
      refine ⟨22633287127764740564717657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15088858085176493709811771 22633287127764740564717657)
      ·
        refine ⟨16974965345823555423538243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22633287127764740564717657 16974965345823555423538243)
        ·
          refine ⟨25462448018735333135307365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16974965345823555423538243 25462448018735333135307365)
          ·
            refine ⟨4774209003512874962870131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25462448018735333135307365 4774209003512874962870131)
            ·
              refine ⟨7161313505269312444305197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774209003512874962870131 7161313505269312444305197)
              ·
                refine ⟨2685492564475992166614449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7161313505269312444305197 2685492564475992166614449)
                ·
                  refine ⟨2014119423356994124960837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685492564475992166614449 2014119423356994124960837)
                  ·
                    refine ⟨377647391879436398430157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014119423356994124960837 377647391879436398430157)
                    ·
                      rfl

theorem cell23_2206397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2206397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206397 prefixEnd_2206397 := by exact prefixLift 2206397
  have htrace : WordTrace (prefixWord ++ tailWord_2206397) baseStart_2206397 baseEnd_2206397 := by
    simpa [prefixWord, tailWord_2206397, baseEnd_2206397] using wordTrace_append hprefix tailTrace_2206397
  have hstable : (prefixWord ++ tailWord_2206397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206397).length < 2 ^ (prefixWord ++ tailWord_2206397).sum := by decide
  have hdescent : baseEnd_2206397 < baseStart_2206397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206401 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2206401 : Nat := 118140960795 + 2206401 * 2 ^ 59
def prefixEnd_2206401 : Nat := 4983230072969 + 3 ^ 40 * 2206401 * 2
def baseEnd_2206401 : Nat := 377648076520309059880151

theorem tailTrace_2206401 : CollatzResearch.WordTrace tailWord_2206401 prefixEnd_2206401 377648076520309059880151 := by
  unfold tailWord_2206401
  simp only [CollatzResearch.WordTrace]
  refine ⟨80474055679593475135475057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53649370453062316756983371 80474055679593475135475057)
  ·
    refine ⟨60355541759695106351606293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80474055679593475135475057 60355541759695106351606293)
    ·
      refine ⟨2829166019985708110231545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60355541759695106351606293 2829166019985708110231545)
      ·
        refine ⟨2121874514989281082673659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2829166019985708110231545 2121874514989281082673659)
        ·
          refine ⟨3182811772483921624010489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121874514989281082673659 3182811772483921624010489)
          ·
            refine ⟨2387108829362941218007867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3182811772483921624010489 2387108829362941218007867)
            ·
              refine ⟨3580663244044411827011801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387108829362941218007867 3580663244044411827011801)
              ·
                refine ⟨2685497433033308870258851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580663244044411827011801 2685497433033308870258851)
                ·
                  refine ⟨4028246149549963305388277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685497433033308870258851 4028246149549963305388277)
                  ·
                    refine ⟨377648076520309059880151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4028246149549963305388277 377648076520309059880151)
                    ·
                      rfl

theorem cell23_2206401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2206401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206401 prefixEnd_2206401 := by exact prefixLift 2206401
  have htrace : WordTrace (prefixWord ++ tailWord_2206401) baseStart_2206401 baseEnd_2206401 := by
    simpa [prefixWord, tailWord_2206401, baseEnd_2206401] using wordTrace_append hprefix tailTrace_2206401
  have hstable : (prefixWord ++ tailWord_2206401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206401).length < 2 ^ (prefixWord ++ tailWord_2206401).sum := by decide
  have hdescent : baseEnd_2206401 < baseStart_2206401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206404 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2206404 : Nat := 118140960795 + 2206404 * 2 ^ 59
def prefixEnd_2206404 : Nat := 4983230072969 + 3 ^ 40 * 2206404 * 2
def baseEnd_2206404 : Nat := 1132945770002890667902939

theorem tailTrace_2206404 : CollatzResearch.WordTrace tailWord_2206404 prefixEnd_2206404 1132945770002890667902939 := by
  unfold tailWord_2206404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40237082549291303323917133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53649443399055071098556177 40237082549291303323917133)
  ·
    refine ⟨15088905955984238746468925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40237082549291303323917133 15088905955984238746468925)
    ·
      refine ⟨5658339733494089529925847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15088905955984238746468925 5658339733494089529925847)
      ·
        refine ⟨8487509600241134294888771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658339733494089529925847 8487509600241134294888771)
        ·
          refine ⟨12731264400361701442333157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8487509600241134294888771 12731264400361701442333157)
          ·
            refine ⟨2387112075067819020437467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12731264400361701442333157 2387112075067819020437467)
            ·
              refine ⟨3580668112601728530656201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387112075067819020437467 3580668112601728530656201)
              ·
                refine ⟨2685501084451296397992151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580668112601728530656201 2685501084451296397992151)
                ·
                  refine ⟨4028251626676944596988227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685501084451296397992151 4028251626676944596988227)
                  ·
                    refine ⟨6042377440015416895482341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028251626676944596988227 6042377440015416895482341)
                    ·
                      refine ⟨1132945770002890667902939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6042377440015416895482341 1132945770002890667902939)
                      ·
                        rfl

theorem cell23_2206404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2206404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206404 prefixEnd_2206404 := by exact prefixLift 2206404
  have htrace : WordTrace (prefixWord ++ tailWord_2206404) baseStart_2206404 baseEnd_2206404 := by
    simpa [prefixWord, tailWord_2206404, baseEnd_2206404] using wordTrace_append hprefix tailTrace_2206404
  have hstable : (prefixWord ++ tailWord_2206404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206404).length < 2 ^ (prefixWord ++ tailWord_2206404).sum := by decide
  have hdescent : baseEnd_2206404 < baseStart_2206404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206421 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2206421 : Nat := 118140960795 + 2206421 * 2 ^ 59
def prefixEnd_2206421 : Nat := 4983230072969 + 3 ^ 40 * 2206421 * 2
def baseEnd_2206421 : Nat := 1132954499174017101390361

theorem tailTrace_2206421 : CollatzResearch.WordTrace tailWord_2206421 prefixEnd_2206421 1132954499174017101390361 := by
  unfold tailWord_2206421
  simp only [CollatzResearch.WordTrace]
  refine ⟨80474785139521018551203117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53649856759680679034135411 80474785139521018551203117)
  ·
    refine ⟨30178044427320381956701169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80474785139521018551203117 30178044427320381956701169)
    ·
      refine ⟨22633533320490286467525877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30178044427320381956701169 22633533320490286467525877)
      ·
        refine ⟨2121893748795964356330551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22633533320490286467525877 2121893748795964356330551)
        ·
          refine ⟨3182840623193946534495827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121893748795964356330551 3182840623193946534495827)
          ·
            refine ⟨4774260934790919801743741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182840623193946534495827 4774260934790919801743741)
            ·
              refine ⟨1790347850546594925653903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4774260934790919801743741 1790347850546594925653903)
              ·
                refine ⟨2685521775819892388480855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790347850546594925653903 2685521775819892388480855)
                ·
                  refine ⟨4028282663729838582721283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685521775819892388480855 4028282663729838582721283)
                  ·
                    refine ⟨6042423995594757874081925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028282663729838582721283 6042423995594757874081925)
                    ·
                      refine ⟨1132954499174017101390361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6042423995594757874081925 1132954499174017101390361)
                      ·
                        rfl

theorem cell23_2206421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2206421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206421 prefixEnd_2206421 := by exact prefixLift 2206421
  have htrace : WordTrace (prefixWord ++ tailWord_2206421) baseStart_2206421 baseEnd_2206421 := by
    simpa [prefixWord, tailWord_2206421, baseEnd_2206421] using wordTrace_append hprefix tailTrace_2206421
  have hstable : (prefixWord ++ tailWord_2206421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206421).length < 2 ^ (prefixWord ++ tailWord_2206421).sum := by decide
  have hdescent : baseEnd_2206421 < baseStart_2206421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206424 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_2206424 : Nat := 118140960795 + 2206424 * 2 ^ 59
def prefixEnd_2206424 : Nat := 4983230072969 + 3 ^ 40 * 2206424 * 2
def baseEnd_2206424 : Nat := 1132956039615980589652847

theorem tailTrace_2206424 : CollatzResearch.WordTrace tailWord_2206424 prefixEnd_2206424 1132956039615980589652847 := by
  unfold tailWord_2206424
  simp only [CollatzResearch.WordTrace]
  refine ⟨40237447279255075031781163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53649929705673433375708217 40237447279255075031781163)
  ·
    refine ⟨60356170918882612547671745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40237447279255075031781163 60356170918882612547671745)
    ·
      refine ⟨45267128189161959410753809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60356170918882612547671745 45267128189161959410753809)
      ·
        refine ⟨33950346141871469558065357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45267128189161959410753809 33950346141871469558065357)
        ·
          refine ⟨12731379803201801084274509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33950346141871469558065357 12731379803201801084274509)
          ·
            refine ⟨4774267426200675406602941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12731379803201801084274509 4774267426200675406602941)
            ·
              refine ⟨1790350284825253277476103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4774267426200675406602941 1790350284825253277476103)
              ·
                refine ⟨2685525427237879916214155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790350284825253277476103 2685525427237879916214155)
                ·
                  refine ⟨4028288140856819874321233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685525427237879916214155 4028288140856819874321233)
                  ·
                    refine ⟨3021216105642614905740925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028288140856819874321233 3021216105642614905740925)
                    ·
                      refine ⟨1132956039615980589652847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021216105642614905740925 1132956039615980589652847)
                      ·
                        rfl

theorem cell23_2206424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_2206424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206424 prefixEnd_2206424 := by exact prefixLift 2206424
  have htrace : WordTrace (prefixWord ++ tailWord_2206424) baseStart_2206424 baseEnd_2206424 := by
    simpa [prefixWord, tailWord_2206424, baseEnd_2206424] using wordTrace_append hprefix tailTrace_2206424
  have hstable : (prefixWord ++ tailWord_2206424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206424).length < 2 ^ (prefixWord ++ tailWord_2206424).sum := by decide
  have hdescent : baseEnd_2206424 < baseStart_2206424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206447 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 3, 3, 2]
def baseStart_2206447 : Nat := 118140960795 + 2206447 * 2 ^ 59
def prefixEnd_2206447 : Nat := 4983230072969 + 3 ^ 40 * 2206447 * 2
def baseEnd_2206447 : Nat := 1132967849671033999665241

theorem tailTrace_2206447 : CollatzResearch.WordTrace tailWord_2206447 prefixEnd_2206447 1132967849671033999665241 := by
  unfold tailWord_2206447
  simp only [CollatzResearch.WordTrace]
  refine ⟨80475733437426824991649595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53650488958284549994433063 80475733437426824991649595)
  ·
    refine ⟨120713600156140237487474393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80475733437426824991649595 120713600156140237487474393)
    ·
      refine ⟨90535200117105178115605795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120713600156140237487474393 90535200117105178115605795)
      ·
        refine ⟨135802800175657767173408693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90535200117105178115605795 135802800175657767173408693)
        ·
          refine ⟨12731512516467915672507065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135802800175657767173408693 12731512516467915672507065)
          ·
            refine ⟨9548634387350936754380299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12731512516467915672507065 9548634387350936754380299)
            ·
              refine ⟨14322951581026405131570449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9548634387350936754380299 14322951581026405131570449)
              ·
                refine ⟨10742213685769803848677837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14322951581026405131570449 10742213685769803848677837)
                ·
                  refine ⟨4028330132163676443254189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10742213685769803848677837 4028330132163676443254189)
                  ·
                    refine ⟨1510623799561378666220321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4028330132163676443254189 1510623799561378666220321)
                    ·
                      refine ⟨1132967849671033999665241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510623799561378666220321 1132967849671033999665241)
                      ·
                        rfl

theorem cell23_2206447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3, 2].length) (baseStart_2206447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206447 prefixEnd_2206447 := by exact prefixLift 2206447
  have htrace : WordTrace (prefixWord ++ tailWord_2206447) baseStart_2206447 baseEnd_2206447 := by
    simpa [prefixWord, tailWord_2206447, baseEnd_2206447] using wordTrace_append hprefix tailTrace_2206447
  have hstable : (prefixWord ++ tailWord_2206447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206447).length < 2 ^ (prefixWord ++ tailWord_2206447).sum := by decide
  have hdescent : baseEnd_2206447 < baseStart_2206447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206454 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2206454 : Nat := 118140960795 + 2206454 * 2 ^ 59
def prefixEnd_2206454 : Nat := 4983230072969 + 3 ^ 40 * 2206454 * 2
def baseEnd_2206454 : Nat := 1132971444035615472277709

theorem tailTrace_2206454 : CollatzResearch.WordTrace tailWord_2206454 prefixEnd_2206454 1132971444035615472277709 := by
  unfold tailWord_2206454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029749296775091574197151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53650659165600976791436277 5029749296775091574197151)
  ·
    refine ⟨7544623945162637361295727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029749296775091574197151 7544623945162637361295727)
    ·
      refine ⟨11316935917743956041943591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7544623945162637361295727 11316935917743956041943591)
      ·
        refine ⟨16975403876615934062915387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11316935917743956041943591 16975403876615934062915387)
        ·
          refine ⟨25463105814923901094373081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16975403876615934062915387 25463105814923901094373081)
          ·
            refine ⟨19097329361192925820779811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25463105814923901094373081 19097329361192925820779811)
            ·
              refine ⟨28645994041789388731169717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19097329361192925820779811 28645994041789388731169717)
              ·
                refine ⟨2685561941417755193547161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28645994041789388731169717 2685561941417755193547161)
                ·
                  refine ⟨2014171456063316395160371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685561941417755193547161 2014171456063316395160371)
                  ·
                    refine ⟨3021257184094974592740557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014171456063316395160371 3021257184094974592740557)
                    ·
                      refine ⟨1132971444035615472277709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021257184094974592740557 1132971444035615472277709)
                      ·
                        rfl

theorem cell23_2206454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2206454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206454 prefixEnd_2206454 := by exact prefixLift 2206454
  have htrace : WordTrace (prefixWord ++ tailWord_2206454) baseStart_2206454 baseEnd_2206454 := by
    simpa [prefixWord, tailWord_2206454, baseEnd_2206454] using wordTrace_append hprefix tailTrace_2206454
  have hstable : (prefixWord ++ tailWord_2206454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206454).length < 2 ^ (prefixWord ++ tailWord_2206454).sum := by decide
  have hdescent : baseEnd_2206454 < baseStart_2206454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206483 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 9]
def baseStart_2206483 : Nat := 118140960795 + 2206483 * 2 ^ 59
def prefixEnd_2206483 : Nat := 4983230072969 + 3 ^ 40 * 2206483 * 2
def baseEnd_2206483 : Nat := 125887370552732873201675

theorem tailTrace_2206483 : CollatzResearch.WordTrace tailWord_2206483 prefixEnd_2206483 125887370552732873201675 := by
  unfold tailWord_2206483
  simp only [CollatzResearch.WordTrace]
  refine ⟨80477046465296403139960103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53651364310197602093306735 80477046465296403139960103)
  ·
    refine ⟨120715569697944604709940155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80477046465296403139960103 120715569697944604709940155)
    ·
      refine ⟨181073354546916907064910233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120715569697944604709940155 181073354546916907064910233)
      ·
        refine ⟨135805015910187680298682675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181073354546916907064910233 135805015910187680298682675)
        ·
          refine ⟨203707523865281520448024013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135805015910187680298682675 203707523865281520448024013)
          ·
            refine ⟨76390321449480570168009005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203707523865281520448024013 76390321449480570168009005)
            ·
              refine ⟨28646370543555213813003377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76390321449480570168009005 28646370543555213813003377)
              ·
                refine ⟨21484777907666410359752533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28646370543555213813003377 21484777907666410359752533)
                ·
                  refine ⟨125887370552732873201675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21484777907666410359752533 125887370552732873201675)
                  ·
                    rfl

theorem cell23_2206483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 9].length) (baseStart_2206483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206483 prefixEnd_2206483 := by exact prefixLift 2206483
  have htrace : WordTrace (prefixWord ++ tailWord_2206483) baseStart_2206483 baseEnd_2206483 := by
    simpa [prefixWord, tailWord_2206483, baseEnd_2206483] using wordTrace_append hprefix tailTrace_2206483
  have hstable : (prefixWord ++ tailWord_2206483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206483).length < 2 ^ (prefixWord ++ tailWord_2206483).sum := by decide
  have hdescent : baseEnd_2206483 < baseStart_2206483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206490 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2206490 : Nat := 118140960795 + 2206490 * 2 ^ 59
def prefixEnd_2206490 : Nat := 4983230072969 + 3 ^ 40 * 2206490 * 2
def baseEnd_2206490 : Nat := 1132989929339177331427543

theorem tailTrace_2206490 : CollatzResearch.WordTrace tailWord_2206490 prefixEnd_2206490 1132989929339177331427543 := by
  unfold tailWord_2206490
  simp only [CollatzResearch.WordTrace]
  refine ⟨20119325444067760833866231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53651534517514028890309949 20119325444067760833866231)
  ·
    refine ⟨30178988166101641250799347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20119325444067760833866231 30178988166101641250799347)
    ·
      refine ⟨45268482249152461876199021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30178988166101641250799347 45268482249152461876199021)
      ·
        refine ⟨16975680843432173203574633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45268482249152461876199021 16975680843432173203574633)
        ·
          refine ⟨12731760632574129902680975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16975680843432173203574633 12731760632574129902680975)
          ·
            refine ⟨19097640948861194854021463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12731760632574129902680975 19097640948861194854021463)
            ·
              refine ⟨28646461423291792281032195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19097640948861194854021463 28646461423291792281032195)
              ·
                refine ⟨42969692134937688421548293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28646461423291792281032195 42969692134937688421548293)
                ·
                  refine ⟨8056817275300816579040305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42969692134937688421548293 8056817275300816579040305)
                  ·
                    refine ⟨6042612956475612434280229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8056817275300816579040305 6042612956475612434280229)
                    ·
                      refine ⟨1132989929339177331427543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6042612956475612434280229 1132989929339177331427543)
                      ·
                        rfl

theorem cell23_2206490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2206490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206490 prefixEnd_2206490 := by exact prefixLift 2206490
  have htrace : WordTrace (prefixWord ++ tailWord_2206490) baseStart_2206490 baseEnd_2206490 := by
    simpa [prefixWord, tailWord_2206490, baseEnd_2206490] using wordTrace_append hprefix tailTrace_2206490
  have hstable : (prefixWord ++ tailWord_2206490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206490).length < 2 ^ (prefixWord ++ tailWord_2206490).sum := by decide
  have hdescent : baseEnd_2206490 < baseStart_2206490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206562 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2206562 : Nat := 118140960795 + 2206562 * 2 ^ 59
def prefixEnd_2206562 : Nat := 4983230072969 + 3 ^ 40 * 2206562 * 2
def baseEnd_2206562 : Nat := 1133026899946301049727213

theorem tailTrace_2206562 : CollatzResearch.WordTrace tailWord_2206562 prefixEnd_2206562 1133026899946301049727213 := by
  unfold tailWord_2206562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20119981958002549908021485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53653285221340133088057293 20119981958002549908021485)
  ·
    refine ⟨7544993234250956215508057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20119981958002549908021485 7544993234250956215508057)
    ·
      refine ⟨5658744925688217161631043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7544993234250956215508057 5658744925688217161631043)
      ·
        refine ⟨8488117388532325742446565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658744925688217161631043 8488117388532325742446565)
        ·
          refine ⟨1591522010349811076708731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8488117388532325742446565 1591522010349811076708731)
          ·
            refine ⟨2387283015524716615063097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591522010349811076708731 2387283015524716615063097)
            ·
              refine ⟨1790462261643537461297323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387283015524716615063097 1790462261643537461297323)
              ·
                refine ⟨2685693392465306191945985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790462261643537461297323 2685693392465306191945985)
                ·
                  refine ⟨2014270044348979643959489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685693392465306191945985 2014270044348979643959489)
                  ·
                    refine ⟨1510702533261734732969617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2014270044348979643959489 1510702533261734732969617)
                    ·
                      refine ⟨1133026899946301049727213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510702533261734732969617 1133026899946301049727213)
                      ·
                        rfl

theorem cell23_2206562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2206562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206562 prefixEnd_2206562 := by exact prefixLift 2206562
  have htrace : WordTrace (prefixWord ++ tailWord_2206562) baseStart_2206562 baseEnd_2206562 := by
    simpa [prefixWord, tailWord_2206562, baseEnd_2206562] using wordTrace_append hprefix tailTrace_2206562
  have hstable : (prefixWord ++ tailWord_2206562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206562).length < 2 ^ (prefixWord ++ tailWord_2206562).sum := by decide
  have hdescent : baseEnd_2206562 < baseStart_2206562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206587 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3]
def baseStart_2206587 : Nat := 118140960795 + 2206587 * 2 ^ 59
def prefixEnd_2206587 : Nat := 4983230072969 + 3 ^ 40 * 2206587 * 2
def baseEnd_2206587 : Nat := 1133039736962663451914597

theorem tailTrace_2206587 : CollatzResearch.WordTrace tailWord_2206587 prefixEnd_2206587 1133039736962663451914597 := by
  unfold tailWord_2206587
  simp only [CollatzResearch.WordTrace]
  refine ⟨80480839656919628901746015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53653893104613085934497343 80480839656919628901746015)
  ·
    refine ⟨120721259485379443352619023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80480839656919628901746015 120721259485379443352619023)
    ·
      refine ⟨181081889228069165028928535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120721259485379443352619023 181081889228069165028928535)
      ·
        refine ⟨271622833842103747543392803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181081889228069165028928535 271622833842103747543392803)
        ·
          refine ⟨407434250763155621315089205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271622833842103747543392803 407434250763155621315089205)
          ·
            refine ⟨38196961009045839498289613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 407434250763155621315089205 38196961009045839498289613)
            ·
              refine ⟨14323860378392189811858605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38196961009045839498289613 14323860378392189811858605)
              ·
                refine ⟨5371447641897071179446977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14323860378392189811858605 5371447641897071179446977)
                ·
                  refine ⟨4028585731422803384585233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5371447641897071179446977 4028585731422803384585233)
                  ·
                    refine ⟨3021439298567102538438925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028585731422803384585233 3021439298567102538438925)
                    ·
                      refine ⟨1133039736962663451914597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021439298567102538438925 1133039736962663451914597)
                      ·
                        rfl

theorem cell23_2206587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3].length) (baseStart_2206587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206587 prefixEnd_2206587 := by exact prefixLift 2206587
  have htrace : WordTrace (prefixWord ++ tailWord_2206587) baseStart_2206587 baseEnd_2206587 := by
    simpa [prefixWord, tailWord_2206587, baseEnd_2206587] using wordTrace_append hprefix tailTrace_2206587
  have hstable : (prefixWord ++ tailWord_2206587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206587).length < 2 ^ (prefixWord ++ tailWord_2206587).sum := by decide
  have hdescent : baseEnd_2206587 < baseStart_2206587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206654 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2206654 : Nat := 118140960795 + 2206654 * 2 ^ 59
def prefixEnd_2206654 : Nat := 4983230072969 + 3 ^ 40 * 2206654 * 2
def baseEnd_2206654 : Nat := 377691380055504896592263

theorem tailTrace_2206654 : CollatzResearch.WordTrace tailWord_2206654 prefixEnd_2206654 377691380055504896592263 := by
  unfold tailWord_2206654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060410418459612418054377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53655522231784599562956677 10060410418459612418054377)
  ·
    refine ⟨7545307813844709313540783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10060410418459612418054377 7545307813844709313540783)
    ·
      refine ⟨11317961720767063970311175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7545307813844709313540783 11317961720767063970311175)
      ·
        refine ⟨16976942581150595955466763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11317961720767063970311175 16976942581150595955466763)
        ·
          refine ⟨25465413871725893933200145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16976942581150595955466763 25465413871725893933200145)
          ·
            refine ⟨19099060403794420449900109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25465413871725893933200145 19099060403794420449900109)
            ·
              refine ⟨7162147651422907668712541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19099060403794420449900109 7162147651422907668712541)
              ·
                refine ⟨2685805369283590375767203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7162147651422907668712541 2685805369283590375767203)
                ·
                  refine ⟨4028708053925385563650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685805369283590375767203 4028708053925385563650805)
                  ·
                    refine ⟨377691380055504896592263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4028708053925385563650805 377691380055504896592263)
                    ·
                      rfl

theorem cell23_2206654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2206654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206654 prefixEnd_2206654 := by exact prefixLift 2206654
  have htrace : WordTrace (prefixWord ++ tailWord_2206654) baseStart_2206654 baseEnd_2206654 := by
    simpa [prefixWord, tailWord_2206654, baseEnd_2206654] using wordTrace_append hprefix tailTrace_2206654
  have hstable : (prefixWord ++ tailWord_2206654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206654).length < 2 ^ (prefixWord ++ tailWord_2206654).sum := by decide
  have hdescent : baseEnd_2206654 < baseStart_2206654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206662 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2206662 : Nat := 118140960795 + 2206662 * 2 ^ 59
def prefixEnd_2206662 : Nat := 4983230072969 + 3 ^ 40 * 2206662 * 2
def baseEnd_2206662 : Nat := 377692749337250219492251

theorem tailTrace_2206662 : CollatzResearch.WordTrace tailWord_2206662 prefixEnd_2206662 377692749337250219492251 := by
  unfold tailWord_2206662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515111722863997397210195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53655716754431944473817493 2515111722863997397210195)
  ·
    refine ⟨3772667584295996095815293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515111722863997397210195 3772667584295996095815293)
    ·
      refine ⟨1414750344110998535930735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3772667584295996095815293 1414750344110998535930735)
      ·
        refine ⟨2122125516166497803896103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414750344110998535930735 2122125516166497803896103)
        ·
          refine ⟨3183188274249746705844155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122125516166497803896103 3183188274249746705844155)
          ·
            refine ⟨4774782411374620058766233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183188274249746705844155 4774782411374620058766233)
            ·
              refine ⟨3581086808530965044074675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4774782411374620058766233 3581086808530965044074675)
              ·
                refine ⟨5371630212796447566112013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581086808530965044074675 5371630212796447566112013)
                ·
                  refine ⟨2014361329798667837292005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5371630212796447566112013 2014361329798667837292005)
                  ·
                    refine ⟨377692749337250219492251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014361329798667837292005 377692749337250219492251)
                    ·
                      rfl

theorem cell23_2206662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2206662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206662 prefixEnd_2206662 := by exact prefixLift 2206662
  have htrace : WordTrace (prefixWord ++ tailWord_2206662) baseStart_2206662 baseEnd_2206662 := by
    simpa [prefixWord, tailWord_2206662, baseEnd_2206662] using wordTrace_append hprefix tailTrace_2206662
  have hstable : (prefixWord ++ tailWord_2206662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206662).length < 2 ^ (prefixWord ++ tailWord_2206662).sum := by decide
  have hdescent : baseEnd_2206662 < baseStart_2206662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206691 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2206691 : Nat := 118140960795 + 2206691 * 2 ^ 59
def prefixEnd_2206691 : Nat := 4983230072969 + 3 ^ 40 * 2206691 * 2
def baseEnd_2206691 : Nat := 1133093138950731045014119

theorem tailTrace_2206691 : CollatzResearch.WordTrace tailWord_2206691 prefixEnd_2206691 1133093138950731045014119 := by
  unfold tailWord_2206691
  simp only [CollatzResearch.WordTrace]
  refine ⟨80484632848542854663531927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53656421899028569775687951 80484632848542854663531927)
  ·
    refine ⟨120726949272814281995297891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80484632848542854663531927 120726949272814281995297891)
    ·
      refine ⟨181090423909221422992946837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120726949272814281995297891 181090423909221422992946837)
      ·
        refine ⟨8488613620744754202794383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 181090423909221422992946837 8488613620744754202794383)
        ·
          refine ⟨12732920431117131304191575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488613620744754202794383 12732920431117131304191575)
          ·
            refine ⟨19099380646675696956287363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12732920431117131304191575 19099380646675696956287363)
            ·
              refine ⟨28649070970013545434431045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19099380646675696956287363 28649070970013545434431045)
              ·
                refine ⟨5371700806877539768955821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28649070970013545434431045 5371700806877539768955821)
                ·
                  refine ⟨2014387802579077413358433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5371700806877539768955821 2014387802579077413358433)
                  ·
                    refine ⟨1510790851934308060018825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2014387802579077413358433 1510790851934308060018825)
                    ·
                      refine ⟨1133093138950731045014119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510790851934308060018825 1133093138950731045014119)
                      ·
                        rfl

theorem cell23_2206691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2206691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206691 prefixEnd_2206691 := by exact prefixLift 2206691
  have htrace : WordTrace (prefixWord ++ tailWord_2206691) baseStart_2206691 baseEnd_2206691 := by
    simpa [prefixWord, tailWord_2206691, baseEnd_2206691] using wordTrace_append hprefix tailTrace_2206691
  have hstable : (prefixWord ++ tailWord_2206691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206691).length < 2 ^ (prefixWord ++ tailWord_2206691).sum := by decide
  have hdescent : baseEnd_2206691 < baseStart_2206691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206702 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_2206702 : Nat := 118140960795 + 2206702 * 2 ^ 59
def prefixEnd_2206702 : Nat := 4983230072969 + 3 ^ 40 * 2206702 * 2
def baseEnd_2206702 : Nat := 1133098787237930501976569

theorem tailTrace_2206702 : CollatzResearch.WordTrace tailWord_2206702 prefixEnd_2206702 1133098787237930501976569 := by
  unfold tailWord_2206702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060629256437875442772795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53656689367668669028121573 10060629256437875442772795)
  ·
    refine ⟨15090943884656813164159193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060629256437875442772795 15090943884656813164159193)
    ·
      refine ⟨11318207913492609873119395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15090943884656813164159193 11318207913492609873119395)
      ·
        refine ⟨16977311870238914809679093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11318207913492609873119395 16977311870238914809679093)
        ·
          refine ⟨1591622987834898263407415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16977311870238914809679093 1591622987834898263407415)
          ·
            refine ⟨2387434481752347395111123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591622987834898263407415 2387434481752347395111123)
            ·
              refine ⟨3581151722628521092666685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387434481752347395111123 3581151722628521092666685)
              ·
                refine ⟨1342931895985695409750007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3581151722628521092666685 1342931895985695409750007)
                ·
                  refine ⟨2014397843978543114625011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342931895985695409750007 2014397843978543114625011)
                  ·
                    refine ⟨3021596765967814671937517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014397843978543114625011 3021596765967814671937517)
                    ·
                      refine ⟨1133098787237930501976569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021596765967814671937517 1133098787237930501976569)
                      ·
                        rfl

theorem cell23_2206702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_2206702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206702 prefixEnd_2206702 := by exact prefixLift 2206702
  have htrace : WordTrace (prefixWord ++ tailWord_2206702) baseStart_2206702 baseEnd_2206702 := by
    simpa [prefixWord, tailWord_2206702, baseEnd_2206702] using wordTrace_append hprefix tailTrace_2206702
  have hstable : (prefixWord ++ tailWord_2206702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206702).length < 2 ^ (prefixWord ++ tailWord_2206702).sum := by decide
  have hdescent : baseEnd_2206702 < baseStart_2206702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206725 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 1, 2, 2]
def baseStart_2206725 : Nat := 118140960795 + 2206725 * 2 ^ 59
def prefixEnd_2206725 : Nat := 4983230072969 + 3 ^ 40 * 2206725 * 2
def baseEnd_2206725 : Nat := 1133110597292983911988963

theorem tailTrace_2206725 : CollatzResearch.WordTrace tailWord_2206725 prefixEnd_2206725 1133110597292983911988963 := by
  unfold tailWord_2206725
  simp only [CollatzResearch.WordTrace]
  refine ⟨80485872930419678470269629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53657248620279785646846419 80485872930419678470269629)
  ·
    refine ⟨30182202348907379426351111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80485872930419678470269629 30182202348907379426351111)
    ·
      refine ⟨45273303523361069139526667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30182202348907379426351111 45273303523361069139526667)
      ·
        refine ⟨67909955285041603709290001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45273303523361069139526667 67909955285041603709290001)
        ·
          refine ⟨50932466463781202781967501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67909955285041603709290001 50932466463781202781967501)
          ·
            refine ⟨19099674923917951043237813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50932466463781202781967501 19099674923917951043237813)
            ·
              refine ⟨1790594524117307910303545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19099674923917951043237813 1790594524117307910303545)
              ·
                refine ⟨1342945893087980932727659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790594524117307910303545 1342945893087980932727659)
                ·
                  refine ⟨2014418839631971399091489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342945893087980932727659 2014418839631971399091489)
                  ·
                    refine ⟨1510814129723978549318617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2014418839631971399091489 1510814129723978549318617)
                    ·
                      refine ⟨1133110597292983911988963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510814129723978549318617 1133110597292983911988963)
                      ·
                        rfl

theorem cell23_2206725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_2206725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206725 prefixEnd_2206725 := by exact prefixLift 2206725
  have htrace : WordTrace (prefixWord ++ tailWord_2206725) baseStart_2206725 baseEnd_2206725 := by
    simpa [prefixWord, tailWord_2206725, baseEnd_2206725] using wordTrace_append hprefix tailTrace_2206725
  have hstable : (prefixWord ++ tailWord_2206725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206725).length < 2 ^ (prefixWord ++ tailWord_2206725).sum := by decide
  have hdescent : baseEnd_2206725 < baseStart_2206725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206727 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 7]
def baseStart_2206727 : Nat := 118140960795 + 2206727 * 2 ^ 59
def prefixEnd_2206727 : Nat := 4983230072969 + 3 ^ 40 * 2206727 * 2
def baseEnd_2206727 : Nat := 377703874751430968054651

theorem tailTrace_2206727 : CollatzResearch.WordTrace tailWord_2206727 prefixEnd_2206727 377703874751430968054651 := by
  unfold tailWord_2206727
  simp only [CollatzResearch.WordTrace]
  refine ⟨80485945876412432811842435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53657297250941621874561623 80485945876412432811842435)
  ·
    refine ⟨120728918814618649217763653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80485945876412432811842435 120728918814618649217763653)
    ·
      refine ⟨22636672277740996728330685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120728918814618649217763653 22636672277740996728330685)
      ·
        refine ⟨8488752104152873773124007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22636672277740996728330685 8488752104152873773124007)
        ·
          refine ⟨12733128156229310659686011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488752104152873773124007 12733128156229310659686011)
          ·
            refine ⟨19099692234343965989529017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12733128156229310659686011 19099692234343965989529017)
            ·
              refine ⟨14324769175757974492146763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19099692234343965989529017 14324769175757974492146763)
              ·
                refine ⟨21487153763636961738220145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14324769175757974492146763 21487153763636961738220145)
                ·
                  refine ⟨16115365322727721303665109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21487153763636961738220145 16115365322727721303665109)
                  ·
                    refine ⟨377703874751430968054651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16115365322727721303665109 377703874751430968054651)
                    ·
                      rfl

theorem cell23_2206727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_2206727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206727 prefixEnd_2206727 := by exact prefixLift 2206727
  have htrace : WordTrace (prefixWord ++ tailWord_2206727) baseStart_2206727 baseEnd_2206727 := by
    simpa [prefixWord, tailWord_2206727, baseEnd_2206727] using wordTrace_append hprefix tailTrace_2206727
  have hstable : (prefixWord ++ tailWord_2206727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206727).length < 2 ^ (prefixWord ++ tailWord_2206727).sum := by decide
  have hdescent : baseEnd_2206727 < baseStart_2206727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206751 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 3, 3, 2]
def baseStart_2206751 : Nat := 118140960795 + 2206751 * 2 ^ 59
def prefixEnd_2206751 : Nat := 4983230072969 + 3 ^ 40 * 2206751 * 2
def baseEnd_2206751 : Nat := 1133123947790000810263843

theorem tailTrace_2206751 : CollatzResearch.WordTrace tailWord_2206751 prefixEnd_2206751 1133123947790000810263843 := by
  unfold tailWord_2206751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80486821228325484910716107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53657880818883656607144071 80486821228325484910716107)
  ·
    refine ⟨120730231842488227366074161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80486821228325484910716107 120730231842488227366074161)
    ·
      refine ⟨90547673881866170524555621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120730231842488227366074161 90547673881866170524555621)
      ·
        refine ⟨16977688852849906973354179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90547673881866170524555621 16977688852849906973354179)
        ·
          refine ⟨25466533279274860460031269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16977688852849906973354179 25466533279274860460031269)
          ·
            refine ⟨4774974989864036336255863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25466533279274860460031269 4774974989864036336255863)
            ·
              refine ⟨7162462484796054504383795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774974989864036336255863 7162462484796054504383795)
              ·
                refine ⟨10743693727194081756575693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7162462484796054504383795 10743693727194081756575693)
                ·
                  refine ⟨4028885147697780658715885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10743693727194081756575693 4028885147697780658715885)
                  ·
                    refine ⟨1510831930386667747018457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4028885147697780658715885 1510831930386667747018457)
                    ·
                      refine ⟨1133123947790000810263843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510831930386667747018457 1133123947790000810263843)
                      ·
                        rfl

theorem cell23_2206751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_2206751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206751 prefixEnd_2206751 := by exact prefixLift 2206751
  have htrace : WordTrace (prefixWord ++ tailWord_2206751) baseStart_2206751 baseEnd_2206751 := by
    simpa [prefixWord, tailWord_2206751, baseEnd_2206751] using wordTrace_append hprefix tailTrace_2206751
  have hstable : (prefixWord ++ tailWord_2206751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206751).length < 2 ^ (prefixWord ++ tailWord_2206751).sum := by decide
  have hdescent : baseEnd_2206751 < baseStart_2206751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206768 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2]
def baseStart_2206768 : Nat := 118140960795 + 2206768 * 2 ^ 59
def prefixEnd_2206768 : Nat := 4983230072969 + 3 ^ 40 * 2206768 * 2
def baseEnd_2206768 : Nat := 1133132676961127243751265

theorem tailTrace_2206768 : CollatzResearch.WordTrace tailWord_2206768 prefixEnd_2206768 1133132676961127243751265 := by
  unfold tailWord_2206768
  simp only [CollatzResearch.WordTrace]
  refine ⟨40243720634631948407042479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53658294179509264542723305 40243720634631948407042479)
  ·
    refine ⟨60365580951947922610563719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40243720634631948407042479 60365580951947922610563719)
    ·
      refine ⟨90548371427921883915845579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60365580951947922610563719 90548371427921883915845579)
      ·
        refine ⟨135822557141882825873768369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90548371427921883915845579 135822557141882825873768369)
        ·
          refine ⟨101866917856412119405326277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135822557141882825873768369 101866917856412119405326277)
          ·
            refine ⟨19100047098077272388498677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101866917856412119405326277 19100047098077272388498677)
            ·
              refine ⟨1790629415444744286421751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19100047098077272388498677 1790629415444744286421751)
              ·
                refine ⟨2685944123167116429632627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790629415444744286421751 2685944123167116429632627)
                ·
                  refine ⟨4028916184750674644448941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685944123167116429632627 4028916184750674644448941)
                  ·
                    refine ⟨1510843569281502991668353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4028916184750674644448941 1510843569281502991668353)
                    ·
                      refine ⟨1133132676961127243751265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510843569281502991668353 1133132676961127243751265)
                      ·
                        rfl

theorem cell23_2206768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 3, 2].length) (baseStart_2206768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206768 prefixEnd_2206768 := by exact prefixLift 2206768
  have htrace : WordTrace (prefixWord ++ tailWord_2206768) baseStart_2206768 baseEnd_2206768 := by
    simpa [prefixWord, tailWord_2206768, baseEnd_2206768] using wordTrace_append hprefix tailTrace_2206768
  have hstable : (prefixWord ++ tailWord_2206768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206768).length < 2 ^ (prefixWord ++ tailWord_2206768).sum := by decide
  have hdescent : baseEnd_2206768 < baseStart_2206768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206787 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 7]
def baseStart_2206787 : Nat := 118140960795 + 2206787 * 2 ^ 59
def prefixEnd_2206787 : Nat := 4983230072969 + 3 ^ 40 * 2206787 * 2
def baseEnd_2206787 : Nat := 125904714788173629934853

theorem tailTrace_2206787 : CollatzResearch.WordTrace tailWord_2206787 prefixEnd_2206787 125904714788173629934853 := by
  unfold tailWord_2206787
  simp only [CollatzResearch.WordTrace]
  refine ⟨80488134256195063059026615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53658756170796708706017743 80488134256195063059026615)
  ·
    refine ⟨120732201384292594588539923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80488134256195063059026615 120732201384292594588539923)
    ·
      refine ⟨181098302076438891882809885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120732201384292594588539923 181098302076438891882809885)
      ·
        refine ⟨67911863278664584456053707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181098302076438891882809885 67911863278664584456053707)
        ·
          refine ⟨101867794917996876684080561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67911863278664584456053707 101867794917996876684080561)
          ·
            refine ⟨76400846188497657513060421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101867794917996876684080561 76400846188497657513060421)
            ·
              refine ⟨14325158660343310783698829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76400846188497657513060421 14325158660343310783698829)
              ·
                refine ⟨5371934497628741543887061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14325158660343310783698829 5371934497628741543887061)
                ·
                  refine ⟨125904714788173629934853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5371934497628741543887061 125904714788173629934853)
                  ·
                    rfl

theorem cell23_2206787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 7].length) (baseStart_2206787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206787 prefixEnd_2206787 := by exact prefixLift 2206787
  have htrace : WordTrace (prefixWord ++ tailWord_2206787) baseStart_2206787 baseEnd_2206787 := by
    simpa [prefixWord, tailWord_2206787, baseEnd_2206787] using wordTrace_append hprefix tailTrace_2206787
  have hstable : (prefixWord ++ tailWord_2206787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206787).length < 2 ^ (prefixWord ++ tailWord_2206787).sum := by decide
  have hdescent : baseEnd_2206787 < baseStart_2206787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206798 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_2206798 : Nat := 118140960795 + 2206798 * 2 ^ 59
def prefixEnd_2206798 : Nat := 4983230072969 + 3 ^ 40 * 2206798 * 2
def baseEnd_2206798 : Nat := 1133148081380762126376127

theorem tailTrace_2206798 : CollatzResearch.WordTrace tailWord_2206798 prefixEnd_2206798 1133148081380762126376127 := by
  unfold tailWord_2206798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061066932394401492209631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53659023639436807958451365 10061066932394401492209631)
  ·
    refine ⟨15091600398591602238314447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10061066932394401492209631 15091600398591602238314447)
    ·
      refine ⟨22637400597887403357471671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15091600398591602238314447 22637400597887403357471671)
      ·
        refine ⟨33956100896831105036207507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22637400597887403357471671 33956100896831105036207507)
        ·
          refine ⟨50934151345246657554311261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33956100896831105036207507 50934151345246657554311261)
          ·
            refine ⟨19100306754467496582866723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50934151345246657554311261 19100306754467496582866723)
            ·
              refine ⟨28650460131701244874300085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19100306754467496582866723 28650460131701244874300085)
              ·
                refine ⟨2685980637346991706965633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28650460131701244874300085 2685980637346991706965633)
                ·
                  refine ⟨2014485478010243780224225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685980637346991706965633 2014485478010243780224225)
                  ·
                    refine ⟨1510864108507682835168169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2014485478010243780224225 1510864108507682835168169)
                    ·
                      refine ⟨1133148081380762126376127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510864108507682835168169 1133148081380762126376127)
                      ·
                        rfl

theorem cell23_2206798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_2206798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206798 prefixEnd_2206798 := by exact prefixLift 2206798
  have htrace : WordTrace (prefixWord ++ tailWord_2206798) baseStart_2206798 baseEnd_2206798 := by
    simpa [prefixWord, tailWord_2206798, baseEnd_2206798] using wordTrace_append hprefix tailTrace_2206798
  have hstable : (prefixWord ++ tailWord_2206798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206798).length < 2 ^ (prefixWord ++ tailWord_2206798).sum := by decide
  have hdescent : baseEnd_2206798 < baseStart_2206798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206821 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 5]
def baseStart_2206821 : Nat := 118140960795 + 2206821 * 2 ^ 59
def prefixEnd_2206821 : Nat := 4983230072969 + 3 ^ 40 * 2206821 * 2
def baseEnd_2206821 : Nat := 125906654603979504043169

theorem tailTrace_2206821 : CollatzResearch.WordTrace tailWord_2206821 prefixEnd_2206821 125906654603979504043169 := by
  unfold tailWord_2206821
  simp only [CollatzResearch.WordTrace]
  refine ⟨80489374338071886865764317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53659582892047924577176211 80489374338071886865764317)
  ·
    refine ⟨30183515376776957574661619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80489374338071886865764317 30183515376776957574661619)
    ·
      refine ⟨45275273065165436361992429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30183515376776957574661619 45275273065165436361992429)
      ·
        refine ⟨16978227399437038635747161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45275273065165436361992429 16978227399437038635747161)
        ·
          refine ⟨12733670549577778976810371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16978227399437038635747161 12733670549577778976810371)
          ·
            refine ⟨19100505824366668465215557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12733670549577778976810371 19100505824366668465215557)
            ·
              refine ⟨3581344842068750337227917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19100505824366668465215557 3581344842068750337227917)
              ·
                refine ⟨1343004315775781376460469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3581344842068750337227917 1343004315775781376460469)
                ·
                  refine ⟨125906654603979504043169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1343004315775781376460469 125906654603979504043169)
                  ·
                    rfl

theorem cell23_2206821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_2206821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206821 prefixEnd_2206821 := by exact prefixLift 2206821
  have htrace : WordTrace (prefixWord ++ tailWord_2206821) baseStart_2206821 baseEnd_2206821 := by
    simpa [prefixWord, tailWord_2206821, baseEnd_2206821] using wordTrace_append hprefix tailTrace_2206821
  have hstable : (prefixWord ++ tailWord_2206821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206821).length < 2 ^ (prefixWord ++ tailWord_2206821).sum := by decide
  have hdescent : baseEnd_2206821 < baseStart_2206821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206834 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_2206834 : Nat := 118140960795 + 2206834 * 2 ^ 59
def prefixEnd_2206834 : Nat := 4983230072969 + 3 ^ 40 * 2206834 * 2
def baseEnd_2206834 : Nat := 377722188894774661841987

theorem tailTrace_2206834 : CollatzResearch.WordTrace tailWord_2206834 prefixEnd_2206834 377722188894774661841987 := by
  unfold tailWord_2206834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20122462121756197521496889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53659898991349860057325037 20122462121756197521496889)
  ·
    refine ⟨15091846591317148141122667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20122462121756197521496889 15091846591317148141122667)
    ·
      refine ⟨22637769886975722211684001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15091846591317148141122667 22637769886975722211684001)
      ·
        refine ⟨16978327415231791658763001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22637769886975722211684001 16978327415231791658763001)
        ·
          refine ⟨12733745561423843744072251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16978327415231791658763001 12733745561423843744072251)
          ·
            refine ⟨19100618342135765616108377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12733745561423843744072251 19100618342135765616108377)
            ·
              refine ⟨14325463756601824212081283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19100618342135765616108377 14325463756601824212081283)
              ·
                refine ⟨21488195634902736318121925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14325463756601824212081283 21488195634902736318121925)
                ·
                  refine ⟨4029036681544263059647861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21488195634902736318121925 4029036681544263059647861)
                  ·
                    refine ⟨377722188894774661841987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4029036681544263059647861 377722188894774661841987)
                    ·
                      rfl

theorem cell23_2206834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_2206834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206834 prefixEnd_2206834 := by exact prefixLift 2206834
  have htrace : WordTrace (prefixWord ++ tailWord_2206834) baseStart_2206834 baseEnd_2206834 := by
    simpa [prefixWord, tailWord_2206834, baseEnd_2206834] using wordTrace_append hprefix tailTrace_2206834
  have hstable : (prefixWord ++ tailWord_2206834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206834).length < 2 ^ (prefixWord ++ tailWord_2206834).sum := by decide
  have hdescent : baseEnd_2206834 < baseStart_2206834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206864 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_2206864 : Nat := 118140960795 + 2206864 * 2 ^ 59
def prefixEnd_2206864 : Nat := 4983230072969 + 3 ^ 40 * 2206864 * 2
def baseEnd_2206864 : Nat := 377727323701319622716941

theorem tailTrace_2206864 : CollatzResearch.WordTrace tailWord_2206864 prefixEnd_2206864 377727323701319622716941 := by
  unfold tailWord_2206864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245471338458052604789823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53660628451277403473053097 40245471338458052604789823)
  ·
    refine ⟨60368207007687078907184735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40245471338458052604789823 60368207007687078907184735)
    ·
      refine ⟨90552310511530618360777103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60368207007687078907184735 90552310511530618360777103)
      ·
        refine ⟨135828465767295927541165655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90552310511530618360777103 135828465767295927541165655)
        ·
          refine ⟨203742698650943891311748483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135828465767295927541165655 203742698650943891311748483)
          ·
            refine ⟨305614047976415836967622725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203742698650943891311748483 305614047976415836967622725)
            ·
              refine ⟨57302633995577969431429261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305614047976415836967622725 57302633995577969431429261)
              ·
                refine ⟨21488487748341738536785973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57302633995577969431429261 21488487748341738536785973)
                ·
                  refine ⟨2014545726407037987823685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21488487748341738536785973 2014545726407037987823685)
                  ·
                    refine ⟨377727323701319622716941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014545726407037987823685 377727323701319622716941)
                    ·
                      rfl

theorem cell23_2206864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_2206864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206864 prefixEnd_2206864 := by exact prefixLift 2206864
  have htrace : WordTrace (prefixWord ++ tailWord_2206864) baseStart_2206864 baseEnd_2206864 := by
    simpa [prefixWord, tailWord_2206864, baseEnd_2206864] using wordTrace_append hprefix tailTrace_2206864
  have hstable : (prefixWord ++ tailWord_2206864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206864).length < 2 ^ (prefixWord ++ tailWord_2206864).sum := by decide
  have hdescent : baseEnd_2206864 < baseStart_2206864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206898 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_2206898 : Nat := 118140960795 + 2206898 * 2 ^ 59
def prefixEnd_2206898 : Nat := 4983230072969 + 3 ^ 40 * 2206898 * 2
def baseEnd_2206898 : Nat := 377733143148737245041889

theorem tailTrace_2206898 : CollatzResearch.WordTrace tailWord_2206898 prefixEnd_2206898 377733143148737245041889 := by
  unfold tailWord_2206898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20123045689698232254079337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53661455172528619344211565 20123045689698232254079337)
  ·
    refine ⟨15092284267273674190559503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20123045689698232254079337 15092284267273674190559503)
    ·
      refine ⟨22638426400910511285839255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15092284267273674190559503 22638426400910511285839255)
      ·
        refine ⟨33957639601365766928758883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22638426400910511285839255 33957639601365766928758883)
        ·
          refine ⟨50936459402048650393138325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33957639601365766928758883 50936459402048650393138325)
          ·
            refine ⟨2387646534471030487178359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50936459402048650393138325 2387646534471030487178359)
            ·
              refine ⟨3581469801706545730767539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387646534471030487178359 3581469801706545730767539)
              ·
                refine ⟨5372204702559818596151309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581469801706545730767539 5372204702559818596151309)
                ·
                  refine ⟨2014576763459931973556741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5372204702559818596151309 2014576763459931973556741)
                  ·
                    refine ⟨377733143148737245041889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014576763459931973556741 377733143148737245041889)
                    ·
                      rfl

theorem cell23_2206898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_2206898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206898 prefixEnd_2206898 := by exact prefixLift 2206898
  have htrace : WordTrace (prefixWord ++ tailWord_2206898) baseStart_2206898 baseEnd_2206898 := by
    simpa [prefixWord, tailWord_2206898, baseEnd_2206898] using wordTrace_append hprefix tailTrace_2206898
  have hstable : (prefixWord ++ tailWord_2206898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206898).length < 2 ^ (prefixWord ++ tailWord_2206898).sum := by decide
  have hdescent : baseEnd_2206898 < baseStart_2206898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206904 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_2206904 : Nat := 118140960795 + 2206904 * 2 ^ 59
def prefixEnd_2206904 : Nat := 4983230072969 + 3 ^ 40 * 2206904 * 2
def baseEnd_2206904 : Nat := 1133202510330138711650639

theorem tailTrace_2206904 : CollatzResearch.WordTrace tailWord_2206904 prefixEnd_2206904 1133202510330138711650639 := by
  unfold tailWord_2206904
  simp only [CollatzResearch.WordTrace]
  refine ⟨40246200798385596020517883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53661601064514128027357177 40246200798385596020517883)
  ·
    refine ⟨60369301197578394030776825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40246200798385596020517883 60369301197578394030776825)
    ·
      refine ⟨45276975898183795523082619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60369301197578394030776825 45276975898183795523082619)
      ·
        refine ⟨67915463847275693284623929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45276975898183795523082619 67915463847275693284623929)
        ·
          refine ⟨50936597885456769963467947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67915463847275693284623929 50936597885456769963467947)
          ·
            refine ⟨76404896828185154945201921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50936597885456769963467947 76404896828185154945201921)
            ·
              refine ⟨57303672621138866208901441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76404896828185154945201921 57303672621138866208901441)
              ·
                refine ⟨42977754465854149656676081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57303672621138866208901441 42977754465854149656676081)
                ·
                  refine ⟨32233315849390612242507061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42977754465854149656676081 32233315849390612242507061)
                  ·
                    refine ⟨3021873360880369897735037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32233315849390612242507061 3021873360880369897735037)
                    ·
                      refine ⟨1133202510330138711650639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021873360880369897735037 1133202510330138711650639)
                      ·
                        rfl

theorem cell23_2206904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_2206904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206904 prefixEnd_2206904 := by exact prefixLift 2206904
  have htrace : WordTrace (prefixWord ++ tailWord_2206904) baseStart_2206904 baseEnd_2206904 := by
    simpa [prefixWord, tailWord_2206904, baseEnd_2206904] using wordTrace_append hprefix tailTrace_2206904
  have hstable : (prefixWord ++ tailWord_2206904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206904).length < 2 ^ (prefixWord ++ tailWord_2206904).sum := by decide
  have hdescent : baseEnd_2206904 < baseStart_2206904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206911 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 6]
def baseStart_2206911 : Nat := 118140960795 + 2206911 * 2 ^ 59
def prefixEnd_2206911 : Nat := 4983230072969 + 3 ^ 40 * 2206911 * 2
def baseEnd_2206911 : Nat := 125911789410524464918123

theorem tailTrace_2206911 : CollatzResearch.WordTrace tailWord_2206911 prefixEnd_2206911 125911789410524464918123 := by
  unfold tailWord_2206911
  simp only [CollatzResearch.WordTrace]
  refine ⟨80492656907745832236540587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53661771271830554824360391 80492656907745832236540587)
  ·
    refine ⟨120738985361618748354810881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80492656907745832236540587 120738985361618748354810881)
    ·
      refine ⟨90554239021214061266108161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120738985361618748354810881 90554239021214061266108161)
      ·
        refine ⟨67915679265910545949581121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90554239021214061266108161 67915679265910545949581121)
        ·
          refine ⟨50936759449432909462185841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67915679265910545949581121 50936759449432909462185841)
          ·
            refine ⟨38202569587074682096639381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50936759449432909462185841 38202569587074682096639381)
            ·
              refine ⟨1790745449394125723279971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38202569587074682096639381 1790745449394125723279971)
              ·
                refine ⟨2686118174091188584919957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790745449394125723279971 2686118174091188584919957)
                ·
                  refine ⟨125911789410524464918123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2686118174091188584919957 125911789410524464918123)
                  ·
                    rfl

theorem cell23_2206911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 6].length) (baseStart_2206911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206911 prefixEnd_2206911 := by exact prefixLift 2206911
  have htrace : WordTrace (prefixWord ++ tailWord_2206911) baseStart_2206911 baseEnd_2206911 := by
    simpa [prefixWord, tailWord_2206911, baseEnd_2206911] using wordTrace_append hprefix tailTrace_2206911
  have hstable : (prefixWord ++ tailWord_2206911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206911).length < 2 ^ (prefixWord ++ tailWord_2206911).sum := by decide
  have hdescent : baseEnd_2206911 < baseStart_2206911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206931 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 6, 3, 2]
def baseStart_2206931 : Nat := 118140960795 + 2206931 * 2 ^ 59
def prefixEnd_2206931 : Nat := 4983230072969 + 3 ^ 40 * 2206931 * 2
def baseEnd_2206931 : Nat := 1133216374307810106013015

theorem tailTrace_2206931 : CollatzResearch.WordTrace tailWord_2206931 prefixEnd_2206931 1133216374307810106013015 := by
  unfold tailWord_2206931
  simp only [CollatzResearch.WordTrace]
  refine ⟨80493386367673375652268647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53662257578448917101512431 80493386367673375652268647)
  ·
    refine ⟨120740079551510063478402971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80493386367673375652268647 120740079551510063478402971)
    ·
      refine ⟨181110119327265095217604457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120740079551510063478402971 181110119327265095217604457)
      ·
        refine ⟨135832589495448821413203343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181110119327265095217604457 135832589495448821413203343)
        ·
          refine ⟨203748884243173232119805015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135832589495448821413203343 203748884243173232119805015)
          ·
            refine ⟨305623326364759848179707523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203748884243173232119805015 305623326364759848179707523)
            ·
              refine ⟨458434989547139772269561285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305623326364759848179707523 458434989547139772269561285)
              ·
                refine ⟨85956560540088707300542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458434989547139772269561285 85956560540088707300542741)
                ·
                  refine ⟨4029213775316658154712941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85956560540088707300542741 4029213775316658154712941)
                  ·
                    refine ⟨1510955165743746808017353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4029213775316658154712941 1510955165743746808017353)
                    ·
                      refine ⟨1133216374307810106013015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510955165743746808017353 1133216374307810106013015)
                      ·
                        rfl

theorem cell23_2206931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3, 2].length) (baseStart_2206931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206931 prefixEnd_2206931 := by exact prefixLift 2206931
  have htrace : WordTrace (prefixWord ++ tailWord_2206931) baseStart_2206931 baseEnd_2206931 := by
    simpa [prefixWord, tailWord_2206931, baseEnd_2206931] using wordTrace_append hprefix tailTrace_2206931
  have hstable : (prefixWord ++ tailWord_2206931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206931).length < 2 ^ (prefixWord ++ tailWord_2206931).sum := by decide
  have hdescent : baseEnd_2206931 < baseStart_2206931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206948 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_2206948 : Nat := 118140960795 + 2206948 * 2 ^ 59
def prefixEnd_2206948 : Nat := 4983230072969 + 3 ^ 40 * 2206948 * 2
def baseEnd_2206948 : Nat := 1133225103478936539500437

theorem tailTrace_2206948 : CollatzResearch.WordTrace tailWord_2206948 prefixEnd_2206948 1133225103478936539500437 := by
  unfold tailWord_2206948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40247003204305893777818749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53662670939074525037091665 40247003204305893777818749)
  ·
    refine ⟨15092626201614710166682031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40247003204305893777818749 15092626201614710166682031)
    ·
      refine ⟨22638939302422065250023047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15092626201614710166682031 22638939302422065250023047)
      ·
        refine ⟨33958408953633097875034571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22638939302422065250023047 33958408953633097875034571)
        ·
          refine ⟨50937613430449646812551857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33958408953633097875034571 50937613430449646812551857)
          ·
            refine ⟨38203210072837235109413893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50937613430449646812551857 38203210072837235109413893)
            ·
              refine ⟨7163101888656981583015105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38203210072837235109413893 7163101888656981583015105)
              ·
                refine ⟨5372326416492736187261329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163101888656981583015105 5372326416492736187261329)
                ·
                  refine ⟨4029244812369552140445997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372326416492736187261329 4029244812369552140445997)
                  ·
                    refine ⟨1510966804638582052667249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4029244812369552140445997 1510966804638582052667249)
                    ·
                      refine ⟨1133225103478936539500437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510966804638582052667249 1133225103478936539500437)
                      ·
                        rfl

theorem cell23_2206948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_2206948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206948 prefixEnd_2206948 := by exact prefixLift 2206948
  have htrace : WordTrace (prefixWord ++ tailWord_2206948) baseStart_2206948 baseEnd_2206948 := by
    simpa [prefixWord, tailWord_2206948, baseEnd_2206948] using wordTrace_append hprefix tailTrace_2206948
  have hstable : (prefixWord ++ tailWord_2206948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206948).length < 2 ^ (prefixWord ++ tailWord_2206948).sum := by decide
  have hdescent : baseEnd_2206948 < baseStart_2206948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206949 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_2206949 : Nat := 118140960795 + 2206949 * 2 ^ 59
def prefixEnd_2206949 : Nat := 4983230072969 + 3 ^ 40 * 2206949 * 2
def baseEnd_2206949 : Nat := 377741872319863678529311

theorem tailTrace_2206949 : CollatzResearch.WordTrace tailWord_2206949 prefixEnd_2206949 377741872319863678529311 := by
  unfold tailWord_2206949
  simp only [CollatzResearch.WordTrace]
  refine ⟨80494042881608164726423901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53662695254405443150949267 80494042881608164726423901)
  ·
    refine ⟨30185266080603061772408963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80494042881608164726423901 30185266080603061772408963)
    ·
      refine ⟨45277899120904592658613445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30185266080603061772408963 45277899120904592658613445)
      ·
        refine ⟨8489606085169611123490021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45277899120904592658613445 8489606085169611123490021)
        ·
          refine ⟨1591801140969302085654379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8489606085169611123490021 1591801140969302085654379)
          ·
            refine ⟨2387701711453953128481569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591801140969302085654379 2387701711453953128481569)
            ·
              refine ⟨1790776283590464846361177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387701711453953128481569 1790776283590464846361177)
              ·
                refine ⟨1343082212692848634770883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790776283590464846361177 1343082212692848634770883)
                ·
                  refine ⟨2014623319039272952156325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343082212692848634770883 2014623319039272952156325)
                  ·
                    refine ⟨377741872319863678529311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014623319039272952156325 377741872319863678529311)
                    ·
                      rfl

theorem cell23_2206949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_2206949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206949 prefixEnd_2206949 := by exact prefixLift 2206949
  have htrace : WordTrace (prefixWord ++ tailWord_2206949) baseStart_2206949 baseEnd_2206949 := by
    simpa [prefixWord, tailWord_2206949, baseEnd_2206949] using wordTrace_append hprefix tailTrace_2206949
  have hstable : (prefixWord ++ tailWord_2206949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206949).length < 2 ^ (prefixWord ++ tailWord_2206949).sum := by decide
  have hdescent : baseEnd_2206949 < baseStart_2206949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206955 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 1, 1, 3]
def baseStart_2206955 : Nat := 118140960795 + 2206955 * 2 ^ 59
def prefixEnd_2206955 : Nat := 4983230072969 + 3 ^ 40 * 2206955 * 2
def baseEnd_2206955 : Nat := 1133228697843518012112905

theorem tailTrace_2206955 : CollatzResearch.WordTrace tailWord_2206955 prefixEnd_2206955 1133228697843518012112905 := by
  unfold tailWord_2206955
  simp only [CollatzResearch.WordTrace]
  refine ⟨80494261719586427751142319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53662841146390951834094879 80494261719586427751142319)
  ·
    refine ⟨120741392579379641626713479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80494261719586427751142319 120741392579379641626713479)
    ·
      refine ⟨181112088869069462440070219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120741392579379641626713479 181112088869069462440070219)
      ·
        refine ⟨271668133303604193660105329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181112088869069462440070219 271668133303604193660105329)
        ·
          refine ⟨203751099977703145245078997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271668133303604193660105329 203751099977703145245078997)
          ·
            refine ⟨4775416405727417466681539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 203751099977703145245078997 4775416405727417466681539)
            ·
              refine ⟨7163124608591126200022309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775416405727417466681539 7163124608591126200022309)
              ·
                refine ⟨1343085864110836162504183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7163124608591126200022309 1343085864110836162504183)
                ·
                  refine ⟨2014628796166254243756275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343085864110836162504183 2014628796166254243756275)
                  ·
                    refine ⟨3021943194249381365634413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014628796166254243756275 3021943194249381365634413)
                    ·
                      refine ⟨1133228697843518012112905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021943194249381365634413 1133228697843518012112905)
                      ·
                        rfl

theorem cell23_2206955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 1, 3].length) (baseStart_2206955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206955 prefixEnd_2206955 := by exact prefixLift 2206955
  have htrace : WordTrace (prefixWord ++ tailWord_2206955) baseStart_2206955 baseEnd_2206955 := by
    simpa [prefixWord, tailWord_2206955, baseEnd_2206955] using wordTrace_append hprefix tailTrace_2206955
  have hstable : (prefixWord ++ tailWord_2206955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206955).length < 2 ^ (prefixWord ++ tailWord_2206955).sum := by decide
  have hdescent : baseEnd_2206955 < baseStart_2206955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206961 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_2206961 : Nat := 118140960795 + 2206961 * 2 ^ 59
def prefixEnd_2206961 : Nat := 4983230072969 + 3 ^ 40 * 2206961 * 2
def baseEnd_2206961 : Nat := 1133231778727444988637877

theorem tailTrace_2206961 : CollatzResearch.WordTrace tailWord_2206961 prefixEnd_2206961 1133231778727444988637877 := by
  unfold tailWord_2206961
  simp only [CollatzResearch.WordTrace]
  refine ⟨80494480557564690775860737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53662987038376460517240491 80494480557564690775860737)
  ·
    refine ⟨60370860418173518081895553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80494480557564690775860737 60370860418173518081895553)
    ·
      refine ⟨45278145313630138561421665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60370860418173518081895553 45278145313630138561421665)
      ·
        refine ⟨33958608985222603921066249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45278145313630138561421665 33958608985222603921066249)
        ·
          refine ⟨25468956738916952940799687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33958608985222603921066249 25468956738916952940799687)
          ·
            refine ⟨38203435108375429411199531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25468956738916952940799687 38203435108375429411199531)
            ·
              refine ⟨57305152662563144116799297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38203435108375429411199531 57305152662563144116799297)
              ·
                refine ⟨42978864496922358087599473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57305152662563144116799297 42978864496922358087599473)
                ·
                  refine ⟨32234148372691768565699605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42978864496922358087599473 32234148372691768565699605)
                  ·
                    refine ⟨1510975704969926651517169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32234148372691768565699605 1510975704969926651517169)
                    ·
                      refine ⟨1133231778727444988637877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1510975704969926651517169 1133231778727444988637877)
                      ·
                        rfl

theorem cell23_2206961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_2206961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206961 prefixEnd_2206961 := by exact prefixLift 2206961
  have htrace : WordTrace (prefixWord ++ tailWord_2206961) baseStart_2206961 baseEnd_2206961 := by
    simpa [prefixWord, tailWord_2206961, baseEnd_2206961] using wordTrace_append hprefix tailTrace_2206961
  have hstable : (prefixWord ++ tailWord_2206961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206961).length < 2 ^ (prefixWord ++ tailWord_2206961).sum := by decide
  have hdescent : baseEnd_2206961 < baseStart_2206961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206981 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_2206981 : Nat := 118140960795 + 2206981 * 2 ^ 59
def prefixEnd_2206981 : Nat := 4983230072969 + 3 ^ 40 * 2206981 * 2
def baseEnd_2206981 : Nat := 1133242048340534910387785

theorem tailTrace_2206981 : CollatzResearch.WordTrace tailWord_2206981 prefixEnd_2206981 1133242048340534910387785 := by
  unfold tailWord_2206981
  simp only [CollatzResearch.WordTrace]
  refine ⟨80495210017492234191588797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53663473344994822794392531 80495210017492234191588797)
  ·
    refine ⟨30185703756559587821845799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80495210017492234191588797 30185703756559587821845799)
    ·
      refine ⟨45278555634839381732768699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30185703756559587821845799 45278555634839381732768699)
      ·
        refine ⟨67917833452259072599153049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45278555634839381732768699 67917833452259072599153049)
        ·
          refine ⟨50938375089194304449364787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67917833452259072599153049 50938375089194304449364787)
          ·
            refine ⟨76407562633791456674047181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50938375089194304449364787 76407562633791456674047181)
            ·
              refine ⟨28652835987671796252767693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76407562633791456674047181 28652835987671796252767693)
              ·
                refine ⟨10744813495376923594787885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28652835987671796252767693 10744813495376923594787885)
                ·
                  refine ⟨4029305060766346348045457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10744813495376923594787885 4029305060766346348045457)
                  ·
                    refine ⟨3021978795574759761034093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029305060766346348045457 3021978795574759761034093)
                    ·
                      refine ⟨1133242048340534910387785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3021978795574759761034093 1133242048340534910387785)
                      ·
                        rfl

theorem cell23_2206981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_2206981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2206981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2206981 prefixEnd_2206981 := by exact prefixLift 2206981
  have htrace : WordTrace (prefixWord ++ tailWord_2206981) baseStart_2206981 baseEnd_2206981 := by
    simpa [prefixWord, tailWord_2206981, baseEnd_2206981] using wordTrace_append hprefix tailTrace_2206981
  have hstable : (prefixWord ++ tailWord_2206981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206981).length < 2 ^ (prefixWord ++ tailWord_2206981).sum := by decide
  have hdescent : baseEnd_2206981 < baseStart_2206981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207005 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2207005 : Nat := 118140960795 + 2207005 * 2 ^ 59
def prefixEnd_2207005 : Nat := 4983230072969 + 3 ^ 40 * 2207005 * 2
def baseEnd_2207005 : Nat := 377751457292080938829225

theorem tailTrace_2207005 : CollatzResearch.WordTrace tailWord_2207005 prefixEnd_2207005 377751457292080938829225 := by
  unfold tailWord_2207005
  simp only [CollatzResearch.WordTrace]
  refine ⟨80496085369405286290462469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53664056912936857526974979 80496085369405286290462469)
  ·
    refine ⟨15093016006763491179461713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80496085369405286290462469 15093016006763491179461713)
    ·
      refine ⟨11319762005072618384596285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15093016006763491179461713 11319762005072618384596285)
      ·
        refine ⟨4244910751902231894223607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11319762005072618384596285 4244910751902231894223607)
        ·
          refine ⟨6367366127853347841335411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244910751902231894223607 6367366127853347841335411)
          ·
            refine ⟨9551049191780021762003117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367366127853347841335411 9551049191780021762003117)
            ·
              refine ⟨3581643446917508160751169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9551049191780021762003117 3581643446917508160751169)
              ·
                refine ⟨2686232585188131120563377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581643446917508160751169 2686232585188131120563377)
                ·
                  refine ⟨2014674438891098340422533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686232585188131120563377 2014674438891098340422533)
                  ·
                    refine ⟨377751457292080938829225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014674438891098340422533 377751457292080938829225)
                    ·
                      rfl

theorem cell23_2207005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2207005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207005 prefixEnd_2207005 := by exact prefixLift 2207005
  have htrace : WordTrace (prefixWord ++ tailWord_2207005) baseStart_2207005 baseEnd_2207005 := by
    simpa [prefixWord, tailWord_2207005, baseEnd_2207005] using wordTrace_append hprefix tailTrace_2207005
  have hstable : (prefixWord ++ tailWord_2207005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207005).length < 2 ^ (prefixWord ++ tailWord_2207005).sum := by decide
  have hdescent : baseEnd_2207005 < baseStart_2207005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207012 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_2207012 : Nat := 118140960795 + 2207012 * 2 ^ 59
def prefixEnd_2207012 : Nat := 4983230072969 + 3 ^ 40 * 2207012 * 2
def baseEnd_2207012 : Nat := 1133257966240824289100143

theorem tailTrace_2207012 : CollatzResearch.WordTrace tailWord_2207012 prefixEnd_2207012 1133257966240824289100143 := by
  unfold tailWord_2207012
  simp only [CollatzResearch.WordTrace]
  refine ⟨40248170340189963242983645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53664227120253284323978193 40248170340189963242983645)
  ·
    refine ⟨15093063877571236216118867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40248170340189963242983645 15093063877571236216118867)
    ·
      refine ⟨22639595816356854324178301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15093063877571236216118867 22639595816356854324178301)
      ·
        refine ⟨8489848431133820371566863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22639595816356854324178301 8489848431133820371566863)
        ·
          refine ⟨12734772646700730557350295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8489848431133820371566863 12734772646700730557350295)
          ·
            refine ⟨19102158970051095836025443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12734772646700730557350295 19102158970051095836025443)
            ·
              refine ⟨28653238455076643754038165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19102158970051095836025443 28653238455076643754038165)
              ·
                refine ⟨1343120552581717675970539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28653238455076643754038165 1343120552581717675970539)
                ·
                  refine ⟨2014680828872576513955809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343120552581717675970539 2014680828872576513955809)
                  ·
                    refine ⟨1511010621654432385466857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2014680828872576513955809 1511010621654432385466857)
                    ·
                      refine ⟨1133257966240824289100143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511010621654432385466857 1133257966240824289100143)
                      ·
                        rfl

theorem cell23_2207012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_2207012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207012 prefixEnd_2207012 := by exact prefixLift 2207012
  have htrace : WordTrace (prefixWord ++ tailWord_2207012) baseStart_2207012 baseEnd_2207012 := by
    simpa [prefixWord, tailWord_2207012, baseEnd_2207012] using wordTrace_append hprefix tailTrace_2207012
  have hstable : (prefixWord ++ tailWord_2207012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207012).length < 2 ^ (prefixWord ++ tailWord_2207012).sum := by decide
  have hdescent : baseEnd_2207012 < baseStart_2207012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207071 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2207071 : Nat := 118140960795 + 2207071 * 2 ^ 59
def prefixEnd_2207071 : Nat := 4983230072969 + 3 ^ 40 * 2207071 * 2
def baseEnd_2207071 : Nat := 1133288261599439558262371

theorem tailTrace_2207071 : CollatzResearch.WordTrace tailWord_2207071 prefixEnd_2207071 1133288261599439558262371 := by
  unfold tailWord_2207071
  simp only [CollatzResearch.WordTrace]
  refine ⟨80498492587166179562365067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53665661724777453041576711 80498492587166179562365067)
  ·
    refine ⟨120747738880749269343547601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80498492587166179562365067 120747738880749269343547601)
    ·
      refine ⟨90560804160561952007660701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120747738880749269343547601 90560804160561952007660701)
      ·
        refine ⟨33960301560210732002872763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90560804160561952007660701 33960301560210732002872763)
        ·
          refine ⟨50940452340316098004309145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33960301560210732002872763 50940452340316098004309145)
          ·
            refine ⟨38205339255237073503231859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50940452340316098004309145 38205339255237073503231859)
            ·
              refine ⟨57308008882855610254847789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38205339255237073503231859 57308008882855610254847789)
              ·
                refine ⟨21490503331070853845567921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57308008882855610254847789 21490503331070853845567921)
                ·
                  refine ⟨16117877498303140384175941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21490503331070853845567921 16117877498303140384175941)
                  ·
                    refine ⟨3022102030931838822032989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16117877498303140384175941 3022102030931838822032989)
                    ·
                      refine ⟨1133288261599439558262371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022102030931838822032989 1133288261599439558262371)
                      ·
                        rfl

theorem cell23_2207071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2207071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207071 prefixEnd_2207071 := by exact prefixLift 2207071
  have htrace : WordTrace (prefixWord ++ tailWord_2207071) baseStart_2207071 baseEnd_2207071 := by
    simpa [prefixWord, tailWord_2207071, baseEnd_2207071] using wordTrace_append hprefix tailTrace_2207071
  have hstable : (prefixWord ++ tailWord_2207071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207071).length < 2 ^ (prefixWord ++ tailWord_2207071).sum := by decide
  have hdescent : baseEnd_2207071 < baseStart_2207071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207079 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_2207079 : Nat := 118140960795 + 2207079 * 2 ^ 59
def prefixEnd_2207079 : Nat := 4983230072969 + 3 ^ 40 * 2207079 * 2
def baseEnd_2207079 : Nat := 1133292369444675526962335

theorem tailTrace_2207079 : CollatzResearch.WordTrace tailWord_2207079 prefixEnd_2207079 1133292369444675526962335 := by
  unfold tailWord_2207079
  simp only [CollatzResearch.WordTrace]
  refine ⟨80498784371137196928656291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53665856247424797952437527 80498784371137196928656291)
  ·
    refine ⟨120748176556705795392984437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80498784371137196928656291 120748176556705795392984437)
    ·
      refine ⟨11320141552191168318092291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120748176556705795392984437 11320141552191168318092291)
      ·
        refine ⟨16980212328286752477138437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11320141552191168318092291 16980212328286752477138437)
        ·
          refine ⟨3183789811553766089463457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16980212328286752477138437 3183789811553766089463457)
          ·
            refine ⟨2387842358665324567097593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3183789811553766089463457 2387842358665324567097593)
            ·
              refine ⟨1790881768998993425323195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387842358665324567097593 1790881768998993425323195)
              ·
                refine ⟨2686322653498490137984793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790881768998993425323195 2686322653498490137984793)
                ·
                  refine ⟨2014741990123867603488595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686322653498490137984793 2014741990123867603488595)
                  ·
                    refine ⟨3022112985185801405232893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014741990123867603488595 3022112985185801405232893)
                    ·
                      refine ⟨1133292369444675526962335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022112985185801405232893 1133292369444675526962335)
                      ·
                        rfl

theorem cell23_2207079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_2207079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207079 prefixEnd_2207079 := by exact prefixLift 2207079
  have htrace : WordTrace (prefixWord ++ tailWord_2207079) baseStart_2207079 baseEnd_2207079 := by
    simpa [prefixWord, tailWord_2207079, baseEnd_2207079] using wordTrace_append hprefix tailTrace_2207079
  have hstable : (prefixWord ++ tailWord_2207079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207079).length < 2 ^ (prefixWord ++ tailWord_2207079).sum := by decide
  have hdescent : baseEnd_2207079 < baseStart_2207079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207106 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2207106 : Nat := 118140960795 + 2207106 * 2 ^ 59
def prefixEnd_2207106 : Nat := 4983230072969 + 3 ^ 40 * 2207106 * 2
def baseEnd_2207106 : Nat := 1133306233422346921324711

theorem tailTrace_2207106 : CollatzResearch.WordTrace tailWord_2207106 prefixEnd_2207106 1133306233422346921324711 := by
  unfold tailWord_2207106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124942285509845134972293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53666512761359587026592781 20124942285509845134972293)
  ·
    refine ⟨3773426678533095962807305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20124942285509845134972293 3773426678533095962807305)
    ·
      refine ⟨2830070008899821972105479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3773426678533095962807305 2830070008899821972105479)
      ·
        refine ⟨4245105013349732958158219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830070008899821972105479 4245105013349732958158219)
        ·
          refine ⟨6367657520024599437237329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245105013349732958158219 6367657520024599437237329)
          ·
            refine ⟨4775743140018449577927997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6367657520024599437237329 4775743140018449577927997)
            ·
              refine ⟨1790903677506918591722999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4775743140018449577927997 1790903677506918591722999)
              ·
                refine ⟨2686355516260377887584499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790903677506918591722999 2686355516260377887584499)
                ·
                  refine ⟨4029533274390566831376749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686355516260377887584499 4029533274390566831376749)
                  ·
                    refine ⟨1511074977896462561766281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4029533274390566831376749 1511074977896462561766281)
                    ·
                      refine ⟨1133306233422346921324711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511074977896462561766281 1133306233422346921324711)
                      ·
                        rfl

theorem cell23_2207106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2207106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207106 prefixEnd_2207106 := by exact prefixLift 2207106
  have htrace : WordTrace (prefixWord ++ tailWord_2207106) baseStart_2207106 baseEnd_2207106 := by
    simpa [prefixWord, tailWord_2207106, baseEnd_2207106] using wordTrace_append hprefix tailTrace_2207106
  have hstable : (prefixWord ++ tailWord_2207106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207106).length < 2 ^ (prefixWord ++ tailWord_2207106).sum := by decide
  have hdescent : baseEnd_2207106 < baseStart_2207106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207125 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 5]
def baseStart_2207125 : Nat := 118140960795 + 2207125 * 2 ^ 59
def prefixEnd_2207125 : Nat := 4983230072969 + 3 ^ 40 * 2207125 * 2
def baseEnd_2207125 : Nat := 125923998839420260776347

theorem tailTrace_2207125 : CollatzResearch.WordTrace tailWord_2207125 prefixEnd_2207125 125923998839420260776347 := by
  unfold tailWord_2207125
  simp only [CollatzResearch.WordTrace]
  refine ⟨80500462128970546784830829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53666974752647031189887219 80500462128970546784830829)
  ·
    refine ⟨30187673298363955044311561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80500462128970546784830829 30187673298363955044311561)
    ·
      refine ⟨22640754973772966283233671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30187673298363955044311561 22640754973772966283233671)
      ·
        refine ⟨33961132460659449424850507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22640754973772966283233671 33961132460659449424850507)
        ·
          refine ⟨50941698690989174137275761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33961132460659449424850507 50941698690989174137275761)
          ·
            refine ⟨38206274018241880602956821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50941698690989174137275761 38206274018241880602956821)
            ·
              refine ⟨1790919094605088153263601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38206274018241880602956821 1790919094605088153263601)
              ·
                refine ⟨1343189320953816114947701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790919094605088153263601 1343189320953816114947701)
                ·
                  refine ⟨125923998839420260776347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1343189320953816114947701 125923998839420260776347)
                  ·
                    rfl

theorem cell23_2207125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_2207125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207125 prefixEnd_2207125 := by exact prefixLift 2207125
  have htrace : WordTrace (prefixWord ++ tailWord_2207125) baseStart_2207125 baseEnd_2207125 := by
    simpa [prefixWord, tailWord_2207125, baseEnd_2207125] using wordTrace_append hprefix tailTrace_2207125
  have hstable : (prefixWord ++ tailWord_2207125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207125).length < 2 ^ (prefixWord ++ tailWord_2207125).sum := by decide
  have hdescent : baseEnd_2207125 < baseStart_2207125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207171 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_2207171 : Nat := 118140960795 + 2207171 * 2 ^ 59
def prefixEnd_2207171 : Nat := 4983230072969 + 3 ^ 40 * 2207171 * 2
def baseEnd_2207171 : Nat := 1133339609664889167011911

theorem tailTrace_2207171 : CollatzResearch.WordTrace tailWord_2207171 prefixEnd_2207171 1133339609664889167011911 := by
  unfold tailWord_2207171
  simp only [CollatzResearch.WordTrace]
  refine ⟨80502139886803896641005367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53668093257869264427336911 80502139886803896641005367)
  ·
    refine ⟨120753209830205844961508051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80502139886803896641005367 120753209830205844961508051)
    ·
      refine ⟨181129814745308767442262077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120753209830205844961508051 181129814745308767442262077)
      ·
        refine ⟨67923680529490787790848279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181129814745308767442262077 67923680529490787790848279)
        ·
          refine ⟨101885520794236181686272419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67923680529490787790848279 101885520794236181686272419)
          ·
            refine ⟨152828281191354272529408629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101885520794236181686272419 152828281191354272529408629)
            ·
              refine ⟨14327651361689463049632059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152828281191354272529408629 14327651361689463049632059)
              ·
                refine ⟨21491477042534194574448089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14327651361689463049632059 21491477042534194574448089)
                ·
                  refine ⟨16118607781900645930836067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21491477042534194574448089 16118607781900645930836067)
                  ·
                    refine ⟨24177911672850968896254101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16118607781900645930836067 24177911672850968896254101)
                    ·
                      refine ⟨1133339609664889167011911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24177911672850968896254101 1133339609664889167011911)
                      ·
                        rfl

theorem cell23_2207171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_2207171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207171 prefixEnd_2207171 := by exact prefixLift 2207171
  have htrace : WordTrace (prefixWord ++ tailWord_2207171) baseStart_2207171 baseEnd_2207171 := by
    simpa [prefixWord, tailWord_2207171, baseEnd_2207171] using wordTrace_append hprefix tailTrace_2207171
  have hstable : (prefixWord ++ tailWord_2207171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207171).length < 2 ^ (prefixWord ++ tailWord_2207171).sum := by decide
  have hdescent : baseEnd_2207171 < baseStart_2207171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207208 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2207208 : Nat := 118140960795 + 2207208 * 2 ^ 59
def prefixEnd_2207208 : Nat := 4983230072969 + 3 ^ 40 * 2207208 * 2
def baseEnd_2207208 : Nat := 1133358608449105522249241

theorem tailTrace_2207208 : CollatzResearch.WordTrace tailWord_2207208 prefixEnd_2207208 1133358608449105522249241 := by
  unfold tailWord_2207208
  simp only [CollatzResearch.WordTrace]
  refine ⟨40251744693834925980051139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53668992925113234640068185 40251744693834925980051139)
  ·
    refine ⟨60377617040752388970076709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40251744693834925980051139 60377617040752388970076709)
    ·
      refine ⟨11320803195141072931889383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60377617040752388970076709 11320803195141072931889383)
      ·
        refine ⟨16981204792711609397834075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11320803195141072931889383 16981204792711609397834075)
        ·
          refine ⟨25471807189067414096751113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16981204792711609397834075 25471807189067414096751113)
          ·
            refine ⟨19103855391800560572563335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25471807189067414096751113 19103855391800560572563335)
            ·
              refine ⟨28655783087700840858845003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19103855391800560572563335 28655783087700840858845003)
              ·
                refine ⟨42983674631551261288267505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28655783087700840858845003 42983674631551261288267505)
                ·
                  refine ⟨32237755973663445966200629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42983674631551261288267505 32237755973663445966200629)
                  ·
                    refine ⟨3022289622530948059331309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32237755973663445966200629 3022289622530948059331309)
                    ·
                      refine ⟨1133358608449105522249241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022289622530948059331309 1133358608449105522249241)
                      ·
                        rfl

theorem cell23_2207208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2207208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207208 prefixEnd_2207208 := by exact prefixLift 2207208
  have htrace : WordTrace (prefixWord ++ tailWord_2207208) baseStart_2207208 baseEnd_2207208 := by
    simpa [prefixWord, tailWord_2207208, baseEnd_2207208] using wordTrace_append hprefix tailTrace_2207208
  have hstable : (prefixWord ++ tailWord_2207208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207208).length < 2 ^ (prefixWord ++ tailWord_2207208).sum := by decide
  have hdescent : baseEnd_2207208 < baseStart_2207208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207236 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_2207236 : Nat := 118140960795 + 2207236 * 2 ^ 59
def prefixEnd_2207236 : Nat := 4983230072969 + 3 ^ 40 * 2207236 * 2
def baseEnd_2207236 : Nat := 377790995302477137566371

theorem tailTrace_2207236 : CollatzResearch.WordTrace tailWord_2207236 prefixEnd_2207236 377790995302477137566371 := by
  unfold tailWord_2207236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40252255315784206371060781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53669673754378941828081041 40252255315784206371060781)
  ·
    refine ⟨15094595743419077389147793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40252255315784206371060781 15094595743419077389147793)
    ·
      refine ⟨11320946807564308041860845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15094595743419077389147793 11320946807564308041860845)
      ·
        refine ⟨4245355052836615515697817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11320946807564308041860845 4245355052836615515697817)
        ·
          refine ⟨3184016289627461636773363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4245355052836615515697817 3184016289627461636773363)
          ·
            refine ⟨4776024434441192455160045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184016289627461636773363 4776024434441192455160045)
            ·
              refine ⟨1791009162915447170685017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4776024434441192455160045 1791009162915447170685017)
              ·
                refine ⟨1343256872186585378013763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791009162915447170685017 1343256872186585378013763)
                ·
                  refine ⟨2014885308279878067020645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343256872186585378013763 2014885308279878067020645)
                  ·
                    refine ⟨377790995302477137566371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014885308279878067020645 377790995302477137566371)
                    ·
                      rfl

theorem cell23_2207236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_2207236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207236 prefixEnd_2207236 := by exact prefixLift 2207236
  have htrace : WordTrace (prefixWord ++ tailWord_2207236) baseStart_2207236 baseEnd_2207236 := by
    simpa [prefixWord, tailWord_2207236, baseEnd_2207236] using wordTrace_append hprefix tailTrace_2207236
  have hstable : (prefixWord ++ tailWord_2207236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207236).length < 2 ^ (prefixWord ++ tailWord_2207236).sum := by decide
  have hdescent : baseEnd_2207236 < baseStart_2207236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207242 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2207242 : Nat := 118140960795 + 2207242 * 2 ^ 59
def prefixEnd_2207242 : Nat := 4983230072969 + 3 ^ 40 * 2207242 * 2
def baseEnd_2207242 : Nat := 1133376066791358389224085

theorem tailTrace_2207242 : CollatzResearch.WordTrace tailWord_2207242 prefixEnd_2207242 1133376066791358389224085 := by
  unfold tailWord_2207242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126182367386668941709995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53669819646364450511226653 20126182367386668941709995)
  ·
    refine ⟨30189273551080003412564993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20126182367386668941709995 30189273551080003412564993)
    ·
      refine ⟨22641955163310002559423745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30189273551080003412564993 22641955163310002559423745)
      ·
        refine ⟨16981466372482501919567809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22641955163310002559423745 16981466372482501919567809)
        ·
          refine ⟨12736099779361876439675857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16981466372482501919567809 12736099779361876439675857)
          ·
            refine ⟨9552074834521407329756893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12736099779361876439675857 9552074834521407329756893)
            ·
              refine ⟨3582028062945527748658835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9552074834521407329756893 3582028062945527748658835)
              ·
                refine ⟨5373042094418291622988253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582028062945527748658835 5373042094418291622988253)
                ·
                  refine ⟨2014890785406859358620595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5373042094418291622988253 2014890785406859358620595)
                  ·
                    refine ⟨3022336178110289037930893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014890785406859358620595 3022336178110289037930893)
                    ·
                      refine ⟨1133376066791358389224085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022336178110289037930893 1133376066791358389224085)
                      ·
                        rfl

theorem cell23_2207242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2207242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207242 prefixEnd_2207242 := by exact prefixLift 2207242
  have htrace : WordTrace (prefixWord ++ tailWord_2207242) baseStart_2207242 baseEnd_2207242 := by
    simpa [prefixWord, tailWord_2207242, baseEnd_2207242] using wordTrace_append hprefix tailTrace_2207242
  have hstable : (prefixWord ++ tailWord_2207242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207242).length < 2 ^ (prefixWord ++ tailWord_2207242).sum := by decide
  have hdescent : baseEnd_2207242 < baseStart_2207242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207258 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_2207258 : Nat := 118140960795 + 2207258 * 2 ^ 59
def prefixEnd_2207258 : Nat := 4983230072969 + 3 ^ 40 * 2207258 * 2
def baseEnd_2207258 : Nat := 377794760827276775541337

theorem tailTrace_2207258 : CollatzResearch.WordTrace tailWord_2207258 prefixEnd_2207258 377794760827276775541337 := by
  unfold tailWord_2207258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126328259372177624855607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53670208691659140332948285 20126328259372177624855607)
  ·
    refine ⟨30189492389058266437283411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20126328259372177624855607 30189492389058266437283411)
    ·
      refine ⟨45284238583587399655925117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30189492389058266437283411 45284238583587399655925117)
      ·
        refine ⟨16981589468845274870971919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45284238583587399655925117 16981589468845274870971919)
        ·
          refine ⟨25472384203267912306457879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16981589468845274870971919 25472384203267912306457879)
          ·
            refine ⟨38208576304901868459686819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25472384203267912306457879 38208576304901868459686819)
            ·
              refine ⟨57312864457352802689530229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38208576304901868459686819 57312864457352802689530229)
              ·
                refine ⟨5373081042876825252143459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57312864457352802689530229 5373081042876825252143459)
                ·
                  refine ⟨8059621564315237878215189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373081042876825252143459 8059621564315237878215189)
                  ·
                    refine ⟨377794760827276775541337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8059621564315237878215189 377794760827276775541337)
                    ·
                      rfl

theorem cell23_2207258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_2207258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207258 prefixEnd_2207258 := by exact prefixLift 2207258
  have htrace : WordTrace (prefixWord ++ tailWord_2207258) baseStart_2207258 baseEnd_2207258 := by
    simpa [prefixWord, tailWord_2207258, baseEnd_2207258] using wordTrace_append hprefix tailTrace_2207258
  have hstable : (prefixWord ++ tailWord_2207258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207258).length < 2 ^ (prefixWord ++ tailWord_2207258).sum := by decide
  have hdescent : baseEnd_2207258 < baseStart_2207258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207265 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2207265 : Nat := 118140960795 + 2207265 * 2 ^ 59
def prefixEnd_2207265 : Nat := 4983230072969 + 3 ^ 40 * 2207265 * 2
def baseEnd_2207265 : Nat := 1133387876846411799236479

theorem tailTrace_2207265 : CollatzResearch.WordTrace tailWord_2207265 prefixEnd_2207265 1133387876846411799236479 := by
  unfold tailWord_2207265
  simp only [CollatzResearch.WordTrace]
  refine ⟨80505568348463350694927249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53670378898975567129951499 80505568348463350694927249)
  ·
    refine ⟨60379176261347513021195437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80505568348463350694927249 60379176261347513021195437)
    ·
      refine ⟨22642191098005317382948289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60379176261347513021195437 22642191098005317382948289)
      ·
        refine ⟨16981643323503988037211217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22642191098005317382948289 16981643323503988037211217)
        ·
          refine ⟨12736232492627991027908413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16981643323503988037211217 12736232492627991027908413)
          ·
            refine ⟨4776087184735496635465655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12736232492627991027908413 4776087184735496635465655)
            ·
              refine ⟨7164130777103244953198483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776087184735496635465655 7164130777103244953198483)
              ·
                refine ⟨10746196165654867429797725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7164130777103244953198483 10746196165654867429797725)
                ·
                  refine ⟨4029823562120575286174147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10746196165654867429797725 4029823562120575286174147)
                  ·
                    refine ⟨6044735343180862929261221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029823562120575286174147 6044735343180862929261221)
                    ·
                      refine ⟨1133387876846411799236479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6044735343180862929261221 1133387876846411799236479)
                      ·
                        rfl

theorem cell23_2207265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2207265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207265 prefixEnd_2207265 := by exact prefixLift 2207265
  have htrace : WordTrace (prefixWord ++ tailWord_2207265) baseStart_2207265 baseEnd_2207265 := by
    simpa [prefixWord, tailWord_2207265, baseEnd_2207265] using wordTrace_append hprefix tailTrace_2207265
  have hstable : (prefixWord ++ tailWord_2207265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207265).length < 2 ^ (prefixWord ++ tailWord_2207265).sum := by decide
  have hdescent : baseEnd_2207265 < baseStart_2207265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207285 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2207285 : Nat := 118140960795 + 2207285 * 2 ^ 59
def prefixEnd_2207285 : Nat := 4983230072969 + 3 ^ 40 * 2207285 * 2
def baseEnd_2207285 : Nat := 1133398146459501720986387

theorem tailTrace_2207285 : CollatzResearch.WordTrace tailWord_2207285 prefixEnd_2207285 1133398146459501720986387 := by
  unfold tailWord_2207285
  simp only [CollatzResearch.WordTrace]
  refine ⟨80506297808390894110655309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53670865205593929407103539 80506297808390894110655309)
  ·
    refine ⟨30189861678146585291495741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80506297808390894110655309 30189861678146585291495741)
    ·
      refine ⟨11321198129304969484310903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30189861678146585291495741 11321198129304969484310903)
      ·
        refine ⟨16981797193957454226466355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11321198129304969484310903 16981797193957454226466355)
        ·
          refine ⟨25472695790936181339699533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16981797193957454226466355 25472695790936181339699533)
          ·
            refine ⟨9552260921601068002387325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25472695790936181339699533 9552260921601068002387325)
            ·
              refine ⟨3582097845600400500895247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9552260921601068002387325 3582097845600400500895247)
              ·
                refine ⟨5373146768400600751342871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582097845600400500895247 5373146768400600751342871)
                ·
                  refine ⟨8059720152600901127014307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373146768400600751342871 8059720152600901127014307)
                  ·
                    refine ⟨12089580228901351690521461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8059720152600901127014307 12089580228901351690521461)
                    ·
                      refine ⟨1133398146459501720986387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12089580228901351690521461 1133398146459501720986387)
                      ·
                        rfl

theorem cell23_2207285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2207285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207285 prefixEnd_2207285 := by exact prefixLift 2207285
  have htrace : WordTrace (prefixWord ++ tailWord_2207285) baseStart_2207285 baseEnd_2207285 := by
    simpa [prefixWord, tailWord_2207285, baseEnd_2207285] using wordTrace_append hprefix tailTrace_2207285
  have hstable : (prefixWord ++ tailWord_2207285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207285).length < 2 ^ (prefixWord ++ tailWord_2207285).sum := by decide
  have hdescent : baseEnd_2207285 < baseStart_2207285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207293 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_2207293 : Nat := 118140960795 + 2207293 * 2 ^ 59
def prefixEnd_2207293 : Nat := 4983230072969 + 3 ^ 40 * 2207293 * 2
def baseEnd_2207293 : Nat := 1133402254304737689686351

theorem tailTrace_2207293 : CollatzResearch.WordTrace tailWord_2207293 prefixEnd_2207293 1133402254304737689686351 := by
  unfold tailWord_2207293
  simp only [CollatzResearch.WordTrace]
  refine ⟨80506589592361911476946533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53671059728241274317964355 80506589592361911476946533)
  ·
    refine ⟨15094985548567858401927475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80506589592361911476946533 15094985548567858401927475)
    ·
      refine ⟨22642478322851787602891213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094985548567858401927475 22642478322851787602891213)
      ·
        refine ⟨8490929371069420351084205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22642478322851787602891213 8490929371069420351084205)
        ·
          refine ⟨3184098514151032631656577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8490929371069420351084205 3184098514151032631656577)
          ·
            refine ⟨2388073885613274473742433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3184098514151032631656577 2388073885613274473742433)
            ·
              refine ⟨1791055414209955855306825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388073885613274473742433 1791055414209955855306825)
              ·
                refine ⟨1343291560657466891480119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791055414209955855306825 1343291560657466891480119)
                ·
                  refine ⟨2014937340986200337220179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343291560657466891480119 2014937340986200337220179)
                  ·
                    refine ⟨3022406011479300505830269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014937340986200337220179 3022406011479300505830269)
                    ·
                      refine ⟨1133402254304737689686351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022406011479300505830269 1133402254304737689686351)
                      ·
                        rfl

theorem cell23_2207293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_2207293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207293 prefixEnd_2207293 := by exact prefixLift 2207293
  have htrace : WordTrace (prefixWord ++ tailWord_2207293) baseStart_2207293 baseEnd_2207293 := by
    simpa [prefixWord, tailWord_2207293, baseEnd_2207293] using wordTrace_append hprefix tailTrace_2207293
  have hstable : (prefixWord ++ tailWord_2207293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207293).length < 2 ^ (prefixWord ++ tailWord_2207293).sum := by decide
  have hdescent : baseEnd_2207293 < baseStart_2207293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207328 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2207328 : Nat := 118140960795 + 2207328 * 2 ^ 59
def prefixEnd_2207328 : Nat := 4983230072969 + 3 ^ 40 * 2207328 * 2
def baseEnd_2207328 : Nat := 1133420226127645052748689

theorem tailTrace_2207328 : CollatzResearch.WordTrace tailWord_2207328 prefixEnd_2207328 1133420226127645052748689 := by
  unfold tailWord_2207328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40253933073617556227235319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53671910764823408302980425 40253933073617556227235319)
  ·
    refine ⟨60380899610426334340852979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40253933073617556227235319 60380899610426334340852979)
    ·
      refine ⟨90571349415639501511279469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60380899610426334340852979 90571349415639501511279469)
      ·
        refine ⟨33964256030864813066729801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90571349415639501511279469 33964256030864813066729801)
        ·
          refine ⟨25473192023148609800047351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33964256030864813066729801 25473192023148609800047351)
          ·
            refine ⟨38209788034722914700071027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25473192023148609800047351 38209788034722914700071027)
            ·
              refine ⟨57314682052084372050106541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38209788034722914700071027 57314682052084372050106541)
              ·
                refine ⟨21493005769531639518789953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57314682052084372050106541 21493005769531639518789953)
                ·
                  refine ⟨16119754327148729639092465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21493005769531639518789953 16119754327148729639092465)
                  ·
                    refine ⟨12089815745361547229319349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16119754327148729639092465 12089815745361547229319349)
                    ·
                      refine ⟨1133420226127645052748689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12089815745361547229319349 1133420226127645052748689)
                      ·
                        rfl

theorem cell23_2207328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2207328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207328 prefixEnd_2207328 := by exact prefixLift 2207328
  have htrace : WordTrace (prefixWord ++ tailWord_2207328) baseStart_2207328 baseEnd_2207328 := by
    simpa [prefixWord, tailWord_2207328, baseEnd_2207328] using wordTrace_append hprefix tailTrace_2207328
  have hstable : (prefixWord ++ tailWord_2207328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207328).length < 2 ^ (prefixWord ++ tailWord_2207328).sum := by decide
  have hdescent : baseEnd_2207328 < baseStart_2207328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207336 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2207336 : Nat := 118140960795 + 2207336 * 2 ^ 59
def prefixEnd_2207336 : Nat := 4983230072969 + 3 ^ 40 * 2207336 * 2
def baseEnd_2207336 : Nat := 1133424333972881021448653

theorem tailTrace_2207336 : CollatzResearch.WordTrace tailWord_2207336 prefixEnd_2207336 1133424333972881021448653 := by
  unfold tailWord_2207336
  simp only [CollatzResearch.WordTrace]
  refine ⟨40254078965603064910380931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53672105287470753213841241 40254078965603064910380931)
  ·
    refine ⟨60381118448404597365571397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40254078965603064910380931 60381118448404597365571397)
    ·
      refine ⟨11321459709075862006044637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60381118448404597365571397 11321459709075862006044637)
      ·
        refine ⟨4245547390903448252266739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11321459709075862006044637 4245547390903448252266739)
        ·
          refine ⟨6368321086355172378400109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245547390903448252266739 6368321086355172378400109)
          ·
            refine ⟨2388120407383189641900041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6368321086355172378400109 2388120407383189641900041)
            ·
              refine ⟨1791090305537392231425031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388120407383189641900041 1791090305537392231425031)
              ·
                refine ⟨2686635458306088347137547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791090305537392231425031 2686635458306088347137547)
                ·
                  refine ⟨4029953187459132520706321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686635458306088347137547 4029953187459132520706321)
                  ·
                    refine ⟨3022464890594349390529741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029953187459132520706321 3022464890594349390529741)
                    ·
                      refine ⟨1133424333972881021448653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022464890594349390529741 1133424333972881021448653)
                      ·
                        rfl

theorem cell23_2207336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2207336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207336 prefixEnd_2207336 := by exact prefixLift 2207336
  have htrace : WordTrace (prefixWord ++ tailWord_2207336) baseStart_2207336 baseEnd_2207336 := by
    simpa [prefixWord, tailWord_2207336, baseEnd_2207336] using wordTrace_append hprefix tailTrace_2207336
  have hstable : (prefixWord ++ tailWord_2207336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207336).length < 2 ^ (prefixWord ++ tailWord_2207336).sum := by decide
  have hdescent : baseEnd_2207336 < baseStart_2207336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207349 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2207349 : Nat := 118140960795 + 2207349 * 2 ^ 59
def prefixEnd_2207349 : Nat := 4983230072969 + 3 ^ 40 * 2207349 * 2
def baseEnd_2207349 : Nat := 1133431009221389470586093

theorem tailTrace_2207349 : CollatzResearch.WordTrace tailWord_2207349 prefixEnd_2207349 1133431009221389470586093 := by
  unfold tailWord_2207349
  simp only [CollatzResearch.WordTrace]
  refine ⟨80508632080159033040985101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53672421386772688693990067 80508632080159033040985101)
  ·
    refine ⟨30190737030059637390369413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80508632080159033040985101 30190737030059637390369413)
    ·
      refine ⟨5660763193136182010694265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30190737030059637390369413 5660763193136182010694265)
      ·
        refine ⟨4245572394852136508020699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5660763193136182010694265 4245572394852136508020699)
        ·
          refine ⟨6368358592278204762031049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245572394852136508020699 6368358592278204762031049)
          ·
            refine ⟨4776268944208653571523287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6368358592278204762031049 4776268944208653571523287)
            ·
              refine ⟨7164403416312980357284931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776268944208653571523287 7164403416312980357284931)
              ·
                refine ⟨10746605124469470535927397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7164403416312980357284931 10746605124469470535927397)
                ·
                  refine ⟨2014988460838025725486387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10746605124469470535927397 2014988460838025725486387)
                  ·
                    refine ⟨3022482691257038588229581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014988460838025725486387 3022482691257038588229581)
                    ·
                      refine ⟨1133431009221389470586093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022482691257038588229581 1133431009221389470586093)
                      ·
                        rfl

theorem cell23_2207349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2207349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207349 prefixEnd_2207349 := by exact prefixLift 2207349
  have htrace : WordTrace (prefixWord ++ tailWord_2207349) baseStart_2207349 baseEnd_2207349 := by
    simpa [prefixWord, tailWord_2207349, baseEnd_2207349] using wordTrace_append hprefix tailTrace_2207349
  have hstable : (prefixWord ++ tailWord_2207349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207349).length < 2 ^ (prefixWord ++ tailWord_2207349).sum := by decide
  have hdescent : baseEnd_2207349 < baseStart_2207349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207405 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2207405 : Nat := 118140960795 + 2207405 * 2 ^ 59
def prefixEnd_2207405 : Nat := 4983230072969 + 3 ^ 40 * 2207405 * 2
def baseEnd_2207405 : Nat := 1133459764138041251485835

theorem tailTrace_2207405 : CollatzResearch.WordTrace tailWord_2207405 prefixEnd_2207405 1133459764138041251485835 := by
  unfold tailWord_2207405
  simp only [CollatzResearch.WordTrace]
  refine ⟨80510674567956154605023669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53673783045304103070015779 80510674567956154605023669)
  ·
    refine ⟨7547875740745889494220969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80510674567956154605023669 7547875740745889494220969)
    ·
      refine ⟨5660906805559417120665727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7547875740745889494220969 5660906805559417120665727)
      ·
        refine ⟨8491360208339125680998591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5660906805559417120665727 8491360208339125680998591)
        ·
          refine ⟨12737040312508688521497887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8491360208339125680998591 12737040312508688521497887)
          ·
            refine ⟨19105560468763032782246831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12737040312508688521497887 19105560468763032782246831)
            ·
              refine ⟨28658340703144549173370247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19105560468763032782246831 28658340703144549173370247)
              ·
                refine ⟨42987511054716823760055371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28658340703144549173370247 42987511054716823760055371)
                ·
                  refine ⟨64481266582075235640083057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42987511054716823760055371 64481266582075235640083057)
                  ·
                    refine ⟨48360949936556426730062293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64481266582075235640083057 48360949936556426730062293)
                    ·
                      refine ⟨1133459764138041251485835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48360949936556426730062293 1133459764138041251485835)
                      ·
                        rfl

theorem cell23_2207405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2207405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207405 prefixEnd_2207405 := by exact prefixLift 2207405
  have htrace : WordTrace (prefixWord ++ tailWord_2207405) baseStart_2207405 baseEnd_2207405 := by
    simpa [prefixWord, tailWord_2207405, baseEnd_2207405] using wordTrace_append hprefix tailTrace_2207405
  have hstable : (prefixWord ++ tailWord_2207405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207405).length < 2 ^ (prefixWord ++ tailWord_2207405).sum := by decide
  have hdescent : baseEnd_2207405 < baseStart_2207405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207442 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2207442 : Nat := 118140960795 + 2207442 * 2 ^ 59
def prefixEnd_2207442 : Nat := 4983230072969 + 3 ^ 40 * 2207442 * 2
def baseEnd_2207442 : Nat := 377826254307419202241055

theorem tailTrace_2207442 : CollatzResearch.WordTrace tailWord_2207442 prefixEnd_2207442 377826254307419202241055 := by
  unfold tailWord_2207442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20128006017205527481030145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53674682712548073282747053 20128006017205527481030145)
  ·
    refine ⟨15096004512904145610772609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20128006017205527481030145 15096004512904145610772609)
    ·
      refine ⟨11322003384678109208079457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15096004512904145610772609 11322003384678109208079457)
      ·
        refine ⟨8491502538508581906059593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11322003384678109208079457 8491502538508581906059593)
        ·
          refine ⟨6368626903881436429544695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8491502538508581906059593 6368626903881436429544695)
          ·
            refine ⟨9552940355822154644317043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368626903881436429544695 9552940355822154644317043)
            ·
              refine ⟨14329410533733231966475565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9552940355822154644317043 14329410533733231966475565)
              ·
                refine ⟨5373528950149961987428337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14329410533733231966475565 5373528950149961987428337)
                ·
                  refine ⟨4030146712612471490571253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5373528950149961987428337 4030146712612471490571253)
                  ·
                    refine ⟨377826254307419202241055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4030146712612471490571253 377826254307419202241055)
                    ·
                      rfl

theorem cell23_2207442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2207442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207442 prefixEnd_2207442 := by exact prefixLift 2207442
  have htrace : WordTrace (prefixWord ++ tailWord_2207442) baseStart_2207442 baseEnd_2207442 := by
    simpa [prefixWord, tailWord_2207442, baseEnd_2207442] using wordTrace_append hprefix tailTrace_2207442
  have hstable : (prefixWord ++ tailWord_2207442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207442).length < 2 ^ (prefixWord ++ tailWord_2207442).sum := by decide
  have hdescent : baseEnd_2207442 < baseStart_2207442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207463 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 5]
def baseStart_2207463 : Nat := 118140960795 + 2207463 * 2 ^ 59
def prefixEnd_2207463 : Nat := 4983230072969 + 3 ^ 40 * 2207463 * 2
def baseEnd_2207463 : Nat := 125943282890666891617841

theorem tailTrace_2207463 : CollatzResearch.WordTrace tailWord_2207463 prefixEnd_2207463 125943282890666891617841 := by
  unfold tailWord_2207463
  simp only [CollatzResearch.WordTrace]
  refine ⟨80512790001746030510635043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53675193334497353673756695 80512790001746030510635043)
  ·
    refine ⟨120769185002619045765952565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80512790001746030510635043 120769185002619045765952565)
    ·
      refine ⟨11322111093995535540558053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120769185002619045765952565 11322111093995535540558053)
      ·
        refine ⟨2122895830124162913854635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11322111093995535540558053 2122895830124162913854635)
        ·
          refine ⟨3184343745186244370781953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122895830124162913854635 3184343745186244370781953)
          ·
            refine ⟨2388257808889683278086465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3184343745186244370781953 2388257808889683278086465)
            ·
              refine ⟨1791193356667262458564849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388257808889683278086465 1791193356667262458564849)
              ·
                refine ⟨1343395017500446843923637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791193356667262458564849 1343395017500446843923637)
                ·
                  refine ⟨125943282890666891617841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1343395017500446843923637 125943282890666891617841)
                  ·
                    rfl

theorem cell23_2207463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 5].length) (baseStart_2207463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207463 prefixEnd_2207463 := by exact prefixLift 2207463
  have htrace : WordTrace (prefixWord ++ tailWord_2207463) baseStart_2207463 baseEnd_2207463 := by
    simpa [prefixWord, tailWord_2207463, baseEnd_2207463] using wordTrace_append hprefix tailTrace_2207463
  have hstable : (prefixWord ++ tailWord_2207463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207463).length < 2 ^ (prefixWord ++ tailWord_2207463).sum := by decide
  have hdescent : baseEnd_2207463 < baseStart_2207463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207465 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_2207465 : Nat := 118140960795 + 2207465 * 2 ^ 59
def prefixEnd_2207465 : Nat := 4983230072969 + 3 ^ 40 * 2207465 * 2
def baseEnd_2207465 : Nat := 1133490572977311016735559

theorem tailTrace_2207465 : CollatzResearch.WordTrace tailWord_2207465 prefixEnd_2207465 1133490572977311016735559 := by
  unfold tailWord_2207465
  simp only [CollatzResearch.WordTrace]
  refine ⟨80512862947738784852207849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53675241965159189901471899 80512862947738784852207849)
  ·
    refine ⟨60384647210804088639155887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80512862947738784852207849 60384647210804088639155887)
    ·
      refine ⟨90576970816206132958733831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60384647210804088639155887 90576970816206132958733831)
      ·
        refine ⟨135865456224309199438100747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90576970816206132958733831 135865456224309199438100747)
        ·
          refine ⟨203798184336463799157151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135865456224309199438100747 203798184336463799157151121)
          ·
            refine ⟨152848638252347849367863341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203798184336463799157151121 152848638252347849367863341)
            ·
              refine ⟨57318239344630443512948753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152848638252347849367863341 57318239344630443512948753)
              ·
                refine ⟨42988679508472832634711565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57318239344630443512948753 42988679508472832634711565)
                ·
                  refine ⟨16120754815677312238016837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42988679508472832634711565 16120754815677312238016837)
                  ·
                    refine ⟨3022641527939496044628157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16120754815677312238016837 3022641527939496044628157)
                    ·
                      refine ⟨1133490572977311016735559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022641527939496044628157 1133490572977311016735559)
                      ·
                        rfl

theorem cell23_2207465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_2207465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207465 prefixEnd_2207465 := by exact prefixLift 2207465
  have htrace : WordTrace (prefixWord ++ tailWord_2207465) baseStart_2207465 baseEnd_2207465 := by
    simpa [prefixWord, tailWord_2207465, baseEnd_2207465] using wordTrace_append hprefix tailTrace_2207465
  have hstable : (prefixWord ++ tailWord_2207465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207465).length < 2 ^ (prefixWord ++ tailWord_2207465).sum := by decide
  have hdescent : baseEnd_2207465 < baseStart_2207465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207549 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2207549 : Nat := 118140960795 + 2207549 * 2 ^ 59
def prefixEnd_2207549 : Nat := 4983230072969 + 3 ^ 40 * 2207549 * 2
def baseEnd_2207549 : Nat := 377844568450762896028391

theorem tailTrace_2207549 : CollatzResearch.WordTrace tailWord_2207549 prefixEnd_2207549 377844568450762896028391 := by
  unfold tailWord_2207549
  simp only [CollatzResearch.WordTrace]
  refine ⟨80515926679434467198265701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53677284452956311465510467 80515926679434467198265701)
  ·
    refine ⟨15096736252393962599674819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80515926679434467198265701 15096736252393962599674819)
    ·
      refine ⟨22645104378590943899512229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15096736252393962599674819 22645104378590943899512229)
      ·
        refine ⟨4245957070985801981158543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22645104378590943899512229 4245957070985801981158543)
        ·
          refine ⟨6368935606478702971737815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245957070985801981158543 6368935606478702971737815)
          ·
            refine ⟨9553403409718054457606723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368935606478702971737815 9553403409718054457606723)
            ·
              refine ⟨14330105114577081686410085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9553403409718054457606723 14330105114577081686410085)
              ·
                refine ⟨2686894708983202816201891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14330105114577081686410085 2686894708983202816201891)
                ·
                  refine ⟨4030342063474804224302837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686894708983202816201891 4030342063474804224302837)
                  ·
                    refine ⟨377844568450762896028391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4030342063474804224302837 377844568450762896028391)
                    ·
                      rfl

theorem cell23_2207549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2207549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207549 prefixEnd_2207549 := by exact prefixLift 2207549
  have htrace : WordTrace (prefixWord ++ tailWord_2207549) baseStart_2207549 baseEnd_2207549 := by
    simpa [prefixWord, tailWord_2207549, baseEnd_2207549] using wordTrace_append hprefix tailTrace_2207549
  have hstable : (prefixWord ++ tailWord_2207549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207549).length < 2 ^ (prefixWord ++ tailWord_2207549).sum := by decide
  have hdescent : baseEnd_2207549 < baseStart_2207549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207562 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_2207562 : Nat := 118140960795 + 2207562 * 2 ^ 59
def prefixEnd_2207562 : Nat := 4983230072969 + 3 ^ 40 * 2207562 * 2
def baseEnd_2207562 : Nat := 377846793533599045740871

theorem tailTrace_2207562 : CollatzResearch.WordTrace tailWord_2207562 prefixEnd_2207562 377846793533599045740871 := by
  unfold tailWord_2207562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20129100207096842604622235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53677600552258246945659293 20129100207096842604622235)
  ·
    refine ⟨30193650310645263906933353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20129100207096842604622235 30193650310645263906933353)
    ·
      refine ⟨22645237732983947930200015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30193650310645263906933353 22645237732983947930200015)
      ·
        refine ⟨33967856599475921895300023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22645237732983947930200015 33967856599475921895300023)
        ·
          refine ⟨50951784899213882842950035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33967856599475921895300023 50951784899213882842950035)
          ·
            refine ⟨76427677348820824264425053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50951784899213882842950035 76427677348820824264425053)
            ·
              refine ⟨28660379005807809099159395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76427677348820824264425053 28660379005807809099159395)
              ·
                refine ⟨42990568508711713648739093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28660379005807809099159395 42990568508711713648739093)
                ·
                  refine ⟨2015182898845861577284645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42990568508711713648739093 2015182898845861577284645)
                  ·
                    refine ⟨377846793533599045740871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015182898845861577284645 377846793533599045740871)
                    ·
                      rfl

theorem cell23_2207562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_2207562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207562 prefixEnd_2207562 := by exact prefixLift 2207562
  have htrace : WordTrace (prefixWord ++ tailWord_2207562) baseStart_2207562 baseEnd_2207562 := by
    simpa [prefixWord, tailWord_2207562, baseEnd_2207562] using wordTrace_append hprefix tailTrace_2207562
  have hstable : (prefixWord ++ tailWord_2207562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207562).length < 2 ^ (prefixWord ++ tailWord_2207562).sum := by decide
  have hdescent : baseEnd_2207562 < baseStart_2207562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207569 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_2207569 : Nat := 118140960795 + 2207569 * 2 ^ 59
def prefixEnd_2207569 : Nat := 4983230072969 + 3 ^ 40 * 2207569 * 2
def baseEnd_2207569 : Nat := 1133543974965378609835081

theorem tailTrace_2207569 : CollatzResearch.WordTrace tailWord_2207569 prefixEnd_2207569 1133543974965378609835081 := by
  unfold tailWord_2207569
  simp only [CollatzResearch.WordTrace]
  refine ⟨80516656139362010613993761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53677770759574673742662507 80516656139362010613993761)
  ·
    refine ⟨60387492104521507960495321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80516656139362010613993761 60387492104521507960495321)
    ·
      refine ⟨45290619078391130970371491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60387492104521507960495321 45290619078391130970371491)
      ·
        refine ⟨67935928617586696455557237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45290619078391130970371491 67935928617586696455557237)
        ·
          refine ⟨6368993307898752792708491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67935928617586696455557237 6368993307898752792708491)
          ·
            refine ⟨9553489961848129189062737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368993307898752792708491 9553489961848129189062737)
            ·
              refine ⟨7165117471386096891797053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9553489961848129189062737 7165117471386096891797053)
              ·
                refine ⟨2686919051769786334423895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7165117471386096891797053 2686919051769786334423895)
                ·
                  refine ⟨4030378577654679501635843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686919051769786334423895 4030378577654679501635843)
                  ·
                    refine ⟨6045567866482019252453765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4030378577654679501635843 6045567866482019252453765)
                    ·
                      refine ⟨1133543974965378609835081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6045567866482019252453765 1133543974965378609835081)
                      ·
                        rfl

theorem cell23_2207569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_2207569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207569 prefixEnd_2207569 := by exact prefixLift 2207569
  have htrace : WordTrace (prefixWord ++ tailWord_2207569) baseStart_2207569 baseEnd_2207569 := by
    simpa [prefixWord, tailWord_2207569, baseEnd_2207569] using wordTrace_append hprefix tailTrace_2207569
  have hstable : (prefixWord ++ tailWord_2207569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207569).length < 2 ^ (prefixWord ++ tailWord_2207569).sum := by decide
  have hdescent : baseEnd_2207569 < baseStart_2207569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207580 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2207580 : Nat := 118140960795 + 2207580 * 2 ^ 59
def prefixEnd_2207580 : Nat := 4983230072969 + 3 ^ 40 * 2207580 * 2
def baseEnd_2207580 : Nat := 1133549623252578066797531

theorem tailTrace_2207580 : CollatzResearch.WordTrace tailWord_2207580 prefixEnd_2207580 1133549623252578066797531 := by
  unfold tailWord_2207580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40258528671161079746322097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53678038228214772995096129 40258528671161079746322097)
  ·
    refine ⟨30193896503370809809741573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40258528671161079746322097 30193896503370809809741573)
    ·
      refine ⟨5661355594382026839326545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30193896503370809809741573 5661355594382026839326545)
      ·
        refine ⟨4246016695786520129494909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5661355594382026839326545 4246016695786520129494909)
        ·
          refine ⟨1592256260919945048560591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4246016695786520129494909 1592256260919945048560591)
          ·
            refine ⟨2388384391379917572840887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592256260919945048560591 2388384391379917572840887)
            ·
              refine ⟨3582576587069876359261331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388384391379917572840887 3582576587069876359261331)
              ·
                refine ⟨5373864880604814538891997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582576587069876359261331 5373864880604814538891997)
                ·
                  refine ⟨2015199330226805452084499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5373864880604814538891997 2015199330226805452084499)
                  ·
                    refine ⟨3022798995340208178126749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015199330226805452084499 3022798995340208178126749)
                    ·
                      refine ⟨1133549623252578066797531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022798995340208178126749 1133549623252578066797531)
                      ·
                        rfl

theorem cell23_2207580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2207580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207580 prefixEnd_2207580 := by exact prefixLift 2207580
  have htrace : WordTrace (prefixWord ++ tailWord_2207580) baseStart_2207580 baseEnd_2207580 := by
    simpa [prefixWord, tailWord_2207580, baseEnd_2207580] using wordTrace_append hprefix tailTrace_2207580
  have hstable : (prefixWord ++ tailWord_2207580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207580).length < 2 ^ (prefixWord ++ tailWord_2207580).sum := by decide
  have hdescent : baseEnd_2207580 < baseStart_2207580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207592 : List Nat := [2, 1, 4, 2, 1, 1, 4, 8]
def baseStart_2207592 : Nat := 118140960795 + 2207592 * 2 ^ 59
def prefixEnd_2207592 : Nat := 4983230072969 + 3 ^ 40 * 2207592 * 2
def baseEnd_2207592 : Nat := 41983547593349334068425

theorem tailTrace_2207592 : CollatzResearch.WordTrace tailWord_2207592 prefixEnd_2207592 41983547593349334068425 := by
  unfold tailWord_2207592
  simp only [CollatzResearch.WordTrace]
  refine ⟨40258747509139342771040515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53678330012185790361387353 40258747509139342771040515)
  ·
    refine ⟨60388121263709014156560773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40258747509139342771040515 60388121263709014156560773)
    ·
      refine ⟨11322772736945440154355145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60388121263709014156560773 11322772736945440154355145)
      ·
        refine ⟨8492079552709080115766359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11322772736945440154355145 8492079552709080115766359)
        ·
          refine ⟨12738119329063620173649539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8492079552709080115766359 12738119329063620173649539)
          ·
            refine ⟨19107178993595430260474309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12738119329063620173649539 19107178993595430260474309)
            ·
              refine ⟨3582596061299143173838933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19107178993595430260474309 3582596061299143173838933)
              ·
                refine ⟨41983547593349334068425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3582596061299143173838933 41983547593349334068425)
                ·
                  rfl

theorem cell23_2207592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 8].length) (baseStart_2207592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207592 prefixEnd_2207592 := by exact prefixLift 2207592
  have htrace : WordTrace (prefixWord ++ tailWord_2207592) baseStart_2207592 baseEnd_2207592 := by
    simpa [prefixWord, tailWord_2207592, baseEnd_2207592] using wordTrace_append hprefix tailTrace_2207592
  have hstable : (prefixWord ++ tailWord_2207592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207592).length < 2 ^ (prefixWord ++ tailWord_2207592).sum := by decide
  have hdescent : baseEnd_2207592 < baseStart_2207592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207595 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_2207595 : Nat := 118140960795 + 2207595 * 2 ^ 59
def prefixEnd_2207595 : Nat := 4983230072969 + 3 ^ 40 * 2207595 * 2
def baseEnd_2207595 : Nat := 1133557325462395508109961

theorem tailTrace_2207595 : CollatzResearch.WordTrace tailWord_2207595 prefixEnd_2207595 1133557325462395508109961 := by
  unfold tailWord_2207595
  simp only [CollatzResearch.WordTrace]
  refine ⟨80517604437267817054440239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53678402958178544702960159 80517604437267817054440239)
  ·
    refine ⟨120776406655901725581660359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80517604437267817054440239 120776406655901725581660359)
    ·
      refine ⟨181164609983852588372490539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120776406655901725581660359 181164609983852588372490539)
      ·
        refine ⟨271746914975778882558735809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181164609983852588372490539 271746914975778882558735809)
        ·
          refine ⟨203810186231834161919051857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271746914975778882558735809 203810186231834161919051857)
          ·
            refine ⟨152857639673875621439288893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203810186231834161919051857 152857639673875621439288893)
            ·
              refine ⟨57321614877703358039733335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152857639673875621439288893 57321614877703358039733335)
              ·
                refine ⟨85982422316555037059600003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57321614877703358039733335 85982422316555037059600003)
                ·
                  refine ⟨128973633474832555589400005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85982422316555037059600003 128973633474832555589400005)
                  ·
                    refine ⟨24182556276531104173012501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128973633474832555589400005 24182556276531104173012501)
                    ·
                      refine ⟨1133557325462395508109961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24182556276531104173012501 1133557325462395508109961)
                      ·
                        rfl

theorem cell23_2207595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_2207595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207595 prefixEnd_2207595 := by exact prefixLift 2207595
  have htrace : WordTrace (prefixWord ++ tailWord_2207595) baseStart_2207595 baseEnd_2207595 := by
    simpa [prefixWord, tailWord_2207595, baseEnd_2207595] using wordTrace_append hprefix tailTrace_2207595
  have hstable : (prefixWord ++ tailWord_2207595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207595).length < 2 ^ (prefixWord ++ tailWord_2207595).sum := by decide
  have hdescent : baseEnd_2207595 < baseStart_2207595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207596 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_2207596 : Nat := 118140960795 + 2207596 * 2 ^ 59
def prefixEnd_2207596 : Nat := 4983230072969 + 3 ^ 40 * 2207596 * 2
def baseEnd_2207596 : Nat := 377852612981016668065819

theorem tailTrace_2207596 : CollatzResearch.WordTrace tailWord_2207596 prefixEnd_2207596 377852612981016668065819 := by
  unfold tailWord_2207596
  simp only [CollatzResearch.WordTrace]
  refine ⟨40258820455132097112613321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53678427273509462816817761 40258820455132097112613321)
  ·
    refine ⟨30194115341349072834459991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40258820455132097112613321 30194115341349072834459991)
    ·
      refine ⟨45291173012023609251689987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30194115341349072834459991 45291173012023609251689987)
      ·
        refine ⟨67936759518035413877534981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45291173012023609251689987 67936759518035413877534981)
        ·
          refine ⟨12738142409631640102037809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67936759518035413877534981 12738142409631640102037809)
          ·
            refine ⟨9553606807223730076528357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12738142409631640102037809 9553606807223730076528357)
            ·
              refine ⟨1791301276354449389349067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9553606807223730076528357 1791301276354449389349067)
              ·
                refine ⟨2686951914531674084023601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791301276354449389349067 2686951914531674084023601)
                ·
                  refine ⟨2015213935898755563017701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686951914531674084023601 2015213935898755563017701)
                  ·
                    refine ⟨377852612981016668065819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015213935898755563017701 377852612981016668065819)
                    ·
                      rfl

theorem cell23_2207596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_2207596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207596 prefixEnd_2207596 := by exact prefixLift 2207596
  have htrace : WordTrace (prefixWord ++ tailWord_2207596) baseStart_2207596 baseEnd_2207596 := by
    simpa [prefixWord, tailWord_2207596, baseEnd_2207596] using wordTrace_append hprefix tailTrace_2207596
  have hstable : (prefixWord ++ tailWord_2207596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207596).length < 2 ^ (prefixWord ++ tailWord_2207596).sum := by decide
  have hdescent : baseEnd_2207596 < baseStart_2207596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207619 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3]
def baseStart_2207619 : Nat := 118140960795 + 2207619 * 2 ^ 59
def prefixEnd_2207619 : Nat := 4983230072969 + 3 ^ 40 * 2207619 * 2
def baseEnd_2207619 : Nat := 1133569648998103414209851

theorem tailTrace_2207619 : CollatzResearch.WordTrace tailWord_2207619 prefixEnd_2207619 1133569648998103414209851 := by
  unfold tailWord_2207619
  simp only [CollatzResearch.WordTrace]
  refine ⟨80518479789180869153313911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53678986526120579435542607 80518479789180869153313911)
  ·
    refine ⟨120777719683771303729970867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80518479789180869153313911 120777719683771303729970867)
    ·
      refine ⟨181166579525656955594956301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120777719683771303729970867 181166579525656955594956301)
      ·
        refine ⟨67937467322121358348108613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181166579525656955594956301 67937467322121358348108613)
        ·
          refine ⟨12738275122897754690270365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67937467322121358348108613 12738275122897754690270365)
          ·
            refine ⟨4776853171086658008851387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12738275122897754690270365 4776853171086658008851387)
            ·
              refine ⟨7165279756629987013277081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776853171086658008851387 7165279756629987013277081)
              ·
                refine ⟨5373959817472490259957811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7165279756629987013277081 5373959817472490259957811)
                ·
                  refine ⟨8060939726208735389936717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373959817472490259957811 8060939726208735389936717)
                  ·
                    refine ⟨3022852397328275771226269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8060939726208735389936717 3022852397328275771226269)
                    ·
                      refine ⟨1133569648998103414209851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022852397328275771226269 1133569648998103414209851)
                      ·
                        rfl

theorem cell23_2207619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_2207619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207619 prefixEnd_2207619 := by exact prefixLift 2207619
  have htrace : WordTrace (prefixWord ++ tailWord_2207619) baseStart_2207619 baseEnd_2207619 := by
    simpa [prefixWord, tailWord_2207619, baseEnd_2207619] using wordTrace_append hprefix tailTrace_2207619
  have hstable : (prefixWord ++ tailWord_2207619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207619).length < 2 ^ (prefixWord ++ tailWord_2207619).sum := by decide
  have hdescent : baseEnd_2207619 < baseStart_2207619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207623 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_2207623 : Nat := 118140960795 + 2207623 * 2 ^ 59
def prefixEnd_2207623 : Nat := 4983230072969 + 3 ^ 40 * 2207623 * 2
def baseEnd_2207623 : Nat := 1133571702920721398559833

theorem tailTrace_2207623 : CollatzResearch.WordTrace tailWord_2207623 prefixEnd_2207623 1133571702920721398559833 := by
  unfold tailWord_2207623
  simp only [CollatzResearch.WordTrace]
  refine ⟨80518625681166377836459523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53679083787444251890973015 80518625681166377836459523)
  ·
    refine ⟨120777938521749566754689285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80518625681166377836459523 120777938521749566754689285)
    ·
      refine ⟨22645863472828043766504241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120777938521749566754689285 22645863472828043766504241)
      ·
        refine ⟨16984397604621032824878181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22645863472828043766504241 16984397604621032824878181)
        ·
          refine ⟨3184574550866443654664659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16984397604621032824878181 3184574550866443654664659)
          ·
            refine ⟨4776861826299665481996989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184574550866443654664659 4776861826299665481996989)
            ·
              refine ⟨1791323184862374555748871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4776861826299665481996989 1791323184862374555748871)
              ·
                refine ⟨2686984777293561833623307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791323184862374555748871 2686984777293561833623307)
                ·
                  refine ⟨4030477165940342750434961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686984777293561833623307 4030477165940342750434961)
                  ·
                    refine ⟨3022857874455257062826221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030477165940342750434961 3022857874455257062826221)
                    ·
                      refine ⟨1133571702920721398559833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3022857874455257062826221 1133571702920721398559833)
                      ·
                        rfl

theorem cell23_2207623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_2207623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207623 prefixEnd_2207623 := by exact prefixLift 2207623
  have htrace : WordTrace (prefixWord ++ tailWord_2207623) baseStart_2207623 baseEnd_2207623 := by
    simpa [prefixWord, tailWord_2207623, baseEnd_2207623] using wordTrace_append hprefix tailTrace_2207623
  have hstable : (prefixWord ++ tailWord_2207623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207623).length < 2 ^ (prefixWord ++ tailWord_2207623).sum := by decide
  have hdescent : baseEnd_2207623 < baseStart_2207623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207652 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_2207652 : Nat := 118140960795 + 2207652 * 2 ^ 59
def prefixEnd_2207652 : Nat := 4983230072969 + 3 ^ 40 * 2207652 * 2
def baseEnd_2207652 : Nat := 377862197953233928365733

theorem tailTrace_2207652 : CollatzResearch.WordTrace tailWord_2207652 prefixEnd_2207652 377862197953233928365733 := by
  unfold tailWord_2207652
  simp only [CollatzResearch.WordTrace]
  refine ⟨40259841699030657894632605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53679788932040877192843473 40259841699030657894632605)
  ·
    refine ⟨15097440637136496710487227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40259841699030657894632605 15097440637136496710487227)
    ·
      refine ⟨22646160955704745065730841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15097440637136496710487227 22646160955704745065730841)
      ·
        refine ⟨16984620716778558799298131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22646160955704745065730841 16984620716778558799298131)
        ·
          refine ⟨25476931075167838198947197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16984620716778558799298131 25476931075167838198947197)
          ·
            refine ⟨9553849153187939324605199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25476931075167838198947197 9553849153187939324605199)
            ·
              refine ⟨14330773729781908986907799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9553849153187939324605199 14330773729781908986907799)
              ·
                refine ⟨21496160594672863480361699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14330773729781908986907799 21496160594672863480361699)
                ·
                  refine ⟨32244240892009295220542549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21496160594672863480361699 32244240892009295220542549)
                  ·
                    refine ⟨377862197953233928365733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32244240892009295220542549 377862197953233928365733)
                    ·
                      rfl

theorem cell23_2207652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_2207652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207652 prefixEnd_2207652 := by exact prefixLift 2207652
  have htrace : WordTrace (prefixWord ++ tailWord_2207652) baseStart_2207652 baseEnd_2207652 := by
    simpa [prefixWord, tailWord_2207652, baseEnd_2207652] using wordTrace_append hprefix tailTrace_2207652
  have hstable : (prefixWord ++ tailWord_2207652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207652).length < 2 ^ (prefixWord ++ tailWord_2207652).sum := by decide
  have hdescent : baseEnd_2207652 < baseStart_2207652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207672 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2207672 : Nat := 118140960795 + 2207672 * 2 ^ 59
def prefixEnd_2207672 : Nat := 4983230072969 + 3 ^ 40 * 2207672 * 2
def baseEnd_2207672 : Nat := 1133596863472791706847107

theorem tailTrace_2207672 : CollatzResearch.WordTrace tailWord_2207672 prefixEnd_2207672 1133596863472791706847107 := by
  unfold tailWord_2207672
  simp only [CollatzResearch.WordTrace]
  refine ⟨40260206428994429602496635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53680275238659239469995513 40260206428994429602496635)
  ·
    refine ⟨60390309643491644403744953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40260206428994429602496635 60390309643491644403744953)
    ·
      refine ⟨45292732232618733302808715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60390309643491644403744953 45292732232618733302808715)
      ·
        refine ⟨67939098348928099954213073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45292732232618733302808715 67939098348928099954213073)
        ·
          refine ⟨50954323761696074965659805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67939098348928099954213073 50954323761696074965659805)
          ·
            refine ⟨19107871410636028112122427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50954323761696074965659805 19107871410636028112122427)
            ·
              refine ⟨28661807115954042168183641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19107871410636028112122427 28661807115954042168183641)
              ·
                refine ⟨21496355336965531626137731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28661807115954042168183641 21496355336965531626137731)
                ·
                  refine ⟨32244533005448297439206597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21496355336965531626137731 32244533005448297439206597)
                  ·
                    refine ⟨6045849938521555769851237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32244533005448297439206597 6045849938521555769851237)
                    ·
                      refine ⟨1133596863472791706847107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6045849938521555769851237 1133596863472791706847107)
                      ·
                        rfl

theorem cell23_2207672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2207672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207672 prefixEnd_2207672 := by exact prefixLift 2207672
  have htrace : WordTrace (prefixWord ++ tailWord_2207672) baseStart_2207672 baseEnd_2207672 := by
    simpa [prefixWord, tailWord_2207672, baseEnd_2207672] using wordTrace_append hprefix tailTrace_2207672
  have hstable : (prefixWord ++ tailWord_2207672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207672).length < 2 ^ (prefixWord ++ tailWord_2207672).sum := by decide
  have hdescent : baseEnd_2207672 < baseStart_2207672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207749 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_2207749 : Nat := 118140960795 + 2207749 * 2 ^ 59
def prefixEnd_2207749 : Nat := 4983230072969 + 3 ^ 40 * 2207749 * 2
def baseEnd_2207749 : Nat := 1133636401483187905584253

theorem tailTrace_2207749 : CollatzResearch.WordTrace tailWord_2207749 prefixEnd_2207749 1133636401483187905584253 := by
  unfold tailWord_2207749
  simp only [CollatzResearch.WordTrace]
  refine ⟨80523221278709901355546301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53682147519139934237030867 80523221278709901355546301)
  ·
    refine ⟨30196207979516213008329863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80523221278709901355546301 30196207979516213008329863)
    ·
      refine ⟨45294311969274319512494795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30196207979516213008329863 45294311969274319512494795)
      ·
        refine ⟨67941467953911479268742193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45294311969274319512494795 67941467953911479268742193)
        ·
          refine ⟨50956100965433609451556645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67941467953911479268742193 50956100965433609451556645)
          ·
            refine ⟨9554268931018801772166871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50956100965433609451556645 9554268931018801772166871)
            ·
              refine ⟨14331403396528202658250307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9554268931018801772166871 14331403396528202658250307)
              ·
                refine ⟨21497105094792303987375461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14331403396528202658250307 21497105094792303987375461)
                ·
                  refine ⟨4030707205273556997632899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21497105094792303987375461 4030707205273556997632899)
                  ·
                    refine ⟨6046060807910335496449349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4030707205273556997632899 6046060807910335496449349)
                    ·
                      refine ⟨1133636401483187905584253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6046060807910335496449349 1133636401483187905584253)
                      ·
                        rfl

theorem cell23_2207749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_2207749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207749 prefixEnd_2207749 := by exact prefixLift 2207749
  have htrace : WordTrace (prefixWord ++ tailWord_2207749) baseStart_2207749 baseEnd_2207749 := by
    simpa [prefixWord, tailWord_2207749, baseEnd_2207749] using wordTrace_append hprefix tailTrace_2207749
  have hstable : (prefixWord ++ tailWord_2207749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207749).length < 2 ^ (prefixWord ++ tailWord_2207749).sum := by decide
  have hdescent : baseEnd_2207749 < baseStart_2207749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207769 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_2207769 : Nat := 118140960795 + 2207769 * 2 ^ 59
def prefixEnd_2207769 : Nat := 4983230072969 + 3 ^ 40 * 2207769 * 2
def baseEnd_2207769 : Nat := 1133646671096277827334161

theorem tailTrace_2207769 : CollatzResearch.WordTrace tailWord_2207769 prefixEnd_2207769 1133646671096277827334161 := by
  unfold tailWord_2207769
  simp only [CollatzResearch.WordTrace]
  refine ⟨80523950738637444771274361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53682633825758296514182907 80523950738637444771274361)
  ·
    refine ⟨60392963053978083578455771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80523950738637444771274361 60392963053978083578455771)
    ·
      refine ⟨90589444580967125367683657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60392963053978083578455771 90589444580967125367683657)
      ·
        refine ⟨67942083435725344025762743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90589444580967125367683657 67942083435725344025762743)
        ·
          refine ⟨101913125153588016038644115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67942083435725344025762743 101913125153588016038644115)
          ·
            refine ⟨152869687730382024057966173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101913125153588016038644115 152869687730382024057966173)
            ·
              refine ⟨57326132898893259021737315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152869687730382024057966173 57326132898893259021737315)
              ·
                refine ⟨85989199348339888532605973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57326132898893259021737315 85989199348339888532605973)
                ·
                  refine ⟨4030743719453432274965905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85989199348339888532605973 4030743719453432274965905)
                  ·
                    refine ⟨3023057789590074206224429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030743719453432274965905 3023057789590074206224429)
                    ·
                      refine ⟨1133646671096277827334161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3023057789590074206224429 1133646671096277827334161)
                      ·
                        rfl

theorem cell23_2207769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_2207769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207769 prefixEnd_2207769 := by exact prefixLift 2207769
  have htrace : WordTrace (prefixWord ++ tailWord_2207769) baseStart_2207769 baseEnd_2207769 := by
    simpa [prefixWord, tailWord_2207769, baseEnd_2207769] using wordTrace_append hprefix tailTrace_2207769
  have hstable : (prefixWord ++ tailWord_2207769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207769).length < 2 ^ (prefixWord ++ tailWord_2207769).sum := by decide
  have hdescent : baseEnd_2207769 < baseStart_2207769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207836 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2207836 : Nat := 118140960795 + 2207836 * 2 ^ 59
def prefixEnd_2207836 : Nat := 4983230072969 + 3 ^ 40 * 2207836 * 2
def baseEnd_2207836 : Nat := 377893691433376355065451

theorem tailTrace_2207836 : CollatzResearch.WordTrace tailWord_2207836 prefixEnd_2207836 377893691433376355065451 := by
  unfold tailWord_2207836
  simp only [CollatzResearch.WordTrace]
  refine ⟨40263197214697357606981681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53684262952929810142642241 40263197214697357606981681)
  ·
    refine ⟨30197397911023018205236261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40263197214697357606981681 30197397911023018205236261)
    ·
      refine ⟨5662012108316815913481799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30197397911023018205236261 5662012108316815913481799)
      ·
        refine ⟨8493018162475223870222699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5662012108316815913481799 8493018162475223870222699)
        ·
          refine ⟨12739527243712835805334049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8493018162475223870222699 12739527243712835805334049)
          ·
            refine ⟨9554645432784626854000537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12739527243712835805334049 9554645432784626854000537)
            ·
              refine ⟨7165984074588470140500403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9554645432784626854000537 7165984074588470140500403)
              ·
                refine ⟨10748976111882705210750605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7165984074588470140500403 10748976111882705210750605)
                ·
                  refine ⟨4030866041956014454031477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10748976111882705210750605 4030866041956014454031477)
                  ·
                    refine ⟨377893691433376355065451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4030866041956014454031477 377893691433376355065451)
                    ·
                      rfl

theorem cell23_2207836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2207836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207836 prefixEnd_2207836 := by exact prefixLift 2207836
  have htrace : WordTrace (prefixWord ++ tailWord_2207836) baseStart_2207836 baseEnd_2207836 := by
    simpa [prefixWord, tailWord_2207836, baseEnd_2207836] using wordTrace_append hprefix tailTrace_2207836
  have hstable : (prefixWord ++ tailWord_2207836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207836).length < 2 ^ (prefixWord ++ tailWord_2207836).sum := by decide
  have hdescent : baseEnd_2207836 < baseStart_2207836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207843 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 2, 3, 2]
def baseStart_2207843 : Nat := 118140960795 + 2207843 * 2 ^ 59
def prefixEnd_2207843 : Nat := 4983230072969 + 3 ^ 40 * 2207843 * 2
def baseEnd_2207843 : Nat := 1133684668664710537808821

theorem tailTrace_2207843 : CollatzResearch.WordTrace tailWord_2207843 prefixEnd_2207843 1133684668664710537808821 := by
  unfold tailWord_2207843
  simp only [CollatzResearch.WordTrace]
  refine ⟨80526649740369355409468183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53684433160246236939645455 80526649740369355409468183)
  ·
    refine ⟨120789974610554033114202275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80526649740369355409468183 120789974610554033114202275)
    ·
      refine ⟨181184961915831049671303413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120789974610554033114202275 181184961915831049671303413)
      ·
        refine ⟨16986090179609160906684695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181184961915831049671303413 16986090179609160906684695)
        ·
          refine ⟨25479135269413741360027043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16986090179609160906684695 25479135269413741360027043)
          ·
            refine ⟨38218702904120612040040565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25479135269413741360027043 38218702904120612040040565)
            ·
              refine ⟨3583003397261307378753803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38218702904120612040040565 3583003397261307378753803)
              ·
                refine ⟨5374505095891961068130705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583003397261307378753803 5374505095891961068130705)
                ·
                  refine ⟨4030878821918970801098029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5374505095891961068130705 4030878821918970801098029)
                  ·
                    refine ⟨1511579558219614050411761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4030878821918970801098029 1511579558219614050411761)
                    ·
                      refine ⟨1133684668664710537808821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511579558219614050411761 1133684668664710537808821)
                      ·
                        rfl

theorem cell23_2207843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_2207843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207843 prefixEnd_2207843 := by exact prefixLift 2207843
  have htrace : WordTrace (prefixWord ++ tailWord_2207843) baseStart_2207843 baseEnd_2207843 := by
    simpa [prefixWord, tailWord_2207843, baseEnd_2207843] using wordTrace_append hprefix tailTrace_2207843
  have hstable : (prefixWord ++ tailWord_2207843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207843).length < 2 ^ (prefixWord ++ tailWord_2207843).sum := by decide
  have hdescent : baseEnd_2207843 < baseStart_2207843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207849 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_2207849 : Nat := 118140960795 + 2207849 * 2 ^ 59
def prefixEnd_2207849 : Nat := 4983230072969 + 3 ^ 40 * 2207849 * 2
def baseEnd_2207849 : Nat := 377895916516212504777931

theorem tailTrace_2207849 : CollatzResearch.WordTrace tailWord_2207849 prefixEnd_2207849 377895916516212504777931 := by
  unfold tailWord_2207849
  simp only [CollatzResearch.WordTrace]
  refine ⟨80526868578347618434186601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53684579052231745622791067 80526868578347618434186601)
  ·
    refine ⟨60395151433760713825639951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80526868578347618434186601 60395151433760713825639951)
    ·
      refine ⟨90592727150641070738459927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60395151433760713825639951 90592727150641070738459927)
      ·
        refine ⟨135889090725961606107689891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90592727150641070738459927 135889090725961606107689891)
        ·
          refine ⟨203833636088942409161534837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135889090725961606107689891 203833636088942409161534837)
          ·
            refine ⟨19109403383338350858893891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203833636088942409161534837 19109403383338350858893891)
            ·
              refine ⟨28664105075007526288340837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19109403383338350858893891 28664105075007526288340837)
              ·
                refine ⟨5374519701563911179063907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28664105075007526288340837 5374519701563911179063907)
                ·
                  refine ⟨8061779552345866768595861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374519701563911179063907 8061779552345866768595861)
                  ·
                    refine ⟨377895916516212504777931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8061779552345866768595861 377895916516212504777931)
                    ·
                      rfl

theorem cell23_2207849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_2207849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207849 prefixEnd_2207849 := by exact prefixLift 2207849
  have htrace : WordTrace (prefixWord ++ tailWord_2207849) baseStart_2207849 baseEnd_2207849 := by
    simpa [prefixWord, tailWord_2207849, baseEnd_2207849] using wordTrace_append hprefix tailTrace_2207849
  have hstable : (prefixWord ++ tailWord_2207849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207849).length < 2 ^ (prefixWord ++ tailWord_2207849).sum := by decide
  have hdescent : baseEnd_2207849 < baseStart_2207849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207876 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2207876 : Nat := 118140960795 + 2207876 * 2 ^ 59
def prefixEnd_2207876 : Nat := 4983230072969 + 3 ^ 40 * 2207876 * 2
def baseEnd_2207876 : Nat := 1133701613526308908696169

theorem tailTrace_2207876 : CollatzResearch.WordTrace tailWord_2207876 prefixEnd_2207876 1133701613526308908696169 := by
  unfold tailWord_2207876
  simp only [CollatzResearch.WordTrace]
  refine ⟨40263926674624901022709741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53685235566166534696946321 40263926674624901022709741)
  ·
    refine ⟨15098972502984337883516153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40263926674624901022709741 15098972502984337883516153)
    ·
      refine ⟨11324229377238253412637115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15098972502984337883516153 11324229377238253412637115)
      ·
        refine ⟨16986344065857380118955673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11324229377238253412637115 16986344065857380118955673)
        ·
          refine ⟨12739758049393035089216755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16986344065857380118955673 12739758049393035089216755)
          ·
            refine ⟨19109637074089552633825133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12739758049393035089216755 19109637074089552633825133)
            ·
              refine ⟨7166113902783582237684425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19109637074089552633825133 7166113902783582237684425)
              ·
                refine ⟨5374585427087686678263319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7166113902783582237684425 5374585427087686678263319)
                ·
                  refine ⟨8061878140631530017394979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374585427087686678263319 8061878140631530017394979)
                  ·
                    refine ⟨12092817210947295026092469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8061878140631530017394979 12092817210947295026092469)
                    ·
                      refine ⟨1133701613526308908696169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12092817210947295026092469 1133701613526308908696169)
                      ·
                        rfl

theorem cell23_2207876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2207876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207876 prefixEnd_2207876 := by exact prefixLift 2207876
  have htrace : WordTrace (prefixWord ++ tailWord_2207876) baseStart_2207876 baseEnd_2207876 := by
    simpa [prefixWord, tailWord_2207876, baseEnd_2207876] using wordTrace_append hprefix tailTrace_2207876
  have hstable : (prefixWord ++ tailWord_2207876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207876).length < 2 ^ (prefixWord ++ tailWord_2207876).sum := by decide
  have hdescent : baseEnd_2207876 < baseStart_2207876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207890 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2207890 : Nat := 118140960795 + 2207890 * 2 ^ 59
def prefixEnd_2207890 : Nat := 4983230072969 + 3 ^ 40 * 2207890 * 2
def baseEnd_2207890 : Nat := 1133708802255471853921105

theorem tailTrace_2207890 : CollatzResearch.WordTrace tailWord_2207890 prefixEnd_2207890 1133708802255471853921105 := by
  unfold tailWord_2207890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20132090992799770609107281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53685575980799388290952749 20132090992799770609107281)
  ·
    refine ⟨15099068244599827956830461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20132090992799770609107281 15099068244599827956830461)
    ·
      refine ⟨5662150591724935483811423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15099068244599827956830461 5662150591724935483811423)
      ·
        refine ⟨8493225887587403225717135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5662150591724935483811423 8493225887587403225717135)
        ·
          refine ⟨12739838831381104838575703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8493225887587403225717135 12739838831381104838575703)
          ·
            refine ⟨19109758247071657257863555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12739838831381104838575703 19109758247071657257863555)
            ·
              refine ⟨28664637370607485886795333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19109758247071657257863555 28664637370607485886795333)
              ·
                refine ⟨5374619506988903603774125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28664637370607485886795333 5374619506988903603774125)
                ·
                  refine ⟨2015482315120838851415297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5374619506988903603774125 2015482315120838851415297)
                  ·
                    refine ⟨1511611736340629138561473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015482315120838851415297 1511611736340629138561473)
                    ·
                      refine ⟨1133708802255471853921105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511611736340629138561473 1133708802255471853921105)
                      ·
                        rfl

theorem cell23_2207890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2207890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207890 prefixEnd_2207890 := by exact prefixLift 2207890
  have htrace : WordTrace (prefixWord ++ tailWord_2207890) baseStart_2207890 baseEnd_2207890 := by
    simpa [prefixWord, tailWord_2207890, baseEnd_2207890] using wordTrace_append hprefix tailTrace_2207890
  have hstable : (prefixWord ++ tailWord_2207890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207890).length < 2 ^ (prefixWord ++ tailWord_2207890).sum := by decide
  have hdescent : baseEnd_2207890 < baseStart_2207890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207893 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_2207893 : Nat := 118140960795 + 2207893 * 2 ^ 59
def prefixEnd_2207893 : Nat := 4983230072969 + 3 ^ 40 * 2207893 * 2
def baseEnd_2207893 : Nat := 1133710342697435342183591

theorem tailTrace_2207893 : CollatzResearch.WordTrace tailWord_2207893 prefixEnd_2207893 1133710342697435342183591 := by
  unfold tailWord_2207893
  simp only [CollatzResearch.WordTrace]
  refine ⟨80528473390188213948788333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53685648926792142632525555 80528473390188213948788333)
  ·
    refine ⟨30198177521320580230795625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80528473390188213948788333 30198177521320580230795625)
    ·
      refine ⟨22648633140990435173096719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30198177521320580230795625 22648633140990435173096719)
      ·
        refine ⟨33972949711485652759645079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22648633140990435173096719 33972949711485652759645079)
        ·
          refine ⟨50959424567228479139467619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33972949711485652759645079 50959424567228479139467619)
          ·
            refine ⟨76439136850842718709201429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50959424567228479139467619 76439136850842718709201429)
            ·
              refine ⟨3583084539883252439493817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76439136850842718709201429 3583084539883252439493817)
              ·
                refine ⟨2687313404912439329620363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583084539883252439493817 2687313404912439329620363)
                ·
                  refine ⟨4030970107368658994430545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687313404912439329620363 4030970107368658994430545)
                  ·
                    refine ⟨3023227580526494245822909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030970107368658994430545 3023227580526494245822909)
                    ·
                      refine ⟨1133710342697435342183591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3023227580526494245822909 1133710342697435342183591)
                      ·
                        rfl

theorem cell23_2207893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_2207893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207893 prefixEnd_2207893 := by exact prefixLift 2207893
  have htrace : WordTrace (prefixWord ++ tailWord_2207893) baseStart_2207893 baseEnd_2207893 := by
    simpa [prefixWord, tailWord_2207893, baseEnd_2207893] using wordTrace_append hprefix tailTrace_2207893
  have hstable : (prefixWord ++ tailWord_2207893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207893).length < 2 ^ (prefixWord ++ tailWord_2207893).sum := by decide
  have hdescent : baseEnd_2207893 < baseStart_2207893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207896 : List Nat := [2, 1, 2, 4, 3, 1, 1, 9]
def baseStart_2207896 : Nat := 118140960795 + 2207896 * 2 ^ 59
def prefixEnd_2207896 : Nat := 4983230072969 + 3 ^ 40 * 2207896 * 2
def baseEnd_2207896 : Nat := 41989329005162919646151

theorem tailTrace_2207896 : CollatzResearch.WordTrace tailWord_2207896 prefixEnd_2207896 41989329005162919646151 := by
  unfold tailWord_2207896
  simp only [CollatzResearch.WordTrace]
  refine ⟨40264291404588672730573771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53685721872784896974098361 40264291404588672730573771)
  ·
    refine ⟨60396437106883009095860657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40264291404588672730573771 60396437106883009095860657)
    ·
      refine ⟨45297327830162256821895493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60396437106883009095860657 45297327830162256821895493)
      ·
        refine ⟨8493248968155423154105405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45297327830162256821895493 8493248968155423154105405)
        ·
          refine ⟨3184968363058283682789527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8493248968155423154105405 3184968363058283682789527)
          ·
            refine ⟨4777452544587425524184291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184968363058283682789527 4777452544587425524184291)
            ·
              refine ⟨7166178816881138286276437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777452544587425524184291 7166178816881138286276437)
              ·
                refine ⟨41989329005162919646151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7166178816881138286276437 41989329005162919646151)
                ·
                  rfl

theorem cell23_2207896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 9].length) (baseStart_2207896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207896 prefixEnd_2207896 := by exact prefixLift 2207896
  have htrace : WordTrace (prefixWord ++ tailWord_2207896) baseStart_2207896 baseEnd_2207896 := by
    simpa [prefixWord, tailWord_2207896, baseEnd_2207896] using wordTrace_append hprefix tailTrace_2207896
  have hstable : (prefixWord ++ tailWord_2207896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207896).length < 2 ^ (prefixWord ++ tailWord_2207896).sum := by decide
  have hdescent : baseEnd_2207896 < baseStart_2207896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207916 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_2207916 : Nat := 118140960795 + 2207916 * 2 ^ 59
def prefixEnd_2207916 : Nat := 4983230072969 + 3 ^ 40 * 2207916 * 2
def baseEnd_2207916 : Nat := 1133722152752488752195985

theorem tailTrace_2207916 : CollatzResearch.WordTrace tailWord_2207916 prefixEnd_2207916 1133722152752488752195985 := by
  unfold tailWord_2207916
  simp only [CollatzResearch.WordTrace]
  refine ⟨40264656134552444438437801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53686208179403259251250401 40264656134552444438437801)
  ·
    refine ⟨30198492100914333328828351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40264656134552444438437801 30198492100914333328828351)
    ·
      refine ⟨45297738151371499993242527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30198492100914333328828351 45297738151371499993242527)
      ·
        refine ⟨67946607227057249989863791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45297738151371499993242527 67946607227057249989863791)
        ·
          refine ⟨101919910840585874984795687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67946607227057249989863791 101919910840585874984795687)
          ·
            refine ⟨152879866260878812477193531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101919910840585874984795687 152879866260878812477193531)
            ·
              refine ⟨229319799391318218715790297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152879866260878812477193531 229319799391318218715790297)
              ·
                refine ⟨171989849543488664036842723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229319799391318218715790297 171989849543488664036842723)
                ·
                  refine ⟨257984774315232996055264085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171989849543488664036842723 257984774315232996055264085)
                  ·
                    refine ⟨1511629537003318336261313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 257984774315232996055264085 1511629537003318336261313)
                    ·
                      refine ⟨1133722152752488752195985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511629537003318336261313 1133722152752488752195985)
                      ·
                        rfl

theorem cell23_2207916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_2207916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207916 prefixEnd_2207916 := by exact prefixLift 2207916
  have htrace : WordTrace (prefixWord ++ tailWord_2207916) baseStart_2207916 baseEnd_2207916 := by
    simpa [prefixWord, tailWord_2207916, baseEnd_2207916] using wordTrace_append hprefix tailTrace_2207916
  have hstable : (prefixWord ++ tailWord_2207916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207916).length < 2 ^ (prefixWord ++ tailWord_2207916).sum := by decide
  have hdescent : baseEnd_2207916 < baseStart_2207916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207919 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_2207919 : Nat := 118140960795 + 2207919 * 2 ^ 59
def prefixEnd_2207919 : Nat := 4983230072969 + 3 ^ 40 * 2207919 * 2
def baseEnd_2207919 : Nat := 1133723693194452240458471

theorem tailTrace_2207919 : CollatzResearch.WordTrace tailWord_2207919 prefixEnd_2207919 1133723693194452240458471 := by
  unfold tailWord_2207919
  simp only [CollatzResearch.WordTrace]
  refine ⟨80529421688094020389234811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53686281125396013592823207 80529421688094020389234811)
  ·
    refine ⟨120794132532141030583852217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80529421688094020389234811 120794132532141030583852217)
    ·
      refine ⟨90595599399105772937889163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120794132532141030583852217 90595599399105772937889163)
      ·
        refine ⟨135893399098658659406833745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90595599399105772937889163 135893399098658659406833745)
        ·
          refine ⟨101920049323993994555125309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135893399098658659406833745 101920049323993994555125309)
          ·
            refine ⟨38220018496497747958171991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101920049323993994555125309 38220018496497747958171991)
            ·
              refine ⟨57330027744746621937257987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38220018496497747958171991 57330027744746621937257987)
              ·
                refine ⟨85995041617119932905886981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57330027744746621937257987 85995041617119932905886981)
                ·
                  refine ⟨16124070303209987419853809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85995041617119932905886981 16124070303209987419853809)
                  ·
                    refine ⟨12093052727407490564890357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16124070303209987419853809 12093052727407490564890357)
                    ·
                      refine ⟨1133723693194452240458471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12093052727407490564890357 1133723693194452240458471)
                      ·
                        rfl

theorem cell23_2207919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_2207919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207919 prefixEnd_2207919 := by exact prefixLift 2207919
  have htrace : WordTrace (prefixWord ++ tailWord_2207919) baseStart_2207919 baseEnd_2207919 := by
    simpa [prefixWord, tailWord_2207919, baseEnd_2207919] using wordTrace_append hprefix tailTrace_2207919
  have hstable : (prefixWord ++ tailWord_2207919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207919).length < 2 ^ (prefixWord ++ tailWord_2207919).sum := by decide
  have hdescent : baseEnd_2207919 < baseStart_2207919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207923 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 3]
def baseStart_2207923 : Nat := 118140960795 + 2207923 * 2 ^ 59
def prefixEnd_2207923 : Nat := 4983230072969 + 3 ^ 40 * 2207923 * 2
def baseEnd_2207923 : Nat := 1133725747117070224808453

theorem tailTrace_2207923 : CollatzResearch.WordTrace tailWord_2207923 prefixEnd_2207923 1133725747117070224808453 := by
  unfold tailWord_2207923
  simp only [CollatzResearch.WordTrace]
  refine ⟨80529567580079529072380423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53686378386719686048253615 80529567580079529072380423)
  ·
    refine ⟨120794351370119293608570635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80529567580079529072380423 120794351370119293608570635)
    ·
      refine ⟨181191527055178940412855953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120794351370119293608570635 181191527055178940412855953)
      ·
        refine ⟨135893645291384205309641965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181191527055178940412855953 135893645291384205309641965)
        ·
          refine ⟨50960116984269076991115737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135893645291384205309641965 50960116984269076991115737)
          ·
            refine ⟨38220087738201807743336803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50960116984269076991115737 38220087738201807743336803)
            ·
              refine ⟨57330131607302711615005205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38220087738201807743336803 57330131607302711615005205)
              ·
                refine ⟨2687349919092314606953369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57330131607302711615005205 2687349919092314606953369)
                ·
                  refine ⟨2015512439319235955215027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687349919092314606953369 2015512439319235955215027)
                  ·
                    refine ⟨3023268658978853932822541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015512439319235955215027 3023268658978853932822541)
                    ·
                      refine ⟨1133725747117070224808453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3023268658978853932822541 1133725747117070224808453)
                      ·
                        rfl

theorem cell23_2207923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_2207923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207923 prefixEnd_2207923 := by exact prefixLift 2207923
  have htrace : WordTrace (prefixWord ++ tailWord_2207923) baseStart_2207923 baseEnd_2207923 := by
    simpa [prefixWord, tailWord_2207923, baseEnd_2207923] using wordTrace_append hprefix tailTrace_2207923
  have hstable : (prefixWord ++ tailWord_2207923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207923).length < 2 ^ (prefixWord ++ tailWord_2207923).sum := by decide
  have hdescent : baseEnd_2207923 < baseStart_2207923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207933 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_2207933 : Nat := 118140960795 + 2207933 * 2 ^ 59
def prefixEnd_2207933 : Nat := 4983230072969 + 3 ^ 40 * 2207933 * 2
def baseEnd_2207933 : Nat := 1133730881923615185683407

theorem tailTrace_2207933 : CollatzResearch.WordTrace tailWord_2207933 prefixEnd_2207933 1133730881923615185683407 := by
  unfold tailWord_2207933
  simp only [CollatzResearch.WordTrace]
  refine ⟨80529932310043300780244453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53686621540028867186829635 80529932310043300780244453)
  ·
    refine ⟨15099362308133118896295835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80529932310043300780244453 15099362308133118896295835)
    ·
      refine ⟨22649043462199678344443753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15099362308133118896295835 22649043462199678344443753)
      ·
        refine ⟨16986782596649758758332815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22649043462199678344443753 16986782596649758758332815)
        ·
          refine ⟨25480173894974638137499223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16986782596649758758332815 25480173894974638137499223)
          ·
            refine ⟨38220260842461957206248835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25480173894974638137499223 38220260842461957206248835)
            ·
              refine ⟨57330391263692935809373253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38220260842461957206248835 57330391263692935809373253)
              ·
                refine ⟨10749448361942425464257485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57330391263692935809373253 10749448361942425464257485)
                ·
                  refine ⟨4031043135728409549096557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10749448361942425464257485 4031043135728409549096557)
                  ·
                    refine ⟨1511641175898153580911209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4031043135728409549096557 1511641175898153580911209)
                    ·
                      refine ⟨1133730881923615185683407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511641175898153580911209 1133730881923615185683407)
                      ·
                        rfl

theorem cell23_2207933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_2207933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207933 prefixEnd_2207933 := by exact prefixLift 2207933
  have htrace : WordTrace (prefixWord ++ tailWord_2207933) baseStart_2207933 baseEnd_2207933 := by
    simpa [prefixWord, tailWord_2207933, baseEnd_2207933] using wordTrace_append hprefix tailTrace_2207933
  have hstable : (prefixWord ++ tailWord_2207933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207933).length < 2 ^ (prefixWord ++ tailWord_2207933).sum := by decide
  have hdescent : baseEnd_2207933 < baseStart_2207933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207934 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2207934 : Nat := 118140960795 + 2207934 * 2 ^ 59
def prefixEnd_2207934 : Nat := 4983230072969 + 3 ^ 40 * 2207934 * 2
def baseEnd_2207934 : Nat := 377910465134756560590301

theorem tailTrace_2207934 : CollatzResearch.WordTrace tailWord_2207934 prefixEnd_2207934 377910465134756560590301 := by
  unfold tailWord_2207934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066246097879959743878857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53686645855359785300687237 10066246097879959743878857)
  ·
    refine ⟨7549684573409969807909143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10066246097879959743878857 7549684573409969807909143)
    ·
      refine ⟨11324526860114954711863715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7549684573409969807909143 11324526860114954711863715)
      ·
        refine ⟨16986790290172432067795573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11324526860114954711863715 16986790290172432067795573)
        ·
          refine ⟨1592511589703665506355835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16986790290172432067795573 1592511589703665506355835)
          ·
            refine ⟨2388767384555498259533753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592511589703665506355835 2388767384555498259533753)
            ·
              refine ⟨1791575538416623694650315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388767384555498259533753 1791575538416623694650315)
              ·
                refine ⟨2687363307624935541975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791575538416623694650315 2687363307624935541975473)
                ·
                  refine ⟨2015522480718701656481605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687363307624935541975473 2015522480718701656481605)
                  ·
                    refine ⟨377910465134756560590301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015522480718701656481605 377910465134756560590301)
                    ·
                      rfl

theorem cell23_2207934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2207934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207934 prefixEnd_2207934 := by exact prefixLift 2207934
  have htrace : WordTrace (prefixWord ++ tailWord_2207934) baseStart_2207934 baseEnd_2207934 := by
    simpa [prefixWord, tailWord_2207934, baseEnd_2207934] using wordTrace_append hprefix tailTrace_2207934
  have hstable : (prefixWord ++ tailWord_2207934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207934).length < 2 ^ (prefixWord ++ tailWord_2207934).sum := by decide
  have hdescent : baseEnd_2207934 < baseStart_2207934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207939 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 6, 6]
def baseStart_2207939 : Nat := 118140960795 + 2207939 * 2 ^ 59
def prefixEnd_2207939 : Nat := 4983230072969 + 3 ^ 40 * 2207939 * 2
def baseEnd_2207939 : Nat := 377911320935847387402793

theorem tailTrace_2207939 : CollatzResearch.WordTrace tailWord_2207939 prefixEnd_2207939 377911320935847387402793 := by
  unfold tailWord_2207939
  simp only [CollatzResearch.WordTrace]
  refine ⟨80530151148021563804962871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53686767432014375869975247 80530151148021563804962871)
  ·
    refine ⟨120795226722032345707444307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80530151148021563804962871 120795226722032345707444307)
    ·
      refine ⟨181192840083048518561166461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120795226722032345707444307 181192840083048518561166461)
      ·
        refine ⟨67947315031143194460437423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181192840083048518561166461 67947315031143194460437423)
        ·
          refine ⟨101920972546714791690656135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67947315031143194460437423 101920972546714791690656135)
          ·
            refine ⟨152881458820072187535984203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101920972546714791690656135 152881458820072187535984203)
            ·
              refine ⟨229322188230108281303976305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152881458820072187535984203 229322188230108281303976305)
              ·
                refine ⟨171991641172581210977982229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229322188230108281303976305 171991641172581210977982229)
                ·
                  refine ⟨8062108179964744264592917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171991641172581210977982229 8062108179964744264592917)
                  ·
                    refine ⟨377911320935847387402793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8062108179964744264592917 377911320935847387402793)
                    ·
                      rfl

theorem cell23_2207939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_2207939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207939 prefixEnd_2207939 := by exact prefixLift 2207939
  have htrace : WordTrace (prefixWord ++ tailWord_2207939) baseStart_2207939 baseEnd_2207939 := by
    simpa [prefixWord, tailWord_2207939, baseEnd_2207939] using wordTrace_append hprefix tailTrace_2207939
  have hstable : (prefixWord ++ tailWord_2207939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207939).length < 2 ^ (prefixWord ++ tailWord_2207939).sum := by decide
  have hdescent : baseEnd_2207939 < baseStart_2207939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207950 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_2207950 : Nat := 118140960795 + 2207950 * 2 ^ 59
def prefixEnd_2207950 : Nat := 4983230072969 + 3 ^ 40 * 2207950 * 2
def baseEnd_2207950 : Nat := 1133739611094741619170829

theorem tailTrace_2207950 : CollatzResearch.WordTrace tailWord_2207950 prefixEnd_2207950 1133739611094741619170829 := by
  unfold tailWord_2207950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066319043872714085451663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53687034900654475122408869 10066319043872714085451663)
  ·
    refine ⟨15099478565809071128177495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10066319043872714085451663 15099478565809071128177495)
    ·
      refine ⟨22649217848713606692266243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15099478565809071128177495 22649217848713606692266243)
      ·
        refine ⟨33973826773070410038399365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22649217848713606692266243 33973826773070410038399365)
        ·
          refine ⟨6370092519950701882199881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33973826773070410038399365 6370092519950701882199881)
          ·
            refine ⟨4777569389963026411649911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6370092519950701882199881 4777569389963026411649911)
            ·
              refine ⟨7166354084944539617474867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777569389963026411649911 7166354084944539617474867)
              ·
                refine ⟨10749531127416809426212301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7166354084944539617474867 10749531127416809426212301)
                ·
                  refine ⟨4031074172781303534829613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10749531127416809426212301 4031074172781303534829613)
                  ·
                    refine ⟨1511652814792988825561105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4031074172781303534829613 1511652814792988825561105)
                    ·
                      refine ⟨1133739611094741619170829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511652814792988825561105 1133739611094741619170829)
                      ·
                        rfl

theorem cell23_2207950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_2207950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2207950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2207950 prefixEnd_2207950 := by exact prefixLift 2207950
  have htrace : WordTrace (prefixWord ++ tailWord_2207950) baseStart_2207950 baseEnd_2207950 := by
    simpa [prefixWord, tailWord_2207950, baseEnd_2207950] using wordTrace_append hprefix tailTrace_2207950
  have hstable : (prefixWord ++ tailWord_2207950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207950).length < 2 ^ (prefixWord ++ tailWord_2207950).sum := by decide
  have hdescent : baseEnd_2207950 < baseStart_2207950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208063 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 3, 4]
def baseStart_2208063 : Nat := 118140960795 + 2208063 * 2 ^ 59
def prefixEnd_2208063 : Nat := 4983230072969 + 3 ^ 40 * 2208063 * 2
def baseEnd_2208063 : Nat := 377932544802899892352603

theorem tailTrace_2208063 : CollatzResearch.WordTrace tailWord_2208063 prefixEnd_2208063 377932544802899892352603 := by
  unfold tailWord_2208063
  simp only [CollatzResearch.WordTrace]
  refine ⟨80534673799572332982476843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53689782533048221988317895 80534673799572332982476843)
  ·
    refine ⟨120802010699358499473715265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80534673799572332982476843 120802010699358499473715265)
    ·
      refine ⟨90601508024518874605286449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120802010699358499473715265 90601508024518874605286449)
      ·
        refine ⟨67951131018389155953964837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90601508024518874605286449 67951131018389155953964837)
        ·
          refine ⟨12740837065947966741368407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67951131018389155953964837 12740837065947966741368407)
          ·
            refine ⟨19111255598921950112052611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12740837065947966741368407 19111255598921950112052611)
            ·
              refine ⟨28666883398382925168078917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19111255598921950112052611 28666883398382925168078917)
              ·
                refine ⟨5375040637196798469014797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28666883398382925168078917 5375040637196798469014797)
                ·
                  refine ⟨2015640238948799425880549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5375040637196798469014797 2015640238948799425880549)
                  ·
                    refine ⟨377932544802899892352603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015640238948799425880549 377932544802899892352603)
                    ·
                      rfl

theorem cell23_2208063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_2208063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208063 prefixEnd_2208063 := by exact prefixLift 2208063
  have htrace : WordTrace (prefixWord ++ tailWord_2208063) baseStart_2208063 baseEnd_2208063 := by
    simpa [prefixWord, tailWord_2208063, baseEnd_2208063] using wordTrace_append hprefix tailTrace_2208063
  have hstable : (prefixWord ++ tailWord_2208063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208063).length < 2 ^ (prefixWord ++ tailWord_2208063).sum := by decide
  have hdescent : baseEnd_2208063 < baseStart_2208063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208073 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_2208073 : Nat := 118140960795 + 2208073 * 2 ^ 59
def prefixEnd_2208073 : Nat := 4983230072969 + 3 ^ 40 * 2208073 * 2
def baseEnd_2208073 : Nat := 1133802769215244637932763

theorem tailTrace_2208073 : CollatzResearch.WordTrace tailWord_2208073 prefixEnd_2208073 1133802769215244637932763 := by
  unfold tailWord_2208073
  simp only [CollatzResearch.WordTrace]
  refine ⟨80535038529536104690340873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53690025686357403126893915 80535038529536104690340873)
  ·
    refine ⟨60401278897152078517755655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80535038529536104690340873 60401278897152078517755655)
    ·
      refine ⟨90601918345728117776633483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60401278897152078517755655 90601918345728117776633483)
      ·
        refine ⟨135902877518592176664950225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90601918345728117776633483 135902877518592176664950225)
        ·
          refine ⟨101927158138944132498712669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135902877518592176664950225 101927158138944132498712669)
          ·
            refine ⟨38222684302104049687017251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101927158138944132498712669 38222684302104049687017251)
            ·
              refine ⟨57334026453156074530525877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38222684302104049687017251 57334026453156074530525877)
              ·
                refine ⟨5375064979983381987236801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57334026453156074530525877 5375064979983381987236801)
                ·
                  refine ⟨4031298734987536490427601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375064979983381987236801 4031298734987536490427601)
                  ·
                    refine ⟨3023474051240652367820701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4031298734987536490427601 3023474051240652367820701)
                    ·
                      refine ⟨1133802769215244637932763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3023474051240652367820701 1133802769215244637932763)
                      ·
                        rfl

theorem cell23_2208073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_2208073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208073 prefixEnd_2208073 := by exact prefixLift 2208073
  have htrace : WordTrace (prefixWord ++ tailWord_2208073) baseStart_2208073 baseEnd_2208073 := by
    simpa [prefixWord, tailWord_2208073, baseEnd_2208073] using wordTrace_append hprefix tailTrace_2208073
  have hstable : (prefixWord ++ tailWord_2208073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208073).length < 2 ^ (prefixWord ++ tailWord_2208073).sum := by decide
  have hdescent : baseEnd_2208073 < baseStart_2208073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208076 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 10]
def baseStart_2208076 : Nat := 118140960795 + 2208076 * 2 ^ 59
def prefixEnd_2208076 : Nat := 4983230072969 + 3 ^ 40 * 2208076 * 2
def baseEnd_2208076 : Nat := 125978256628578680688361

theorem tailTrace_2208076 : CollatzResearch.WordTrace tailWord_2208076 prefixEnd_2208076 125978256628578680688361 := by
  unfold tailWord_2208076
  simp only [CollatzResearch.WordTrace]
  refine ⟨40267573974262618101350041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53690098632350157468466721 40267573974262618101350041)
  ·
    refine ⟨30200680480696963576012531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40267573974262618101350041 30200680480696963576012531)
    ·
      refine ⟨45301020721045445364018797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30200680480696963576012531 45301020721045445364018797)
      ·
        refine ⟨16987882770392042011507049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45301020721045445364018797 16987882770392042011507049)
        ·
          refine ⟨12740912077794031508630287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16987882770392042011507049 12740912077794031508630287)
          ·
            refine ⟨19111368116691047262945431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12740912077794031508630287 19111368116691047262945431)
            ·
              refine ⟨28667052175036570894418147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19111368116691047262945431 28667052175036570894418147)
              ·
                refine ⟨43000578262554856341627221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28667052175036570894418147 43000578262554856341627221)
                ·
                  refine ⟨125978256628578680688361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43000578262554856341627221 125978256628578680688361)
                  ·
                    rfl

theorem cell23_2208076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_2208076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208076 prefixEnd_2208076 := by exact prefixLift 2208076
  have htrace : WordTrace (prefixWord ++ tailWord_2208076) baseStart_2208076 baseEnd_2208076 := by
    simpa [prefixWord, tailWord_2208076, baseEnd_2208076] using wordTrace_append hprefix tailTrace_2208076
  have hstable : (prefixWord ++ tailWord_2208076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208076).length < 2 ^ (prefixWord ++ tailWord_2208076).sum := by decide
  have hdescent : baseEnd_2208076 < baseStart_2208076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208123 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 3, 5]
def baseStart_2208123 : Nat := 118140960795 + 2208123 * 2 ^ 59
def prefixEnd_2208123 : Nat := 4983230072969 + 3 ^ 40 * 2208123 * 2
def baseEnd_2208123 : Nat := 377942814415989814102511

theorem tailTrace_2208123 : CollatzResearch.WordTrace tailWord_2208123 prefixEnd_2208123 377942814415989814102511 := by
  unfold tailWord_2208123
  simp only [CollatzResearch.WordTrace]
  refine ⟨80536862179354963229661023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53691241452903308819774015 80536862179354963229661023)
  ·
    refine ⟨120805293269032444844491535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80536862179354963229661023 120805293269032444844491535)
    ·
      refine ⟨181207939903548667266737303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120805293269032444844491535 181207939903548667266737303)
      ·
        refine ⟨271811909855323000900105955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181207939903548667266737303 271811909855323000900105955)
        ·
          refine ⟨407717864782984501350158933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271811909855323000900105955 407717864782984501350158933)
          ·
            refine ⟨4777943727925599625197175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 407717864782984501350158933 4777943727925599625197175)
            ·
              refine ⟨7166915591888399437795763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777943727925599625197175 7166915591888399437795763)
              ·
                refine ⟨10750373387832599156693645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7166915591888399437795763 10750373387832599156693645)
                ·
                  refine ⟨4031390020437224683760117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10750373387832599156693645 4031390020437224683760117)
                  ·
                    refine ⟨377942814415989814102511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4031390020437224683760117 377942814415989814102511)
                    ·
                      rfl

theorem cell23_2208123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 5].length) (baseStart_2208123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208123 prefixEnd_2208123 := by exact prefixLift 2208123
  have htrace : WordTrace (prefixWord ++ tailWord_2208123) baseStart_2208123 baseEnd_2208123 := by
    simpa [prefixWord, tailWord_2208123, baseEnd_2208123] using wordTrace_append hprefix tailTrace_2208123
  have hstable : (prefixWord ++ tailWord_2208123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208123).length < 2 ^ (prefixWord ++ tailWord_2208123).sum := by decide
  have hdescent : baseEnd_2208123 < baseStart_2208123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208148 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2208148 : Nat := 118140960795 + 2208148 * 2 ^ 59
def prefixEnd_2208148 : Nat := 4983230072969 + 3 ^ 40 * 2208148 * 2
def baseEnd_2208148 : Nat := 377947093421443948164973

theorem tailTrace_2208148 : CollatzResearch.WordTrace tailWord_2208148 prefixEnd_2208148 377947093421443948164973 := by
  unfold tailWord_2208148
  simp only [CollatzResearch.WordTrace]
  refine ⟨40268887002132196249660549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53691849336176261666214065 40268887002132196249660549)
  ·
    refine ⟨7550416312899786796811353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40268887002132196249660549 7550416312899786796811353)
    ·
      refine ⟨5662812234674840097608515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7550416312899786796811353 5662812234674840097608515)
      ·
        refine ⟨8494218352012260146412773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5662812234674840097608515 8494218352012260146412773)
        ·
          refine ⟨1592665941002298777452395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8494218352012260146412773 1592665941002298777452395)
          ·
            refine ⟨2388998911503448166178593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592665941002298777452395 2388998911503448166178593)
            ·
              refine ⟨1791749183627586124633945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388998911503448166178593 1791749183627586124633945)
              ·
                refine ⟨1343811887720689593475459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791749183627586124633945 1343811887720689593475459)
                ·
                  refine ⟨2015717831581034390213189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343811887720689593475459 2015717831581034390213189)
                  ·
                    refine ⟨377947093421443948164973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015717831581034390213189 377947093421443948164973)
                    ·
                      rfl

theorem cell23_2208148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2208148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208148 prefixEnd_2208148 := by exact prefixLift 2208148
  have htrace : WordTrace (prefixWord ++ tailWord_2208148) baseStart_2208148 baseEnd_2208148 := by
    simpa [prefixWord, tailWord_2208148, baseEnd_2208148] using wordTrace_append hprefix tailTrace_2208148
  have hstable : (prefixWord ++ tailWord_2208148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208148).length < 2 ^ (prefixWord ++ tailWord_2208148).sum := by decide
  have hdescent : baseEnd_2208148 < baseStart_2208148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208154 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3]
def baseStart_2208154 : Nat := 118140960795 + 2208154 * 2 ^ 59
def prefixEnd_2208154 : Nat := 4983230072969 + 3 ^ 40 * 2208154 * 2
def baseEnd_2208154 : Nat := 1133844361148258821019891

theorem tailTrace_2208154 : CollatzResearch.WordTrace tailWord_2208154 prefixEnd_2208154 1133844361148258821019891 := by
  unfold tailWord_2208154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134498210560663881009879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53691995228161770349359677 20134498210560663881009879)
  ·
    refine ⟨30201747315840995821514819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20134498210560663881009879 30201747315840995821514819)
    ·
      refine ⟨45302620973761493732272229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30201747315840995821514819 45302620973761493732272229)
      ·
        refine ⟨8494241432580280074801043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45302620973761493732272229 8494241432580280074801043)
        ·
          refine ⟨12741362148870420112201565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8494241432580280074801043 12741362148870420112201565)
          ·
            refine ⟨4778010805826407542075587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12741362148870420112201565 4778010805826407542075587)
            ·
              refine ⟨7167016208739611313113381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778010805826407542075587 7167016208739611313113381)
              ·
                refine ⟨1343815539138677121208759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7167016208739611313113381 1343815539138677121208759)
                ·
                  refine ⟨2015723308708015681813139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343815539138677121208759 2015723308708015681813139)
                  ·
                    refine ⟨3023584963062023522719709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015723308708015681813139 3023584963062023522719709)
                    ·
                      refine ⟨1133844361148258821019891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3023584963062023522719709 1133844361148258821019891)
                      ·
                        rfl

theorem cell23_2208154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_2208154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208154 prefixEnd_2208154 := by exact prefixLift 2208154
  have htrace : WordTrace (prefixWord ++ tailWord_2208154) baseStart_2208154 baseEnd_2208154 := by
    simpa [prefixWord, tailWord_2208154, baseEnd_2208154] using wordTrace_append hprefix tailTrace_2208154
  have hstable : (prefixWord ++ tailWord_2208154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208154).length < 2 ^ (prefixWord ++ tailWord_2208154).sum := by decide
  have hdescent : baseEnd_2208154 < baseStart_2208154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208177 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2208177 : Nat := 118140960795 + 2208177 * 2 ^ 59
def prefixEnd_2208177 : Nat := 4983230072969 + 3 ^ 40 * 2208177 * 2
def baseEnd_2208177 : Nat := 1133856171203312231032285

theorem tailTrace_2208177 : CollatzResearch.WordTrace tailWord_2208177 prefixEnd_2208177 1133856171203312231032285 := by
  unfold tailWord_2208177
  simp only [CollatzResearch.WordTrace]
  refine ⟨80538831721159330452126785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53692554480772886968084523 80538831721159330452126785)
  ·
    refine ⟨60404123790869497839095089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80538831721159330452126785 60404123790869497839095089)
    ·
      refine ⟨45303092843152123379321317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60404123790869497839095089 45303092843152123379321317)
      ·
        refine ⟨8494329908091023133622747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45303092843152123379321317 8494329908091023133622747)
        ·
          refine ⟨12741494862136534700434121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8494329908091023133622747 12741494862136534700434121)
          ·
            refine ⟨9556121146602401025325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12741494862136534700434121 9556121146602401025325591)
            ·
              refine ⟨14334181719903601537988387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9556121146602401025325591 14334181719903601537988387)
              ·
                refine ⟨21501272579855402306982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14334181719903601537988387 21501272579855402306982581)
                ·
                  refine ⟨2015744304361443966279617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21501272579855402306982581 2015744304361443966279617)
                  ·
                    refine ⟨1511808228271082974709713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015744304361443966279617 1511808228271082974709713)
                    ·
                      refine ⟨1133856171203312231032285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511808228271082974709713 1133856171203312231032285)
                      ·
                        rfl

theorem cell23_2208177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2208177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208177 prefixEnd_2208177 := by exact prefixLift 2208177
  have htrace : WordTrace (prefixWord ++ tailWord_2208177) baseStart_2208177 baseEnd_2208177 := by
    simpa [prefixWord, tailWord_2208177, baseEnd_2208177] using wordTrace_append hprefix tailTrace_2208177
  have hstable : (prefixWord ++ tailWord_2208177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208177).length < 2 ^ (prefixWord ++ tailWord_2208177).sum := by decide
  have hdescent : baseEnd_2208177 < baseStart_2208177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208181 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_2208181 : Nat := 118140960795 + 2208181 * 2 ^ 59
def prefixEnd_2208181 : Nat := 4983230072969 + 3 ^ 40 * 2208181 * 2
def baseEnd_2208181 : Nat := 1133858225125930215382267

theorem tailTrace_2208181 : CollatzResearch.WordTrace tailWord_2208181 prefixEnd_2208181 1133858225125930215382267 := by
  unfold tailWord_2208181
  simp only [CollatzResearch.WordTrace]
  refine ⟨80538977613144839135272397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53692651742096559423514931 80538977613144839135272397)
  ·
    refine ⟨30202116604929314675727149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80538977613144839135272397 30202116604929314675727149)
    ·
      refine ⟨11325793726848493003397681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30202116604929314675727149 11325793726848493003397681)
      ·
        refine ⟨8494345295136369752548261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11325793726848493003397681 8494345295136369752548261)
        ·
          refine ⟨1592689742838069328602799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8494345295136369752548261 1592689742838069328602799)
          ·
            refine ⟨2389034614257103992904199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592689742838069328602799 2389034614257103992904199)
            ·
              refine ⟨3583551921385655989356299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389034614257103992904199 3583551921385655989356299)
              ·
                refine ⟨5375327882078483984034449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583551921385655989356299 5375327882078483984034449)
                ·
                  refine ⟨4031495911558862988025837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375327882078483984034449 4031495911558862988025837)
                  ·
                    refine ⟨1511810966834573620509689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4031495911558862988025837 1511810966834573620509689)
                    ·
                      refine ⟨1133858225125930215382267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511810966834573620509689 1133858225125930215382267)
                      ·
                        rfl

theorem cell23_2208181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_2208181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208181 prefixEnd_2208181 := by exact prefixLift 2208181
  have htrace : WordTrace (prefixWord ++ tailWord_2208181) baseStart_2208181 baseEnd_2208181 := by
    simpa [prefixWord, tailWord_2208181, baseEnd_2208181] using wordTrace_append hprefix tailTrace_2208181
  have hstable : (prefixWord ++ tailWord_2208181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208181).length < 2 ^ (prefixWord ++ tailWord_2208181).sum := by decide
  have hdescent : baseEnd_2208181 < baseStart_2208181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208190 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2208190 : Nat := 118140960795 + 2208190 * 2 ^ 59
def prefixEnd_2208190 : Nat := 4983230072969 + 3 ^ 40 * 2208190 * 2
def baseEnd_2208190 : Nat := 1133862846451820680169725

theorem tailTrace_2208190 : CollatzResearch.WordTrace tailWord_2208190 prefixEnd_2208190 1133862846451820680169725 := by
  unfold tailWord_2208190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10067413233764029209043753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53692870580074822448233349 10067413233764029209043753)
  ·
    refine ⟨7550559925323021906782815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10067413233764029209043753 7550559925323021906782815)
    ·
      refine ⟨11325839887984532860174223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7550559925323021906782815 11325839887984532860174223)
      ·
        refine ⟨16988759831976799290261335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11325839887984532860174223 16988759831976799290261335)
        ·
          refine ⟨25483139747965198935392003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16988759831976799290261335 25483139747965198935392003)
          ·
            refine ⟨38224709621947798403088005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25483139747965198935392003 38224709621947798403088005)
            ·
              refine ⟨7167133054115212200579001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38224709621947798403088005 7167133054115212200579001)
              ·
                refine ⟨5375349790586409150434251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7167133054115212200579001 5375349790586409150434251)
                ·
                  refine ⟨8063024685879613725651377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5375349790586409150434251 8063024685879613725651377)
                  ·
                    refine ⟨6047268514409710294238533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8063024685879613725651377 6047268514409710294238533)
                    ·
                      refine ⟨1133862846451820680169725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6047268514409710294238533 1133862846451820680169725)
                      ·
                        rfl

theorem cell23_2208190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2208190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208190 prefixEnd_2208190 := by exact prefixLift 2208190
  have htrace : WordTrace (prefixWord ++ tailWord_2208190) baseStart_2208190 baseEnd_2208190 := by
    simpa [prefixWord, tailWord_2208190, baseEnd_2208190] using wordTrace_append hprefix tailTrace_2208190
  have hstable : (prefixWord ++ tailWord_2208190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208190).length < 2 ^ (prefixWord ++ tailWord_2208190).sum := by decide
  have hdescent : baseEnd_2208190 < baseStart_2208190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208204 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_2208204 : Nat := 118140960795 + 2208204 * 2 ^ 59
def prefixEnd_2208204 : Nat := 4983230072969 + 3 ^ 40 * 2208204 * 2
def baseEnd_2208204 : Nat := 377956678393661208464887

theorem tailTrace_2208204 : CollatzResearch.WordTrace tailWord_2208204 prefixEnd_2208204 377956678393661208464887 := by
  unfold tailWord_2208204
  simp only [CollatzResearch.WordTrace]
  refine ⟨40269908246030757031679833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53693210994707676042239777 40269908246030757031679833)
  ·
    refine ⟨30202431184523067773759875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40269908246030757031679833 30202431184523067773759875)
    ·
      refine ⟨45303646776784601660639813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30202431184523067773759875 45303646776784601660639813)
      ·
        refine ⟨8494433770647112811369965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45303646776784601660639813 8494433770647112811369965)
        ·
          refine ⟨3185412663992667304263737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8494433770647112811369965 3185412663992667304263737)
          ·
            refine ⟨2389059497994500478197803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3185412663992667304263737 2389059497994500478197803)
            ·
              refine ⟨3583589246991750717296705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389059497994500478197803 3583589246991750717296705)
              ·
                refine ⟨2687691935243813037972529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583589246991750717296705 2687691935243813037972529)
                ·
                  refine ⟨2015768951432859778479397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687691935243813037972529 2015768951432859778479397)
                  ·
                    refine ⟨377956678393661208464887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015768951432859778479397 377956678393661208464887)
                    ·
                      rfl

theorem cell23_2208204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_2208204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208204 prefixEnd_2208204 := by exact prefixLift 2208204
  have htrace : WordTrace (prefixWord ++ tailWord_2208204) baseStart_2208204 baseEnd_2208204 := by
    simpa [prefixWord, tailWord_2208204, baseEnd_2208204] using wordTrace_append hprefix tailTrace_2208204
  have hstable : (prefixWord ++ tailWord_2208204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208204).length < 2 ^ (prefixWord ++ tailWord_2208204).sum := by decide
  have hdescent : baseEnd_2208204 < baseStart_2208204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208245 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2208245 : Nat := 118140960795 + 2208245 * 2 ^ 59
def prefixEnd_2208245 : Nat := 4983230072969 + 3 ^ 40 * 2208245 * 2
def baseEnd_2208245 : Nat := 1133891087887817964981973

theorem tailTrace_2208245 : CollatzResearch.WordTrace tailWord_2208245 prefixEnd_2208245 1133891087887817964981973 := by
  unfold tailWord_2208245
  simp only [CollatzResearch.WordTrace]
  refine ⟨80541311884912978065602189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53694207923275318710401459 80541311884912978065602189)
  ·
    refine ⟨30202991956842366774600821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80541311884912978065602189 30202991956842366774600821)
    ·
      refine ⟨2831530495953971885118827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30202991956842366774600821 2831530495953971885118827)
      ·
        refine ⟨4247295743930957827678241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831530495953971885118827 4247295743930957827678241)
        ·
          refine ⟨3185471807948218370758681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247295743930957827678241 3185471807948218370758681)
          ·
            refine ⟨2389103855961163778069011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3185471807948218370758681 2389103855961163778069011)
            ·
              refine ⟨3583655783941745667103517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389103855961163778069011 3583655783941745667103517)
              ·
                refine ⟨1343870918978154625163819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3583655783941745667103517 1343870918978154625163819)
                ·
                  refine ⟨2015806378467231937745729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343870918978154625163819 2015806378467231937745729)
                  ·
                    refine ⟨1511854783850423953309297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015806378467231937745729 1511854783850423953309297)
                    ·
                      refine ⟨1133891087887817964981973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511854783850423953309297 1133891087887817964981973)
                      ·
                        rfl

theorem cell23_2208245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2208245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208245 prefixEnd_2208245 := by exact prefixLift 2208245
  have htrace : WordTrace (prefixWord ++ tailWord_2208245) baseStart_2208245 baseEnd_2208245 := by
    simpa [prefixWord, tailWord_2208245, baseEnd_2208245] using wordTrace_append hprefix tailTrace_2208245
  have hstable : (prefixWord ++ tailWord_2208245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208245).length < 2 ^ (prefixWord ++ tailWord_2208245).sum := by decide
  have hdescent : baseEnd_2208245 < baseStart_2208245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208273 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 7]
def baseStart_2208273 : Nat := 118140960795 + 2208273 * 2 ^ 59
def prefixEnd_2208273 : Nat := 4983230072969 + 3 ^ 40 * 2208273 * 2
def baseEnd_2208273 : Nat := 125989496149571539492427

theorem tailTrace_2208273 : CollatzResearch.WordTrace tailWord_2208273 prefixEnd_2208273 125989496149571539492427 := by
  unfold tailWord_2208273
  simp only [CollatzResearch.WordTrace]
  refine ⟨80542333128811538847621473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53694888752541025898414315 80542333128811538847621473)
  ·
    refine ⟨60406749846608654135716105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80542333128811538847621473 60406749846608654135716105)
    ·
      refine ⟨45305062384956490601787079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60406749846608654135716105 45305062384956490601787079)
      ·
        refine ⟨67957593577434735902680619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45305062384956490601787079 67957593577434735902680619)
        ·
          refine ⟨101936390366152103854020929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67957593577434735902680619 101936390366152103854020929)
          ·
            refine ⟨76452292774614077890515697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101936390366152103854020929 76452292774614077890515697)
            ·
              refine ⟨57339219580960558417886773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76452292774614077890515697 57339219580960558417886773)
              ·
                refine ⟨5375551835715052351676885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57339219580960558417886773 5375551835715052351676885)
                ·
                  refine ⟨125989496149571539492427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5375551835715052351676885 125989496149571539492427)
                  ·
                    rfl

theorem cell23_2208273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_2208273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208273 prefixEnd_2208273 := by exact prefixLift 2208273
  have htrace : WordTrace (prefixWord ++ tailWord_2208273) baseStart_2208273 baseEnd_2208273 := by
    simpa [prefixWord, tailWord_2208273, baseEnd_2208273] using wordTrace_append hprefix tailTrace_2208273
  have hstable : (prefixWord ++ tailWord_2208273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208273).length < 2 ^ (prefixWord ++ tailWord_2208273).sum := by decide
  have hdescent : baseEnd_2208273 < baseStart_2208273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208288 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2208288 : Nat := 118140960795 + 2208288 * 2 ^ 59
def prefixEnd_2208288 : Nat := 4983230072969 + 3 ^ 40 * 2208288 * 2
def baseEnd_2208288 : Nat := 1133913167555961296744275

theorem tailTrace_2208288 : CollatzResearch.WordTrace tailWord_2208288 prefixEnd_2208288 1133913167555961296744275 := by
  unfold tailWord_2208288
  simp only [CollatzResearch.WordTrace]
  refine ⟨40271440111878598204708759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53695253482504797606278345 40271440111878598204708759)
  ·
    refine ⟨60407160167817897307063139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40271440111878598204708759 60407160167817897307063139)
    ·
      refine ⟨90610740251726845960594709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60407160167817897307063139 90610740251726845960594709)
      ·
        refine ⟨4247378449299695904402877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90610740251726845960594709 4247378449299695904402877)
        ·
          refine ⟨1592766918487385964151079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4247378449299695904402877 1592766918487385964151079)
          ·
            refine ⟨2389150377731078946226619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592766918487385964151079 2389150377731078946226619)
            ·
              refine ⟨3583725566596618419339929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389150377731078946226619 3583725566596618419339929)
              ·
                refine ⟨2687794174947463814504947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583725566596618419339929 2687794174947463814504947)
                ·
                  refine ⟨4031691262421195721757421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687794174947463814504947 4031691262421195721757421)
                  ·
                    refine ⟨1511884223407948395659033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4031691262421195721757421 1511884223407948395659033)
                    ·
                      refine ⟨1133913167555961296744275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511884223407948395659033 1133913167555961296744275)
                      ·
                        rfl

theorem cell23_2208288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2208288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208288 prefixEnd_2208288 := by exact prefixLift 2208288
  have htrace : WordTrace (prefixWord ++ tailWord_2208288) baseStart_2208288 baseEnd_2208288 := by
    simpa [prefixWord, tailWord_2208288, baseEnd_2208288] using wordTrace_append hprefix tailTrace_2208288
  have hstable : (prefixWord ++ tailWord_2208288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208288).length < 2 ^ (prefixWord ++ tailWord_2208288).sum := by decide
  have hdescent : baseEnd_2208288 < baseStart_2208288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208320 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_2208320 : Nat := 118140960795 + 2208320 * 2 ^ 59
def prefixEnd_2208320 : Nat := 4983230072969 + 3 ^ 40 * 2208320 * 2
def baseEnd_2208320 : Nat := 377976532978968390514709

theorem tailTrace_2208320 : CollatzResearch.WordTrace tailWord_2208320 prefixEnd_2208320 377976532978968390514709 := by
  unfold tailWord_2208320
  simp only [CollatzResearch.WordTrace]
  refine ⟨40272023679820632937291207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53696031573094177249721609 40272023679820632937291207)
  ·
    refine ⟨60408035519730949405936811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40272023679820632937291207 60408035519730949405936811)
    ·
      refine ⟨90612053279596424108905217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60408035519730949405936811 90612053279596424108905217)
      ·
        refine ⟨67959039959697318081678913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90612053279596424108905217 67959039959697318081678913)
        ·
          refine ⟨50969279969772988561259185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67959039959697318081678913 50969279969772988561259185)
          ·
            refine ⟨38226959977329741420944389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50969279969772988561259185 38226959977329741420944389)
            ·
              refine ⟨7167554995749326516427073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38226959977329741420944389 7167554995749326516427073)
              ·
                refine ⟨5375666246811994887320305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7167554995749326516427073 5375666246811994887320305)
                ·
                  refine ⟨4031749685108996165490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375666246811994887320305 4031749685108996165490229)
                  ·
                    refine ⟨377976532978968390514709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4031749685108996165490229 377976532978968390514709)
                    ·
                      rfl

theorem cell23_2208320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_2208320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208320 prefixEnd_2208320 := by exact prefixLift 2208320
  have htrace : WordTrace (prefixWord ++ tailWord_2208320) baseStart_2208320 baseEnd_2208320 := by
    simpa [prefixWord, tailWord_2208320, baseEnd_2208320] using wordTrace_append hprefix tailTrace_2208320
  have hstable : (prefixWord ++ tailWord_2208320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208320).length < 2 ^ (prefixWord ++ tailWord_2208320).sum := by decide
  have hdescent : baseEnd_2208320 < baseStart_2208320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208327 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_2208327 : Nat := 118140960795 + 2208327 * 2 ^ 59
def prefixEnd_2208327 : Nat := 4983230072969 + 3 ^ 40 * 2208327 * 2
def baseEnd_2208327 : Nat := 1133933193301486644156595

theorem tailTrace_2208327 : CollatzResearch.WordTrace tailWord_2208327 prefixEnd_2208327 1133933193301486644156595 := by
  unfold tailWord_2208327
  simp only [CollatzResearch.WordTrace]
  refine ⟨80544302670615906070087235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53696201780410604046724823 80544302670615906070087235)
  ·
    refine ⟨120816454005923859105130853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80544302670615906070087235 120816454005923859105130853)
    ·
      refine ⟨22653085126110723582212035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120816454005923859105130853 22653085126110723582212035)
      ·
        refine ⟨33979627689166085373318053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22653085126110723582212035 33979627689166085373318053)
        ·
          refine ⟨6371180191718641007497135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33979627689166085373318053 6371180191718641007497135)
          ·
            refine ⟨9556770287577961511245703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6371180191718641007497135 9556770287577961511245703)
            ·
              refine ⟨14335155431366942266868555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9556770287577961511245703 14335155431366942266868555)
              ·
                refine ⟨21502733147050413400302833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14335155431366942266868555 21502733147050413400302833)
                ·
                  refine ⟨16127049860287810050227125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21502733147050413400302833 16127049860287810050227125)
                  ·
                    refine ⟨1511910924401982192208793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16127049860287810050227125 1511910924401982192208793)
                    ·
                      refine ⟨1133933193301486644156595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1511910924401982192208793 1133933193301486644156595)
                      ·
                        rfl

theorem cell23_2208327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_2208327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208327 prefixEnd_2208327 := by exact prefixLift 2208327
  have htrace : WordTrace (prefixWord ++ tailWord_2208327) baseStart_2208327 baseEnd_2208327 := by
    simpa [prefixWord, tailWord_2208327, baseEnd_2208327] using wordTrace_append hprefix tailTrace_2208327
  have hstable : (prefixWord ++ tailWord_2208327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208327).length < 2 ^ (prefixWord ++ tailWord_2208327).sum := by decide
  have hdescent : baseEnd_2208327 < baseStart_2208327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208330 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2208330 : Nat := 118140960795 + 2208330 * 2 ^ 59
def prefixEnd_2208330 : Nat := 4983230072969 + 3 ^ 40 * 2208330 * 2
def baseEnd_2208330 : Nat := 1133934733743450132419081

theorem tailTrace_2208330 : CollatzResearch.WordTrace tailWord_2208330 prefixEnd_2208330 1133934733743450132419081 := by
  unfold tailWord_2208330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20136103022401259395611611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53696274726403358388297629 20136103022401259395611611)
  ·
    refine ⟨30204154533601889093417417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20136103022401259395611611 30204154533601889093417417)
    ·
      refine ⟨22653115900201416820063063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30204154533601889093417417 22653115900201416820063063)
      ·
        refine ⟨33979673850302125230094595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22653115900201416820063063 33979673850302125230094595)
        ·
          refine ⟨50969510775453187845141893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33979673850302125230094595 50969510775453187845141893)
          ·
            refine ⟨9556783270397472720964105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50969510775453187845141893 9556783270397472720964105)
            ·
              refine ⟨7167587452798104540723079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9556783270397472720964105 7167587452798104540723079)
              ·
                refine ⟨10751381179197156811084619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167587452798104540723079 10751381179197156811084619)
                ·
                  refine ⟨16127071768795735216626929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10751381179197156811084619 16127071768795735216626929)
                  ·
                    refine ⟨12095303826596801412470197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16127071768795735216626929 12095303826596801412470197)
                    ·
                      refine ⟨1133934733743450132419081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12095303826596801412470197 1133934733743450132419081)
                      ·
                        rfl

theorem cell23_2208330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2208330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208330 prefixEnd_2208330 := by exact prefixLift 2208330
  have htrace : WordTrace (prefixWord ++ tailWord_2208330) baseStart_2208330 baseEnd_2208330 := by
    simpa [prefixWord, tailWord_2208330, baseEnd_2208330] using wordTrace_append hprefix tailTrace_2208330
  have hstable : (prefixWord ++ tailWord_2208330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208330).length < 2 ^ (prefixWord ++ tailWord_2208330).sum := by decide
  have hdescent : baseEnd_2208330 < baseStart_2208330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208354 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2208354 : Nat := 118140960795 + 2208354 * 2 ^ 59
def prefixEnd_2208354 : Nat := 4983230072969 + 3 ^ 40 * 2208354 * 2
def baseEnd_2208354 : Nat := 377982352426386012839657

theorem tailTrace_2208354 : CollatzResearch.WordTrace tailWord_2208354 prefixEnd_2208354 377982352426386012839657 := by
  unfold tailWord_2208354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20136321860379522420330029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53696858294345393120880077 20136321860379522420330029)
  ·
    refine ⟨7551120697642320907623761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20136321860379522420330029 7551120697642320907623761)
    ·
      refine ⟨5663340523231740680717821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7551120697642320907623761 5663340523231740680717821)
      ·
        refine ⟨2123752696211902755269183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5663340523231740680717821 2123752696211902755269183)
        ·
          refine ⟨3185629044317854132903775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123752696211902755269183 3185629044317854132903775)
          ·
            refine ⟨4778443566476781199355663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185629044317854132903775 4778443566476781199355663)
            ·
              refine ⟨7167665349715171799033495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778443566476781199355663 7167665349715171799033495)
              ·
                refine ⟨10751498024572757698550243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167665349715171799033495 10751498024572757698550243)
                ·
                  refine ⟨16127247036859136547825365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10751498024572757698550243 16127247036859136547825365)
                  ·
                    refine ⟨377982352426386012839657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16127247036859136547825365 377982352426386012839657)
                    ·
                      rfl

theorem cell23_2208354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2208354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208354 prefixEnd_2208354 := by exact prefixLift 2208354
  have htrace : WordTrace (prefixWord ++ tailWord_2208354) baseStart_2208354 baseEnd_2208354 := by
    simpa [prefixWord, tailWord_2208354, baseEnd_2208354] using wordTrace_append hprefix tailTrace_2208354
  have hstable : (prefixWord ++ tailWord_2208354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208354).length < 2 ^ (prefixWord ++ tailWord_2208354).sum := by decide
  have hdescent : baseEnd_2208354 < baseStart_2208354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208357 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_2208357 : Nat := 118140960795 + 2208357 * 2 ^ 59
def prefixEnd_2208357 : Nat := 4983230072969 + 3 ^ 40 * 2208357 * 2
def baseEnd_2208357 : Nat := 1133948597721121526781457

theorem tailTrace_2208357 : CollatzResearch.WordTrace tailWord_2208357 prefixEnd_2208357 1133948597721121526781457 := by
  unfold tailWord_2208357
  simp only [CollatzResearch.WordTrace]
  refine ⟨80545396860507221193679325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53696931240338147462452883 80545396860507221193679325)
  ·
    refine ⟨30204523822690207947629747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80545396860507221193679325 30204523822690207947629747)
    ·
      refine ⟨45306785734035311921444621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30204523822690207947629747 45306785734035311921444621)
      ·
        refine ⟨16990044650263241970541733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45306785734035311921444621 16990044650263241970541733)
        ·
          refine ⟨3185633371924357869476575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16990044650263241970541733 3185633371924357869476575)
          ·
            refine ⟨4778450057886536804214863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185633371924357869476575 4778450057886536804214863)
            ·
              refine ⟨7167675086829805206322295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778450057886536804214863 7167675086829805206322295)
              ·
                refine ⟨10751512630244707809483443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167675086829805206322295 10751512630244707809483443)
                ·
                  refine ⟨16127268945367061714225165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10751512630244707809483443 16127268945367061714225165)
                  ·
                    refine ⟨6047725854512648142834437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16127268945367061714225165 6047725854512648142834437)
                    ·
                      refine ⟨1133948597721121526781457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6047725854512648142834437 1133948597721121526781457)
                      ·
                        rfl

theorem cell23_2208357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_2208357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208357 prefixEnd_2208357 := by exact prefixLift 2208357
  have htrace : WordTrace (prefixWord ++ tailWord_2208357) baseStart_2208357 baseEnd_2208357 := by
    simpa [prefixWord, tailWord_2208357, baseEnd_2208357] using wordTrace_append hprefix tailTrace_2208357
  have hstable : (prefixWord ++ tailWord_2208357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208357).length < 2 ^ (prefixWord ++ tailWord_2208357).sum := by decide
  have hdescent : baseEnd_2208357 < baseStart_2208357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208384 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 1, 4]
def baseStart_2208384 : Nat := 118140960795 + 2208384 * 2 ^ 59
def prefixEnd_2208384 : Nat := 4983230072969 + 3 ^ 40 * 2208384 * 2
def baseEnd_2208384 : Nat := 377987487232930973714611

theorem tailTrace_2208384 : CollatzResearch.WordTrace tailWord_2208384 prefixEnd_2208384 377987487232930973714611 := by
  unfold tailWord_2208384
  simp only [CollatzResearch.WordTrace]
  refine ⟨40273190815704702402456103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53697587754272936536608137 40273190815704702402456103)
  ·
    refine ⟨60409786223557053603684155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40273190815704702402456103 60409786223557053603684155)
    ·
      refine ⟨90614679335335580405526233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60409786223557053603684155 90614679335335580405526233)
      ·
        refine ⟨67961009501501685304144675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90614679335335580405526233 67961009501501685304144675)
        ·
          refine ⟨101941514252252527956217013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67961009501501685304144675 101941514252252527956217013)
          ·
            refine ⟨9557016961148674495895345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101941514252252527956217013 9557016961148674495895345)
            ·
              refine ⟨7167762720861505871921509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9557016961148674495895345 7167762720861505871921509)
              ·
                refine ⟨1343955510161532350985283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7167762720861505871921509 1343955510161532350985283)
                ·
                  refine ⟨2015933265242298526477925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343955510161532350985283 2015933265242298526477925)
                  ·
                    refine ⟨377987487232930973714611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015933265242298526477925 377987487232930973714611)
                    ·
                      rfl

theorem cell23_2208384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 4].length) (baseStart_2208384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208384 prefixEnd_2208384 := by exact prefixLift 2208384
  have htrace : WordTrace (prefixWord ++ tailWord_2208384) baseStart_2208384 baseEnd_2208384 := by
    simpa [prefixWord, tailWord_2208384, baseEnd_2208384] using wordTrace_append hprefix tailTrace_2208384
  have hstable : (prefixWord ++ tailWord_2208384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208384).length < 2 ^ (prefixWord ++ tailWord_2208384).sum := by decide
  have hdescent : baseEnd_2208384 < baseStart_2208384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208461 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2208461 : Nat := 118140960795 + 2208461 * 2 ^ 59
def prefixEnd_2208461 : Nat := 4983230072969 + 3 ^ 40 * 2208461 * 2
def baseEnd_2208461 : Nat := 378000666569729706626993

theorem tailTrace_2208461 : CollatzResearch.WordTrace tailWord_2208461 prefixEnd_2208461 378000666569729706626993 := by
  unfold tailWord_2208461
  simp only [CollatzResearch.WordTrace]
  refine ⟨80549190052130446955465237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53699460034753631303643491 80549190052130446955465237)
  ·
    refine ⟨3775743283693614701037433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80549190052130446955465237 3775743283693614701037433)
    ·
      refine ⟨2831807462770211025778075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3775743283693614701037433 2831807462770211025778075)
      ·
        refine ⟨4247711194155316538667113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831807462770211025778075 4247711194155316538667113)
        ·
          refine ⟨3185783395616487404000335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247711194155316538667113 3185783395616487404000335)
          ·
            refine ⟨4778675093424731106000503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185783395616487404000335 4778675093424731106000503)
            ·
              refine ⟨7168012640137096659000755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778675093424731106000503 7168012640137096659000755)
              ·
                refine ⟨10752018960205644988501133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7168012640137096659000755 10752018960205644988501133)
                ·
                  refine ⟨4032007110077116870687925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10752018960205644988501133 4032007110077116870687925)
                  ·
                    refine ⟨378000666569729706626993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4032007110077116870687925 378000666569729706626993)
                    ·
                      rfl

theorem cell23_2208461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2208461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208461 prefixEnd_2208461 := by exact prefixLift 2208461
  have htrace : WordTrace (prefixWord ++ tailWord_2208461) baseStart_2208461 baseEnd_2208461 := by
    simpa [prefixWord, tailWord_2208461, baseEnd_2208461] using wordTrace_append hprefix tailTrace_2208461
  have hstable : (prefixWord ++ tailWord_2208461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208461).length < 2 ^ (prefixWord ++ tailWord_2208461).sum := by decide
  have hdescent : baseEnd_2208461 < baseStart_2208461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208468 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2208468 : Nat := 118140960795 + 2208468 * 2 ^ 59
def prefixEnd_2208468 : Nat := 4983230072969 + 3 ^ 40 * 2208468 * 2
def baseEnd_2208468 : Nat := 1134005594073770592493447

theorem tailTrace_2208468 : CollatzResearch.WordTrace tailWord_2208468 prefixEnd_2208468 1134005594073770592493447 := by
  unfold tailWord_2208468
  simp only [CollatzResearch.WordTrace]
  refine ⟨40274722681552543575485029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53699630242070058100646705 40274722681552543575485029)
  ·
    refine ⟨7551510502791101920403443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40274722681552543575485029 7551510502791101920403443)
    ·
      refine ⟨11327265754186652880605165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551510502791101920403443 11327265754186652880605165)
      ·
        refine ⟨4247724657819994830226937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11327265754186652880605165 4247724657819994830226937)
        ·
          refine ⟨3185793493364996122670203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247724657819994830226937 3185793493364996122670203)
          ·
            refine ⟨4778690240047494184005305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185793493364996122670203 4778690240047494184005305)
            ·
              refine ⟨3584017680035620638003979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4778690240047494184005305 3584017680035620638003979)
              ·
                refine ⟨5376026520053430957005969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584017680035620638003979 5376026520053430957005969)
                ·
                  refine ⟨4032019890040073217754477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5376026520053430957005969 4032019890040073217754477)
                  ·
                    refine ⟨1512007458765027456657929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4032019890040073217754477 1512007458765027456657929)
                    ·
                      refine ⟨1134005594073770592493447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512007458765027456657929 1134005594073770592493447)
                      ·
                        rfl

theorem cell23_2208468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2208468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208468 prefixEnd_2208468 := by exact prefixLift 2208468
  have htrace : WordTrace (prefixWord ++ tailWord_2208468) baseStart_2208468 baseEnd_2208468 := by
    simpa [prefixWord, tailWord_2208468, baseEnd_2208468] using wordTrace_append hprefix tailTrace_2208468
  have hstable : (prefixWord ++ tailWord_2208468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208468).length < 2 ^ (prefixWord ++ tailWord_2208468).sum := by decide
  have hdescent : baseEnd_2208468 < baseStart_2208468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208481 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_2208481 : Nat := 118140960795 + 2208481 * 2 ^ 59
def prefixEnd_2208481 : Nat := 4983230072969 + 3 ^ 40 * 2208481 * 2
def baseEnd_2208481 : Nat := 1134012269322279041630887

theorem tailTrace_2208481 : CollatzResearch.WordTrace tailWord_2208481 prefixEnd_2208481 1134012269322279041630887 := by
  unfold tailWord_2208481
  simp only [CollatzResearch.WordTrace]
  refine ⟨80549919512057990371193297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53699946341371993580795531 80549919512057990371193297)
  ·
    refine ⟨60412439634043492778394973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80549919512057990371193297 60412439634043492778394973)
    ·
      refine ⟨22654664862766309791898115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60412439634043492778394973 22654664862766309791898115)
      ·
        refine ⟨33981997294149464687847173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22654664862766309791898115 33981997294149464687847173)
        ·
          refine ⟨6371624492653024628971345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33981997294149464687847173 6371624492653024628971345)
          ·
            refine ⟨4778718369489768471728509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6371624492653024628971345 4778718369489768471728509)
            ·
              refine ⟨1792019388558663176898191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4778718369489768471728509 1792019388558663176898191)
              ·
                refine ⟨2688029082837994765347287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792019388558663176898191 2688029082837994765347287)
                ·
                  refine ⟨4032043624256992148020931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688029082837994765347287 4032043624256992148020931)
                  ·
                    refine ⟨6048065436385488222031397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4032043624256992148020931 6048065436385488222031397)
                    ·
                      refine ⟨1134012269322279041630887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6048065436385488222031397 1134012269322279041630887)
                      ·
                        rfl

theorem cell23_2208481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_2208481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208481 prefixEnd_2208481 := by exact prefixLift 2208481
  have htrace : WordTrace (prefixWord ++ tailWord_2208481) baseStart_2208481 baseEnd_2208481 := by
    simpa [prefixWord, tailWord_2208481, baseEnd_2208481] using wordTrace_append hprefix tailTrace_2208481
  have hstable : (prefixWord ++ tailWord_2208481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208481).length < 2 ^ (prefixWord ++ tailWord_2208481).sum := by decide
  have hdescent : baseEnd_2208481 < baseStart_2208481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208484 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_2208484 : Nat := 118140960795 + 2208484 * 2 ^ 59
def prefixEnd_2208484 : Nat := 4983230072969 + 3 ^ 40 * 2208484 * 2
def baseEnd_2208484 : Nat := 1134013809764242529893373

theorem tailTrace_2208484 : CollatzResearch.WordTrace tailWord_2208484 prefixEnd_2208484 1134013809764242529893373 := by
  unfold tailWord_2208484
  simp only [CollatzResearch.WordTrace]
  refine ⟨40275014465523560941776253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53700019287364747922368337 40275014465523560941776253)
  ·
    refine ⟨15103130424571335353166095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40275014465523560941776253 15103130424571335353166095)
    ·
      refine ⟨22654695636857003029749143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15103130424571335353166095 22654695636857003029749143)
      ·
        refine ⟨33982043455285504544623715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22654695636857003029749143 33982043455285504544623715)
        ·
          refine ⟨50973065182928256816935573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33982043455285504544623715 50973065182928256816935573)
          ·
            refine ⟨2389362430449762038293855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50973065182928256816935573 2389362430449762038293855)
            ·
              refine ⟨3584043645674643057440783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389362430449762038293855 3584043645674643057440783)
              ·
                refine ⟨5376065468511964586161175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584043645674643057440783 5376065468511964586161175)
                ·
                  refine ⟨8064098202767946879241763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5376065468511964586161175 8064098202767946879241763)
                  ·
                    refine ⟨12096147304151920318862645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8064098202767946879241763 12096147304151920318862645)
                    ·
                      refine ⟨1134013809764242529893373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12096147304151920318862645 1134013809764242529893373)
                      ·
                        rfl

theorem cell23_2208484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_2208484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208484 prefixEnd_2208484 := by exact prefixLift 2208484
  have htrace : WordTrace (prefixWord ++ tailWord_2208484) baseStart_2208484 baseEnd_2208484 := by
    simpa [prefixWord, tailWord_2208484, baseEnd_2208484] using wordTrace_append hprefix tailTrace_2208484
  have hstable : (prefixWord ++ tailWord_2208484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208484).length < 2 ^ (prefixWord ++ tailWord_2208484).sum := by decide
  have hdescent : baseEnd_2208484 < baseStart_2208484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208497 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_2208497 : Nat := 118140960795 + 2208497 * 2 ^ 59
def prefixEnd_2208497 : Nat := 4983230072969 + 3 ^ 40 * 2208497 * 2
def baseEnd_2208497 : Nat := 1134020485012750979030813

theorem tailTrace_2208497 : CollatzResearch.WordTrace tailWord_2208497 prefixEnd_2208497 1134020485012750979030813 := by
  unfold tailWord_2208497
  simp only [CollatzResearch.WordTrace]
  refine ⟨80550503080000025103775745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53700335386666683402517163 80550503080000025103775745)
  ·
    refine ⟨60412877310000018827831809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80550503080000025103775745 60412877310000018827831809)
    ·
      refine ⟨45309657982500014120873857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60412877310000018827831809 45309657982500014120873857)
      ·
        refine ⟨33982243486875010590655393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45309657982500014120873857 33982243486875010590655393)
        ·
          refine ⟨25486682615156257942991545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33982243486875010590655393 25486682615156257942991545)
          ·
            refine ⟨19115011961367193457243659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25486682615156257942991545 19115011961367193457243659)
            ·
              refine ⟨28672517942050790185865489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19115011961367193457243659 28672517942050790185865489)
              ·
                refine ⟨21504388456538092639399117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28672517942050790185865489 21504388456538092639399117)
                ·
                  refine ⟨8064145671201784739774669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21504388456538092639399117 8064145671201784739774669)
                  ·
                    refine ⟨3024054626700669277415501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8064145671201784739774669 3024054626700669277415501)
                    ·
                      refine ⟨1134020485012750979030813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024054626700669277415501 1134020485012750979030813)
                      ·
                        rfl

theorem cell23_2208497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_2208497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208497 prefixEnd_2208497 := by exact prefixLift 2208497
  have htrace : WordTrace (prefixWord ++ tailWord_2208497) baseStart_2208497 baseEnd_2208497 := by
    simpa [prefixWord, tailWord_2208497, baseEnd_2208497] using wordTrace_append hprefix tailTrace_2208497
  have hstable : (prefixWord ++ tailWord_2208497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208497).length < 2 ^ (prefixWord ++ tailWord_2208497).sum := by decide
  have hdescent : baseEnd_2208497 < baseStart_2208497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208535 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_2208535 : Nat := 118140960795 + 2208535 * 2 ^ 59
def prefixEnd_2208535 : Nat := 4983230072969 + 3 ^ 40 * 2208535 * 2
def baseEnd_2208535 : Nat := 1134039997277621830355639

theorem tailTrace_2208535 : CollatzResearch.WordTrace tailWord_2208535 prefixEnd_2208535 1134039997277621830355639 := by
  unfold tailWord_2208535
  simp only [CollatzResearch.WordTrace]
  refine ⟨80551889053862357593659059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53701259369241571729106039 80551889053862357593659059)
  ·
    refine ⟨120827833580793536390488589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80551889053862357593659059 120827833580793536390488589)
    ·
      refine ⟨45310437592797576146433221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120827833580793536390488589 45310437592797576146433221)
      ·
        refine ⟨8495707048649545527456229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45310437592797576146433221 8495707048649545527456229)
        ·
          refine ⟨1592945071621789786398043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8495707048649545527456229 1592945071621789786398043)
          ·
            refine ⟨2389417607432684679597065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592945071621789786398043 2389417607432684679597065)
            ·
              refine ⟨1792063205574513509697799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389417607432684679597065 1792063205574513509697799)
              ·
                refine ⟨2688094808361770264546699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792063205574513509697799 2688094808361770264546699)
                ·
                  refine ⟨4032142212542655396820049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688094808361770264546699 4032142212542655396820049)
                  ·
                    refine ⟨3024106659406991547615037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4032142212542655396820049 3024106659406991547615037)
                    ·
                      refine ⟨1134039997277621830355639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024106659406991547615037 1134039997277621830355639)
                      ·
                        rfl

theorem cell23_2208535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_2208535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208535 prefixEnd_2208535 := by exact prefixLift 2208535
  have htrace : WordTrace (prefixWord ++ tailWord_2208535) baseStart_2208535 baseEnd_2208535 := by
    simpa [prefixWord, tailWord_2208535, baseEnd_2208535] using wordTrace_append hprefix tailTrace_2208535
  have hstable : (prefixWord ++ tailWord_2208535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208535).length < 2 ^ (prefixWord ++ tailWord_2208535).sum := by decide
  have hdescent : baseEnd_2208535 < baseStart_2208535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208567 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_2208567 : Nat := 118140960795 + 2208567 * 2 ^ 59
def prefixEnd_2208567 : Nat := 4983230072969 + 3 ^ 40 * 2208567 * 2
def baseEnd_2208567 : Nat := 1134056428658565705155491

theorem tailTrace_2208567 : CollatzResearch.WordTrace tailWord_2208567 prefixEnd_2208567 1134056428658565705155491 := by
  unfold tailWord_2208567
  simp only [CollatzResearch.WordTrace]
  refine ⟨80553056189746427058823955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53702037459830951372549303 80553056189746427058823955)
  ·
    refine ⟨120829584284619640588235933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80553056189746427058823955 120829584284619640588235933)
    ·
      refine ⟨45311094106732365220588475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120829584284619640588235933 45311094106732365220588475)
      ·
        refine ⟨67966641160098547830882713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45311094106732365220588475 67966641160098547830882713)
        ·
          refine ⟨50974980870073910873162035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67966641160098547830882713 50974980870073910873162035)
          ·
            refine ⟨76462471305110866309743053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50974980870073910873162035 76462471305110866309743053)
            ·
              refine ⟨28673426739416574866153645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76462471305110866309743053 28673426739416574866153645)
              ·
                refine ⟨10752535027281215574807617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28673426739416574866153645 10752535027281215574807617)
                ·
                  refine ⟨8064401270460911681105713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10752535027281215574807617 8064401270460911681105713)
                  ·
                    refine ⟨6048300952845683760829285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8064401270460911681105713 6048300952845683760829285)
                    ·
                      refine ⟨1134056428658565705155491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6048300952845683760829285 1134056428658565705155491)
                      ·
                        rfl

theorem cell23_2208567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_2208567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208567 prefixEnd_2208567 := by exact prefixLift 2208567
  have htrace : WordTrace (prefixWord ++ tailWord_2208567) baseStart_2208567 baseEnd_2208567 := by
    simpa [prefixWord, tailWord_2208567, baseEnd_2208567] using wordTrace_append hprefix tailTrace_2208567
  have hstable : (prefixWord ++ tailWord_2208567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208567).length < 2 ^ (prefixWord ++ tailWord_2208567).sum := by decide
  have hdescent : baseEnd_2208567 < baseStart_2208567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208627 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_2208627 : Nat := 118140960795 + 2208627 * 2 ^ 59
def prefixEnd_2208627 : Nat := 4983230072969 + 3 ^ 40 * 2208627 * 2
def baseEnd_2208627 : Nat := 1134087237497835470405215

theorem tailTrace_2208627 : CollatzResearch.WordTrace tailWord_2208627 prefixEnd_2208627 1134087237497835470405215 := by
  unfold tailWord_2208627
  simp only [CollatzResearch.WordTrace]
  refine ⟨80555244569529057306008135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53703496379686038204005423 80555244569529057306008135)
  ·
    refine ⟨120832866854293585959012203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80555244569529057306008135 120832866854293585959012203)
    ·
      refine ⟨181249300281440378938518305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120832866854293585959012203 181249300281440378938518305)
      ·
        refine ⟨135936975211080284203888729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181249300281440378938518305 135936975211080284203888729)
        ·
          refine ⟨101952731408310213152916547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135936975211080284203888729 101952731408310213152916547)
          ·
            refine ⟨152929097112465319729374821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101952731408310213152916547 152929097112465319729374821)
            ·
              refine ⟨28674205708587247449257779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152929097112465319729374821 28674205708587247449257779)
              ·
                refine ⟨43011308562880871173886669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28674205708587247449257779 43011308562880871173886669)
                ·
                  refine ⟨16129240711080326690207501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43011308562880871173886669 16129240711080326690207501)
                  ·
                    refine ⟨6048465266655122508827813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16129240711080326690207501 6048465266655122508827813)
                    ·
                      refine ⟨1134087237497835470405215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6048465266655122508827813 1134087237497835470405215)
                      ·
                        rfl

theorem cell23_2208627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_2208627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208627 prefixEnd_2208627 := by exact prefixLift 2208627
  have htrace : WordTrace (prefixWord ++ tailWord_2208627) baseStart_2208627 baseEnd_2208627 := by
    simpa [prefixWord, tailWord_2208627, baseEnd_2208627] using wordTrace_append hprefix tailTrace_2208627
  have hstable : (prefixWord ++ tailWord_2208627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208627).length < 2 ^ (prefixWord ++ tailWord_2208627).sum := by decide
  have hdescent : baseEnd_2208627 < baseStart_2208627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208637 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2208637 : Nat := 118140960795 + 2208637 * 2 ^ 59
def prefixEnd_2208637 : Nat := 4983230072969 + 3 ^ 40 * 2208637 * 2
def baseEnd_2208637 : Nat := 378030790768126810426723

theorem tailTrace_2208637 : CollatzResearch.WordTrace tailWord_2208637 prefixEnd_2208637 378030790768126810426723 := by
  unfold tailWord_2208637
  simp only [CollatzResearch.WordTrace]
  refine ⟨80555609299492829013872165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53703739532995219342581443 80555609299492829013872165)
  ·
    refine ⟨15104176743654905440101031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80555609299492829013872165 15104176743654905440101031)
    ·
      refine ⟨22656265115482358160151547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15104176743654905440101031 22656265115482358160151547)
      ·
        refine ⟨33984397673223537240227321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22656265115482358160151547 33984397673223537240227321)
        ·
          refine ⟨25488298254917652930170491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33984397673223537240227321 25488298254917652930170491)
          ·
            refine ⟨38232447382376479395255737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25488298254917652930170491 38232447382376479395255737)
            ·
              refine ⟨28674335536782359546441803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38232447382376479395255737 28674335536782359546441803)
              ·
                refine ⟨43011503305173539319662705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28674335536782359546441803 43011503305173539319662705)
                ·
                  refine ⟨32258627478880154489747029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43011503305173539319662705 32258627478880154489747029)
                  ·
                    refine ⟨378030790768126810426723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32258627478880154489747029 378030790768126810426723)
                    ·
                      rfl

theorem cell23_2208637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2208637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208637 prefixEnd_2208637 := by exact prefixLift 2208637
  have htrace : WordTrace (prefixWord ++ tailWord_2208637) baseStart_2208637 baseEnd_2208637 := by
    simpa [prefixWord, tailWord_2208637, baseEnd_2208637] using wordTrace_append hprefix tailTrace_2208637
  have hstable : (prefixWord ++ tailWord_2208637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208637).length < 2 ^ (prefixWord ++ tailWord_2208637).sum := by decide
  have hdescent : baseEnd_2208637 < baseStart_2208637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208657 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2208657 : Nat := 118140960795 + 2208657 * 2 ^ 59
def prefixEnd_2208657 : Nat := 4983230072969 + 3 ^ 40 * 2208657 * 2
def baseEnd_2208657 : Nat := 1134102641917470353030077

theorem tailTrace_2208657 : CollatzResearch.WordTrace tailWord_2208657 prefixEnd_2208657 1134102641917470353030077 := by
  unfold tailWord_2208657
  simp only [CollatzResearch.WordTrace]
  refine ⟨80556338759420372429600225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53704225839613581619733483 80556338759420372429600225)
  ·
    refine ⟨60417254069565279322200169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80556338759420372429600225 60417254069565279322200169)
    ·
      refine ⟨45312940552173959491650127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60417254069565279322200169 45312940552173959491650127)
      ·
        refine ⟨67969410828260939237475191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45312940552173959491650127 67969410828260939237475191)
        ·
          refine ⟨101954116242391408856212787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67969410828260939237475191 101954116242391408856212787)
          ·
            refine ⟨152931174363587113284319181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101954116242391408856212787 152931174363587113284319181)
            ·
              refine ⟨57349190386345167481619693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152931174363587113284319181 57349190386345167481619693)
              ·
                refine ⟨21505946394879437805607385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57349190386345167481619693 21505946394879437805607385)
                ·
                  refine ⟨16129459796159578354205539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21505946394879437805607385 16129459796159578354205539)
                  ·
                    refine ⟨24194189694239367531308309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16129459796159578354205539 24194189694239367531308309)
                    ·
                      refine ⟨1134102641917470353030077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24194189694239367531308309 1134102641917470353030077)
                      ·
                        rfl

theorem cell23_2208657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2208657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208657 prefixEnd_2208657 := by exact prefixLift 2208657
  have htrace : WordTrace (prefixWord ++ tailWord_2208657) baseStart_2208657 baseEnd_2208657 := by
    simpa [prefixWord, tailWord_2208657, baseEnd_2208657] using wordTrace_append hprefix tailTrace_2208657
  have hstable : (prefixWord ++ tailWord_2208657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208657).length < 2 ^ (prefixWord ++ tailWord_2208657).sum := by decide
  have hdescent : baseEnd_2208657 < baseStart_2208657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208662 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2208662 : Nat := 118140960795 + 2208662 * 2 ^ 59
def prefixEnd_2208662 : Nat := 4983230072969 + 3 ^ 40 * 2208662 * 2
def baseEnd_2208662 : Nat := 126011689924526981496395

theorem tailTrace_2208662 : CollatzResearch.WordTrace tailWord_2208662 prefixEnd_2208662 126011689924526981496395 := by
  unfold tailWord_2208662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034782570275141142720765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53704347416268172189021493 5034782570275141142720765)
  ·
    refine ⟨1888043463853177928520287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5034782570275141142720765 1888043463853177928520287)
    ·
      refine ⟨2832065195779766892780431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888043463853177928520287 2832065195779766892780431)
      ·
        refine ⟨4248097793669650339170647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832065195779766892780431 4248097793669650339170647)
        ·
          refine ⟨6372146690504475508755971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248097793669650339170647 6372146690504475508755971)
          ·
            refine ⟨9558220035756713263133957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372146690504475508755971 9558220035756713263133957)
            ·
              refine ⟨1792166256704383736837617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9558220035756713263133957 1792166256704383736837617)
              ·
                refine ⟨1344124692528287802628213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792166256704383736837617 1344124692528287802628213)
                ·
                  refine ⟨126011689924526981496395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344124692528287802628213 126011689924526981496395)
                  ·
                    rfl

theorem cell23_2208662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2208662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208662 prefixEnd_2208662 := by exact prefixLift 2208662
  have htrace : WordTrace (prefixWord ++ tailWord_2208662) baseStart_2208662 baseEnd_2208662 := by
    simpa [prefixWord, tailWord_2208662, baseEnd_2208662] using wordTrace_append hprefix tailTrace_2208662
  have hstable : (prefixWord ++ tailWord_2208662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208662).length < 2 ^ (prefixWord ++ tailWord_2208662).sum := by decide
  have hdescent : baseEnd_2208662 < baseStart_2208662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208687 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_2208687 : Nat := 118140960795 + 2208687 * 2 ^ 59
def prefixEnd_2208687 : Nat := 4983230072969 + 3 ^ 40 * 2208687 * 2
def baseEnd_2208687 : Nat := 1134118046337105235654939

theorem tailTrace_2208687 : CollatzResearch.WordTrace tailWord_2208687 prefixEnd_2208687 1134118046337105235654939 := by
  unfold tailWord_2208687
  simp only [CollatzResearch.WordTrace]
  refine ⟨80557432949311687553192315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53704955299541125035461543 80557432949311687553192315)
  ·
    refine ⟨120836149423967531329788473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80557432949311687553192315 120836149423967531329788473)
    ·
      refine ⟨90627112067975648497341355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120836149423967531329788473 90627112067975648497341355)
      ·
        refine ⟨135940668101963472746012033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90627112067975648497341355 135940668101963472746012033)
        ·
          refine ⟨101955501076472604559509025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135940668101963472746012033 101955501076472604559509025)
          ·
            refine ⟨76466625807354453419631769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101955501076472604559509025 76466625807354453419631769)
            ·
              refine ⟨57349969355515840064723827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76466625807354453419631769 57349969355515840064723827)
              ·
                refine ⟨86024954033273760097085741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57349969355515840064723827 86024954033273760097085741)
                ·
                  refine ⟨32259357762477660036407153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86024954033273760097085741 32259357762477660036407153)
                  ·
                    refine ⟨24194518321858245027305365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32259357762477660036407153 24194518321858245027305365)
                    ·
                      refine ⟨1134118046337105235654939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24194518321858245027305365 1134118046337105235654939)
                      ·
                        rfl

theorem cell23_2208687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_2208687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208687 prefixEnd_2208687 := by exact prefixLift 2208687
  have htrace : WordTrace (prefixWord ++ tailWord_2208687) baseStart_2208687 baseEnd_2208687 := by
    simpa [prefixWord, tailWord_2208687, baseEnd_2208687] using wordTrace_append hprefix tailTrace_2208687
  have hstable : (prefixWord ++ tailWord_2208687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208687).length < 2 ^ (prefixWord ++ tailWord_2208687).sum := by decide
  have hdescent : baseEnd_2208687 < baseStart_2208687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208707 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_2208707 : Nat := 118140960795 + 2208707 * 2 ^ 59
def prefixEnd_2208707 : Nat := 4983230072969 + 3 ^ 40 * 2208707 * 2
def baseEnd_2208707 : Nat := 1134128315950195157404847

theorem tailTrace_2208707 : CollatzResearch.WordTrace tailWord_2208707 prefixEnd_2208707 1134128315950195157404847 := by
  unfold tailWord_2208707
  simp only [CollatzResearch.WordTrace]
  refine ⟨80558162409239230968920375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53705441606159487312613583 80558162409239230968920375)
  ·
    refine ⟨120837243613858846453380563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80558162409239230968920375 120837243613858846453380563)
    ·
      refine ⟨181255865420788269680070845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120837243613858846453380563 181255865420788269680070845)
      ·
        refine ⟨67970949532795601130026567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181255865420788269680070845 67970949532795601130026567)
        ·
          refine ⟨101956424299193401695039851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67970949532795601130026567 101956424299193401695039851)
          ·
            refine ⟨152934636448790102542559777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101956424299193401695039851 152934636448790102542559777)
            ·
              refine ⟨114700977336592576906919833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152934636448790102542559777 114700977336592576906919833)
              ·
                refine ⟨86025733002444432680189875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114700977336592576906919833 86025733002444432680189875)
                ·
                  refine ⟨129038599503666649020284813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86025733002444432680189875 129038599503666649020284813)
                  ·
                    refine ⟨48389474813874993382606805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129038599503666649020284813 48389474813874993382606805)
                    ·
                      refine ⟨1134128315950195157404847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48389474813874993382606805 1134128315950195157404847)
                      ·
                        rfl

theorem cell23_2208707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_2208707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208707 prefixEnd_2208707 := by exact prefixLift 2208707
  have htrace : WordTrace (prefixWord ++ tailWord_2208707) baseStart_2208707 baseEnd_2208707 := by
    simpa [prefixWord, tailWord_2208707, baseEnd_2208707] using wordTrace_append hprefix tailTrace_2208707
  have hstable : (prefixWord ++ tailWord_2208707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208707).length < 2 ^ (prefixWord ++ tailWord_2208707).sum := by decide
  have hdescent : baseEnd_2208707 < baseStart_2208707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208721 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_2208721 : Nat := 118140960795 + 2208721 * 2 ^ 59
def prefixEnd_2208721 : Nat := 4983230072969 + 3 ^ 40 * 2208721 * 2
def baseEnd_2208721 : Nat := 1134135504679358102629783

theorem tailTrace_2208721 : CollatzResearch.WordTrace tailWord_2208721 prefixEnd_2208721 1134135504679358102629783 := by
  unfold tailWord_2208721
  simp only [CollatzResearch.WordTrace]
  refine ⟨80558673031188511359930017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53705782020792340906620011 80558673031188511359930017)
  ·
    refine ⟨60419004773391383519947513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80558673031188511359930017 60419004773391383519947513)
    ·
      refine ⟨45314253580043537639960635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60419004773391383519947513 45314253580043537639960635)
      ·
        refine ⟨67971380370065306459940953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45314253580043537639960635 67971380370065306459940953)
        ·
          refine ⟨50978535277548979844955715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67971380370065306459940953 50978535277548979844955715)
          ·
            refine ⟨76467802916323469767433573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50978535277548979844955715 76467802916323469767433573)
            ·
              refine ⟨14337713046810650581393795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76467802916323469767433573 14337713046810650581393795)
              ·
                refine ⟨21506569570215975872090693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14337713046810650581393795 21506569570215975872090693)
                ·
                  refine ⟨4032481794415495476017005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21506569570215975872090693 4032481794415495476017005)
                  ·
                    refine ⟨1512180672905810803506377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4032481794415495476017005 1512180672905810803506377)
                    ·
                      refine ⟨1134135504679358102629783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512180672905810803506377 1134135504679358102629783)
                      ·
                        rfl

theorem cell23_2208721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_2208721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208721 prefixEnd_2208721 := by exact prefixLift 2208721
  have htrace : WordTrace (prefixWord ++ tailWord_2208721) baseStart_2208721 baseEnd_2208721 := by
    simpa [prefixWord, tailWord_2208721, baseEnd_2208721] using wordTrace_append hprefix tailTrace_2208721
  have hstable : (prefixWord ++ tailWord_2208721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208721).length < 2 ^ (prefixWord ++ tailWord_2208721).sum := by decide
  have hdescent : baseEnd_2208721 < baseStart_2208721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208728 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2208728 : Nat := 118140960795 + 2208728 * 2 ^ 59
def prefixEnd_2208728 : Nat := 4983230072969 + 3 ^ 40 * 2208728 * 2
def baseEnd_2208728 : Nat := 1134139099043939575242251

theorem tailTrace_2208728 : CollatzResearch.WordTrace tailWord_2208728 prefixEnd_2208728 1134139099043939575242251 := by
  unfold tailWord_2208728
  simp only [CollatzResearch.WordTrace]
  refine ⟨40279464171081575777717419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53705952228108767703623225 40279464171081575777717419)
  ·
    refine ⟨60419196256622363666576129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40279464171081575777717419 60419196256622363666576129)
    ·
      refine ⟨45314397192466772749932097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60419196256622363666576129 45314397192466772749932097)
      ·
        refine ⟨33985797894350079562449073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45314397192466772749932097 33985797894350079562449073)
        ·
          refine ⟨25489348420762559671836805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33985797894350079562449073 25489348420762559671836805)
          ·
            refine ⟨4779252828892979938469401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25489348420762559671836805 4779252828892979938469401)
            ·
              refine ⟨3584439621669734953852051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4779252828892979938469401 3584439621669734953852051)
              ·
                refine ⟨5376659432504602430778077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584439621669734953852051 5376659432504602430778077)
                ·
                  refine ⟨2016247287189225911541779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5376659432504602430778077 2016247287189225911541779)
                  ·
                    refine ⟨3024370930783838867312669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2016247287189225911541779 3024370930783838867312669)
                    ·
                      refine ⟨1134139099043939575242251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024370930783838867312669 1134139099043939575242251)
                      ·
                        rfl

theorem cell23_2208728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2208728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208728 prefixEnd_2208728 := by exact prefixLift 2208728
  have htrace : WordTrace (prefixWord ++ tailWord_2208728) baseStart_2208728 baseEnd_2208728 := by
    simpa [prefixWord, tailWord_2208728, baseEnd_2208728] using wordTrace_append hprefix tailTrace_2208728
  have hstable : (prefixWord ++ tailWord_2208728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208728).length < 2 ^ (prefixWord ++ tailWord_2208728).sum := by decide
  have hdescent : baseEnd_2208728 < baseStart_2208728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208751 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_2208751 : Nat := 118140960795 + 2208751 * 2 ^ 59
def prefixEnd_2208751 : Nat := 4983230072969 + 3 ^ 40 * 2208751 * 2
def baseEnd_2208751 : Nat := 1134150909098992985254645

theorem tailTrace_2208751 : CollatzResearch.WordTrace tailWord_2208751 prefixEnd_2208751 1134150909098992985254645 := by
  unfold tailWord_2208751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80559767221079826483522107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53706511480719884322348071 80559767221079826483522107)
  ·
    refine ⟨120839650831619739725283161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80559767221079826483522107 120839650831619739725283161)
    ·
      refine ⟨90629738123714804793962371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120839650831619739725283161 90629738123714804793962371)
      ·
        refine ⟨135944607185572207190943557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90629738123714804793962371 135944607185572207190943557)
        ·
          refine ⟨25489613847294788848301917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135944607185572207190943557 25489613847294788848301917)
          ·
            refine ⟨9558605192735545818113219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25489613847294788848301917 9558605192735545818113219)
            ·
              refine ⟨14337907789103318727169829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9558605192735545818113219 14337907789103318727169829)
              ·
                refine ⟨2688357710456872261344343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14337907789103318727169829 2688357710456872261344343)
                ·
                  refine ⟨4032536565685308392016515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688357710456872261344343 4032536565685308392016515)
                  ·
                    refine ⟨6048804848527962588024773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4032536565685308392016515 6048804848527962588024773)
                    ·
                      refine ⟨1134150909098992985254645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6048804848527962588024773 1134150909098992985254645)
                      ·
                        rfl

theorem cell23_2208751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_2208751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208751 prefixEnd_2208751 := by exact prefixLift 2208751
  have htrace : WordTrace (prefixWord ++ tailWord_2208751) baseStart_2208751 baseEnd_2208751 := by
    simpa [prefixWord, tailWord_2208751, baseEnd_2208751] using wordTrace_append hprefix tailTrace_2208751
  have hstable : (prefixWord ++ tailWord_2208751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208751).length < 2 ^ (prefixWord ++ tailWord_2208751).sum := by decide
  have hdescent : baseEnd_2208751 < baseStart_2208751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208784 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_2208784 : Nat := 118140960795 + 2208784 * 2 ^ 59
def prefixEnd_2208784 : Nat := 4983230072969 + 3 ^ 40 * 2208784 * 2
def baseEnd_2208784 : Nat := 1134167853960591356141993

theorem tailTrace_2208784 : CollatzResearch.WordTrace tailWord_2208784 prefixEnd_2208784 1134167853960591356141993 := by
  unfold tailWord_2208784
  simp only [CollatzResearch.WordTrace]
  refine ⟨40280485414980136559736703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53707313886640182079648937 40280485414980136559736703)
  ·
    refine ⟨60420728122470204839605055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40280485414980136559736703 60420728122470204839605055)
    ·
      refine ⟨90631092183705307259407583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60420728122470204839605055 90631092183705307259407583)
      ·
        refine ⟨135946638275557960889111375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90631092183705307259407583 135946638275557960889111375)
        ·
          refine ⟨203919957413336941333667063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135946638275557960889111375 203919957413336941333667063)
          ·
            refine ⟨305879936120005412000500595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203919957413336941333667063 305879936120005412000500595)
            ·
              refine ⟨458819904180008118000750893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305879936120005412000500595 458819904180008118000750893)
              ·
                refine ⟨172057464067503044250281585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 458819904180008118000750893 172057464067503044250281585)
                ·
                  refine ⟨129043098050627283187711189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172057464067503044250281585 129043098050627283187711189)
                  ·
                    refine ⟨3024447610561576949711981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129043098050627283187711189 3024447610561576949711981)
                    ·
                      refine ⟨1134167853960591356141993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024447610561576949711981 1134167853960591356141993)
                      ·
                        rfl

theorem cell23_2208784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_2208784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208784 prefixEnd_2208784 := by exact prefixLift 2208784
  have htrace : WordTrace (prefixWord ++ tailWord_2208784) baseStart_2208784 baseEnd_2208784 := by
    simpa [prefixWord, tailWord_2208784, baseEnd_2208784] using wordTrace_append hprefix tailTrace_2208784
  have hstable : (prefixWord ++ tailWord_2208784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208784).length < 2 ^ (prefixWord ++ tailWord_2208784).sum := by decide
  have hdescent : baseEnd_2208784 < baseStart_2208784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208785 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 1, 2, 2]
def baseStart_2208785 : Nat := 118140960795 + 2208785 * 2 ^ 59
def prefixEnd_2208785 : Nat := 4983230072969 + 3 ^ 40 * 2208785 * 2
def baseEnd_2208785 : Nat := 1134168367441245852229489

theorem tailTrace_2208785 : CollatzResearch.WordTrace tailWord_2208785 prefixEnd_2208785 1134168367441245852229489 := by
  unfold tailWord_2208785
  simp only [CollatzResearch.WordTrace]
  refine ⟨80561007302956650290259809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53707338201971100193506539 80561007302956650290259809)
  ·
    refine ⟨60420755477217487717694857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80561007302956650290259809 60420755477217487717694857)
    ·
      refine ⟨45315566607913115788271143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60420755477217487717694857 45315566607913115788271143)
      ·
        refine ⟨67973349911869673682406715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45315566607913115788271143 67973349911869673682406715)
        ·
          refine ⟨101960024867804510523610073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67973349911869673682406715 101960024867804510523610073)
          ·
            refine ⟨76470018650853382892707555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101960024867804510523610073 76470018650853382892707555)
            ·
              refine ⟨114705027976280074339061333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76470018650853382892707555 114705027976280074339061333)
              ·
                refine ⟨1344199546597032121160875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 114705027976280074339061333 1344199546597032121160875)
                ·
                  refine ⟨2016299319895548181741313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344199546597032121160875 2016299319895548181741313)
                  ·
                    refine ⟨1512224489921661136305985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016299319895548181741313 1512224489921661136305985)
                    ·
                      refine ⟨1134168367441245852229489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512224489921661136305985 1134168367441245852229489)
                      ·
                        rfl

theorem cell23_2208785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_2208785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208785 prefixEnd_2208785 := by exact prefixLift 2208785
  have htrace : WordTrace (prefixWord ++ tailWord_2208785) baseStart_2208785 baseEnd_2208785 := by
    simpa [prefixWord, tailWord_2208785, baseEnd_2208785] using wordTrace_append hprefix tailTrace_2208785
  have hstable : (prefixWord ++ tailWord_2208785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208785).length < 2 ^ (prefixWord ++ tailWord_2208785).sum := by decide
  have hdescent : baseEnd_2208785 < baseStart_2208785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208791 : List Nat := [1, 1, 3, 5, 1, 2, 2, 8]
def baseStart_2208791 : Nat := 118140960795 + 2208791 * 2 ^ 59
def prefixEnd_2208791 : Nat := 4983230072969 + 3 ^ 40 * 2208791 * 2
def baseEnd_2208791 : Nat := 42006349937969364027943

theorem tailTrace_2208791 : CollatzResearch.WordTrace tailWord_2208791 prefixEnd_2208791 42006349937969364027943 := by
  unfold tailWord_2208791
  simp only [CollatzResearch.WordTrace]
  refine ⟨80561226140934913314978227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53707484093956608876652151 80561226140934913314978227)
  ·
    refine ⟨120841839211402369972467341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80561226140934913314978227 120841839211402369972467341)
    ·
      refine ⟨45315689704275888739675253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120841839211402369972467341 45315689704275888739675253)
      ·
        refine ⟨4248345909775864569344555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45315689704275888739675253 4248345909775864569344555)
        ·
          refine ⟨6372518864663796854016833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248345909775864569344555 6372518864663796854016833)
          ·
            refine ⟨4779389148497847640512625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6372518864663796854016833 4779389148497847640512625)
            ·
              refine ⟨3584541861373385730384469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4779389148497847640512625 3584541861373385730384469)
              ·
                refine ⟨42006349937969364027943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3584541861373385730384469 42006349937969364027943)
                ·
                  rfl

theorem cell23_2208791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 8].length) (baseStart_2208791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208791 prefixEnd_2208791 := by exact prefixLift 2208791
  have htrace : WordTrace (prefixWord ++ tailWord_2208791) baseStart_2208791 baseEnd_2208791 := by
    simpa [prefixWord, tailWord_2208791, baseEnd_2208791] using wordTrace_append hprefix tailTrace_2208791
  have hstable : (prefixWord ++ tailWord_2208791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208791).length < 2 ^ (prefixWord ++ tailWord_2208791).sum := by decide
  have hdescent : baseEnd_2208791 < baseStart_2208791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208794 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2208794 : Nat := 118140960795 + 2208794 * 2 ^ 59
def prefixEnd_2208794 : Nat := 4983230072969 + 3 ^ 40 * 2208794 * 2
def baseEnd_2208794 : Nat := 1134172988767136317016947

theorem tailTrace_2208794 : CollatzResearch.WordTrace tailWord_2208794 prefixEnd_2208794 1134172988767136317016947 := by
  unfold tailWord_2208794
  simp only [CollatzResearch.WordTrace]
  refine ⟨20140333889981011206834359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53707557039949363218224957 20140333889981011206834359)
  ·
    refine ⟨30210500834971516810251539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20140333889981011206834359 30210500834971516810251539)
    ·
      refine ⟨45315751252457275215377309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30210500834971516810251539 45315751252457275215377309)
      ·
        refine ⟨16993406719671478205766491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45315751252457275215377309 16993406719671478205766491)
        ·
          refine ⟨25490110079507217308649737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16993406719671478205766491 25490110079507217308649737)
          ·
            refine ⟨19117582559630412981487303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25490110079507217308649737 19117582559630412981487303)
            ·
              refine ⟨28676373839445619472230955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19117582559630412981487303 28676373839445619472230955)
              ·
                refine ⟨43014560759168429208346433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28676373839445619472230955 43014560759168429208346433)
                ·
                  refine ⟨32260920569376321906259825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43014560759168429208346433 32260920569376321906259825)
                  ·
                    refine ⟨24195690427032241429694869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32260920569376321906259825 24195690427032241429694869)
                    ·
                      refine ⟨1134172988767136317016947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24195690427032241429694869 1134172988767136317016947)
                      ·
                        rfl

theorem cell23_2208794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2208794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208794 prefixEnd_2208794 := by exact prefixLift 2208794
  have htrace : WordTrace (prefixWord ++ tailWord_2208794) baseStart_2208794 baseEnd_2208794 := by
    simpa [prefixWord, tailWord_2208794, baseEnd_2208794] using wordTrace_append hprefix tailTrace_2208794
  have hstable : (prefixWord ++ tailWord_2208794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208794).length < 2 ^ (prefixWord ++ tailWord_2208794).sum := by decide
  have hdescent : baseEnd_2208794 < baseStart_2208794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208822 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2208822 : Nat := 118140960795 + 2208822 * 2 ^ 59
def prefixEnd_2208822 : Nat := 4983230072969 + 3 ^ 40 * 2208822 * 2
def baseEnd_2208822 : Nat := 1134187366225462207466819

theorem tailTrace_2208822 : CollatzResearch.WordTrace tailWord_2208822 prefixEnd_2208822 1134187366225462207466819 := by
  unfold tailWord_2208822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035147300238912850584795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53708237869215070406237813 5035147300238912850584795)
  ·
    refine ⟨7552720950358369275877193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035147300238912850584795 7552720950358369275877193)
    ·
      refine ⟨5664540712768776956907895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7552720950358369275877193 5664540712768776956907895)
      ·
        refine ⟨8496811069153165435361843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664540712768776956907895 8496811069153165435361843)
        ·
          refine ⟨12745216603729748153042765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8496811069153165435361843 12745216603729748153042765)
          ·
            refine ⟨4779456226398655557391037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12745216603729748153042765 4779456226398655557391037)
            ·
              refine ⟨1792296084899495834021639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4779456226398655557391037 1792296084899495834021639)
              ·
                refine ⟨2688444127349243751032459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792296084899495834021639 2688444127349243751032459)
                ·
                  refine ⟨4032666191023865626548689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688444127349243751032459 4032666191023865626548689)
                  ·
                    refine ⟨3024499643267899219911517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4032666191023865626548689 3024499643267899219911517)
                    ·
                      refine ⟨1134187366225462207466819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024499643267899219911517 1134187366225462207466819)
                      ·
                        rfl

theorem cell23_2208822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2208822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208822 prefixEnd_2208822 := by exact prefixLift 2208822
  have htrace : WordTrace (prefixWord ++ tailWord_2208822) baseStart_2208822 baseEnd_2208822 := by
    simpa [prefixWord, tailWord_2208822, baseEnd_2208822] using wordTrace_append hprefix tailTrace_2208822
  have hstable : (prefixWord ++ tailWord_2208822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208822).length < 2 ^ (prefixWord ++ tailWord_2208822).sum := by decide
  have hdescent : baseEnd_2208822 < baseStart_2208822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208838 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2208838 : Nat := 118140960795 + 2208838 * 2 ^ 59
def prefixEnd_2208838 : Nat := 4983230072969 + 3 ^ 40 * 2208838 * 2
def baseEnd_2208838 : Nat := 378065193971978048288915

theorem tailTrace_2208838 : CollatzResearch.WordTrace tailWord_2208838 prefixEnd_2208838 378065193971978048288915 := by
  unfold tailWord_2208838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517591886617645010685599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53708626914509760227959445 2517591886617645010685599)
  ·
    refine ⟨3776387829926467516028399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517591886617645010685599 3776387829926467516028399)
    ·
      refine ⟨5664581744889701274042599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776387829926467516028399 5664581744889701274042599)
      ·
        refine ⟨8496872617334551911063899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664581744889701274042599 8496872617334551911063899)
        ·
          refine ⟨12745308926001827866595849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8496872617334551911063899 12745308926001827866595849)
          ·
            refine ⟨9558981694501370899946887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12745308926001827866595849 9558981694501370899946887)
            ·
              refine ⟨14338472541752056349920331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9558981694501370899946887 14338472541752056349920331)
              ·
                refine ⟨21507708812628084524880497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14338472541752056349920331 21507708812628084524880497)
                ·
                  refine ⟨16130781609471063393660373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21507708812628084524880497 16130781609471063393660373)
                  ·
                    refine ⟨378065193971978048288915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16130781609471063393660373 378065193971978048288915)
                    ·
                      rfl

theorem cell23_2208838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2208838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208838 prefixEnd_2208838 := by exact prefixLift 2208838
  have htrace : WordTrace (prefixWord ++ tailWord_2208838) baseStart_2208838 baseEnd_2208838 := by
    simpa [prefixWord, tailWord_2208838, baseEnd_2208838] using wordTrace_append hprefix tailTrace_2208838
  have hstable : (prefixWord ++ tailWord_2208838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208838).length < 2 ^ (prefixWord ++ tailWord_2208838).sum := by decide
  have hdescent : baseEnd_2208838 < baseStart_2208838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208845 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_2208845 : Nat := 118140960795 + 2208845 * 2 ^ 59
def prefixEnd_2208845 : Nat := 4983230072969 + 3 ^ 40 * 2208845 * 2
def baseEnd_2208845 : Nat := 1134199176280515617479213

theorem tailTrace_2208845 : CollatzResearch.WordTrace tailWord_2208845 prefixEnd_2208845 1134199176280515617479213 := by
  unfold tailWord_2208845
  simp only [CollatzResearch.WordTrace]
  refine ⟨80563195682739280537443989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53708797121826187024962659 80563195682739280537443989)
  ·
    refine ⟨3776399797628403775192687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80563195682739280537443989 3776399797628403775192687)
    ·
      refine ⟨5664599696442605662789031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776399797628403775192687 5664599696442605662789031)
      ·
        refine ⟨8496899544663908494183547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664599696442605662789031 8496899544663908494183547)
        ·
          refine ⟨12745349316995862741275321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8496899544663908494183547 12745349316995862741275321)
          ·
            refine ⟨9559011987746897055956491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12745349316995862741275321 9559011987746897055956491)
            ·
              refine ⟨14338517981620345583934737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9559011987746897055956491 14338517981620345583934737)
              ·
                refine ⟨10753888486215259187951053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14338517981620345583934737 10753888486215259187951053)
                ·
                  refine ⟨4032708182330722195481645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10753888486215259187951053 4032708182330722195481645)
                  ·
                    refine ⟨1512265568374020823305617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4032708182330722195481645 1512265568374020823305617)
                    ·
                      refine ⟨1134199176280515617479213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512265568374020823305617 1134199176280515617479213)
                      ·
                        rfl

theorem cell23_2208845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_2208845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208845 prefixEnd_2208845 := by exact prefixLift 2208845
  have htrace : WordTrace (prefixWord ++ tailWord_2208845) baseStart_2208845 baseEnd_2208845 := by
    simpa [prefixWord, tailWord_2208845, baseEnd_2208845] using wordTrace_append hprefix tailTrace_2208845
  have hstable : (prefixWord ++ tailWord_2208845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208845).length < 2 ^ (prefixWord ++ tailWord_2208845).sum := by decide
  have hdescent : baseEnd_2208845 < baseStart_2208845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208931 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2208931 : Nat := 118140960795 + 2208931 * 2 ^ 59
def prefixEnd_2208931 : Nat := 4983230072969 + 3 ^ 40 * 2208931 * 2
def baseEnd_2208931 : Nat := 1134243335616802281003817

theorem tailTrace_2208931 : CollatzResearch.WordTrace tailWord_2208931 prefixEnd_2208931 1134243335616802281003817 := by
  unfold tailWord_2208931
  simp only [CollatzResearch.WordTrace]
  refine ⟨80566332360427717225074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53710888240285144816716431 80566332360427717225074647)
  ·
    refine ⟨120849498540641575837611971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80566332360427717225074647 120849498540641575837611971)
    ·
      refine ⟨181274247810962363756417957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120849498540641575837611971 181274247810962363756417957)
      ·
        refine ⟨33988921464555443204328367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181274247810962363756417957 33988921464555443204328367)
        ·
          refine ⟨50983382196833164806492551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33988921464555443204328367 50983382196833164806492551)
          ·
            refine ⟨76475073295249747209738827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50983382196833164806492551 76475073295249747209738827)
            ·
              refine ⟨114712609942874620814608241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76475073295249747209738827 114712609942874620814608241)
              ·
                refine ⟨86034457457155965610956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114712609942874620814608241 86034457457155965610956181)
                ·
                  refine ⟨4032865193304185888013571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86034457457155965610956181 4032865193304185888013571)
                  ·
                    refine ⟨6049297789956278832020357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4032865193304185888013571 6049297789956278832020357)
                    ·
                      refine ⟨1134243335616802281003817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6049297789956278832020357 1134243335616802281003817)
                      ·
                        rfl

theorem cell23_2208931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2208931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2208931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2208931 prefixEnd_2208931 := by exact prefixLift 2208931
  have htrace : WordTrace (prefixWord ++ tailWord_2208931) baseStart_2208931 baseEnd_2208931 := by
    simpa [prefixWord, tailWord_2208931, baseEnd_2208931] using wordTrace_append hprefix tailTrace_2208931
  have hstable : (prefixWord ++ tailWord_2208931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208931).length < 2 ^ (prefixWord ++ tailWord_2208931).sum := by decide
  have hdescent : baseEnd_2208931 < baseStart_2208931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209001 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_2209001 : Nat := 118140960795 + 2209001 * 2 ^ 59
def prefixEnd_2209001 : Nat := 4983230072969 + 3 ^ 40 * 2209001 * 2
def baseEnd_2209001 : Nat := 378093093087539002376165

theorem tailTrace_2209001 : CollatzResearch.WordTrace tailWord_2209001 prefixEnd_2209001 378093093087539002376165 := by
  unfold tailWord_2209001
  simp only [CollatzResearch.WordTrace]
  refine ⟨80568885470174119180122857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53712590313449412786748571 80568885470174119180122857)
  ·
    refine ⟨60426664102630589385092143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80568885470174119180122857 60426664102630589385092143)
    ·
      refine ⟨90639996153945884077638215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60426664102630589385092143 90639996153945884077638215)
      ·
        refine ⟨135959994230918826116457323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90639996153945884077638215 135959994230918826116457323)
        ·
          refine ⟨203939991346378239174685985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135959994230918826116457323 203939991346378239174685985)
          ·
            refine ⟨152954993509783679381014489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203939991346378239174685985 152954993509783679381014489)
            ·
              refine ⟨114716245132337759535760867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152954993509783679381014489 114716245132337759535760867)
              ·
                refine ⟨172074367698506639303641301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114716245132337759535760867 172074367698506639303641301)
                ·
                  refine ⟨4032992992933749358679093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 172074367698506639303641301 4032992992933749358679093)
                  ·
                    refine ⟨378093093087539002376165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4032992992933749358679093 378093093087539002376165)
                    ·
                      rfl

theorem cell23_2209001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_2209001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209001 prefixEnd_2209001 := by exact prefixLift 2209001
  have htrace : WordTrace (prefixWord ++ tailWord_2209001) baseStart_2209001 baseEnd_2209001 := by
    simpa [prefixWord, tailWord_2209001, baseEnd_2209001] using wordTrace_append hprefix tailTrace_2209001
  have hstable : (prefixWord ++ tailWord_2209001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209001).length < 2 ^ (prefixWord ++ tailWord_2209001).sum := by decide
  have hdescent : baseEnd_2209001 < baseStart_2209001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209005 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2209005 : Nat := 118140960795 + 2209005 * 2 ^ 59
def prefixEnd_2209005 : Nat := 4983230072969 + 3 ^ 40 * 2209005 * 2
def baseEnd_2209005 : Nat := 126031259242803887942053

theorem tailTrace_2209005 : CollatzResearch.WordTrace tailWord_2209005 prefixEnd_2209005 126031259242803887942053 := by
  unfold tailWord_2209005
  simp only [CollatzResearch.WordTrace]
  refine ⟨80569031362159627863268469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53712687574773085242178979 80569031362159627863268469)
  ·
    refine ⟨7553346690202465112181419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80569031362159627863268469 7553346690202465112181419)
    ·
      refine ⟨11330020035303697668272129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7553346690202465112181419 11330020035303697668272129)
      ·
        refine ⟨8497515026477773251204097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11330020035303697668272129 8497515026477773251204097)
        ·
          refine ⟨6373136269858329938403073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8497515026477773251204097 6373136269858329938403073)
          ·
            refine ⟨4779852202393747453802305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6373136269858329938403073 4779852202393747453802305)
            ·
              refine ⟨3584889151795310590351729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4779852202393747453802305 3584889151795310590351729)
              ·
                refine ⟨2688666863846482942763797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3584889151795310590351729 2688666863846482942763797)
                ·
                  refine ⟨126031259242803887942053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2688666863846482942763797 126031259242803887942053)
                  ·
                    rfl

theorem cell23_2209005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2209005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209005 prefixEnd_2209005 := by exact prefixLift 2209005
  have htrace : WordTrace (prefixWord ++ tailWord_2209005) baseStart_2209005 baseEnd_2209005 := by
    simpa [prefixWord, tailWord_2209005, baseEnd_2209005] using wordTrace_append hprefix tailTrace_2209005
  have hstable : (prefixWord ++ tailWord_2209005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209005).length < 2 ^ (prefixWord ++ tailWord_2209005).sum := by decide
  have hdescent : baseEnd_2209005 < baseStart_2209005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209008 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2]
def baseStart_2209008 : Nat := 118140960795 + 2209008 * 2 ^ 59
def prefixEnd_2209008 : Nat := 4983230072969 + 3 ^ 40 * 2209008 * 2
def baseEnd_2209008 : Nat := 1134282873627198479740963

theorem tailTrace_2209008 : CollatzResearch.WordTrace tailWord_2209008 prefixEnd_2209008 1134282873627198479740963 := by
  unfold tailWord_2209008
  simp only [CollatzResearch.WordTrace]
  refine ⟨40284570390574379687813839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53712760520765839583751785 40284570390574379687813839)
  ·
    refine ⟨60426855585861569531720759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40284570390574379687813839 60426855585861569531720759)
    ·
      refine ⟨90640283378792354297581139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60426855585861569531720759 90640283378792354297581139)
      ·
        refine ⟨135960425068188531446371709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90640283378792354297581139 135960425068188531446371709)
        ·
          refine ⟨50985159400570699292389391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135960425068188531446371709 50985159400570699292389391)
          ·
            refine ⟨76477739100856048938584087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50985159400570699292389391 76477739100856048938584087)
            ·
              refine ⟨114716608651284073407876131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76477739100856048938584087 114716608651284073407876131)
              ·
                refine ⟨172074912976926110111814197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114716608651284073407876131 172074912976926110111814197)
                ·
                  refine ⟨16132023091586822822982581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172074912976926110111814197 16132023091586822822982581)
                  ·
                    refine ⟨1512377164836264639654617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16132023091586822822982581 1512377164836264639654617)
                    ·
                      refine ⟨1134282873627198479740963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512377164836264639654617 1134282873627198479740963)
                      ·
                        rfl

theorem cell23_2209008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2].length) (baseStart_2209008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209008 prefixEnd_2209008 := by exact prefixLift 2209008
  have htrace : WordTrace (prefixWord ++ tailWord_2209008) baseStart_2209008 baseEnd_2209008 := by
    simpa [prefixWord, tailWord_2209008, baseEnd_2209008] using wordTrace_append hprefix tailTrace_2209008
  have hstable : (prefixWord ++ tailWord_2209008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209008).length < 2 ^ (prefixWord ++ tailWord_2209008).sum := by decide
  have hdescent : baseEnd_2209008 < baseStart_2209008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209032 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_2209032 : Nat := 118140960795 + 2209032 * 2 ^ 59
def prefixEnd_2209032 : Nat := 4983230072969 + 3 ^ 40 * 2209032 * 2
def baseEnd_2209032 : Nat := 1134295197162906385840853

theorem tailTrace_2209032 : CollatzResearch.WordTrace tailWord_2209032 prefixEnd_2209032 1134295197162906385840853 := by
  unfold tailWord_2209032
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285008066530905737250675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53713344088707874316334233 40285008066530905737250675)
  ·
    refine ⟨60427512099796358605876013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40285008066530905737250675 60427512099796358605876013)
    ·
      refine ⟨22660317037423634477203505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60427512099796358605876013 22660317037423634477203505)
      ·
        refine ⟨16995237778067725857902629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22660317037423634477203505 16995237778067725857902629)
        ·
          refine ⟨3186607083387698598356743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16995237778067725857902629 3186607083387698598356743)
          ·
            refine ⟨4779910625081547897535115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3186607083387698598356743 4779910625081547897535115)
            ·
              refine ⟨7169865937622321846302673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4779910625081547897535115 7169865937622321846302673)
              ·
                refine ⟨5377399453216741384727005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7169865937622321846302673 5377399453216741384727005)
                ·
                  refine ⟨2016524794956278019272627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5377399453216741384727005 2016524794956278019272627)
                  ·
                    refine ⟨3024787192434417028908941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2016524794956278019272627 3024787192434417028908941)
                    ·
                      refine ⟨1134295197162906385840853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024787192434417028908941 1134295197162906385840853)
                      ·
                        rfl

theorem cell23_2209032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_2209032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209032 prefixEnd_2209032 := by exact prefixLift 2209032
  have htrace : WordTrace (prefixWord ++ tailWord_2209032) baseStart_2209032 baseEnd_2209032 := by
    simpa [prefixWord, tailWord_2209032, baseEnd_2209032] using wordTrace_append hprefix tailTrace_2209032
  have hstable : (prefixWord ++ tailWord_2209032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209032).length < 2 ^ (prefixWord ++ tailWord_2209032).sum := by decide
  have hdescent : baseEnd_2209032 < baseStart_2209032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209048 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_2209048 : Nat := 118140960795 + 2209048 * 2 ^ 59
def prefixEnd_2209048 : Nat := 4983230072969 + 3 ^ 40 * 2209048 * 2
def baseEnd_2209048 : Nat := 378101137617792774413593

theorem tailTrace_2209048 : CollatzResearch.WordTrace tailWord_2209048 prefixEnd_2209048 378101137617792774413593 := by
  unfold tailWord_2209048
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285299850501923103541899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53713733134002564138055865 40285299850501923103541899)
  ·
    refine ⟨60427949775752884655312849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40285299850501923103541899 60427949775752884655312849)
    ·
      refine ⟨45320962331814663491484637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60427949775752884655312849 45320962331814663491484637)
      ·
        refine ⟨16995360874430498809306739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45320962331814663491484637 16995360874430498809306739)
        ·
          refine ⟨25493041311645748213960109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16995360874430498809306739 25493041311645748213960109)
          ·
            refine ⟨9559890491867155580235041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25493041311645748213960109 9559890491867155580235041)
            ·
              refine ⟨7169917868900366685176281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9559890491867155580235041 7169917868900366685176281)
              ·
                refine ⟨5377438401675275013882211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7169917868900366685176281 5377438401675275013882211)
                ·
                  refine ⟨8066157602512912520823317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5377438401675275013882211 8066157602512912520823317)
                  ·
                    refine ⟨378101137617792774413593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8066157602512912520823317 378101137617792774413593)
                    ·
                      rfl

theorem cell23_2209048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_2209048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209048 prefixEnd_2209048 := by exact prefixLift 2209048
  have htrace : WordTrace (prefixWord ++ tailWord_2209048) baseStart_2209048 baseEnd_2209048 := by
    simpa [prefixWord, tailWord_2209048, baseEnd_2209048] using wordTrace_append hprefix tailTrace_2209048
  have hstable : (prefixWord ++ tailWord_2209048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209048).length < 2 ^ (prefixWord ++ tailWord_2209048).sum := by decide
  have hdescent : baseEnd_2209048 < baseStart_2209048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209051 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_2209051 : Nat := 118140960795 + 2209051 * 2 ^ 59
def prefixEnd_2209051 : Nat := 4983230072969 + 3 ^ 40 * 2209051 * 2
def baseEnd_2209051 : Nat := 1134304953295341811503265

theorem tailTrace_2209051 : CollatzResearch.WordTrace tailWord_2209051 prefixEnd_2209051 1134304953295341811503265 := by
  unfold tailWord_2209051
  simp only [CollatzResearch.WordTrace]
  refine ⟨80570709119992977719443007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53713806079995318479628671 80570709119992977719443007)
  ·
    refine ⟨120856063679989466579164511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80570709119992977719443007 120856063679989466579164511)
    ·
      refine ⟨181284095519984199868746767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120856063679989466579164511 181284095519984199868746767)
      ·
        refine ⟨271926143279976299803120151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181284095519984199868746767 271926143279976299803120151)
        ·
          refine ⟨407889214919964449704680227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271926143279976299803120151 407889214919964449704680227)
          ·
            refine ⟨611833822379946674557020341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407889214919964449704680227 611833822379946674557020341)
            ·
              refine ⟨57359420848120000739720657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 611833822379946674557020341 57359420848120000739720657)
              ·
                refine ⟨43019565636090000554790493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57359420848120000739720657 43019565636090000554790493)
                ·
                  refine ⟨16132337113533750208046435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43019565636090000554790493 16132337113533750208046435)
                  ·
                    refine ⟨24198505670300625312069653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16132337113533750208046435 24198505670300625312069653)
                    ·
                      refine ⟨1134304953295341811503265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24198505670300625312069653 1134304953295341811503265)
                      ·
                        rfl

theorem cell23_2209051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_2209051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209051 prefixEnd_2209051 := by exact prefixLift 2209051
  have htrace : WordTrace (prefixWord ++ tailWord_2209051) baseStart_2209051 baseEnd_2209051 := by
    simpa [prefixWord, tailWord_2209051, baseEnd_2209051] using wordTrace_append hprefix tailTrace_2209051
  have hstable : (prefixWord ++ tailWord_2209051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209051).length < 2 ^ (prefixWord ++ tailWord_2209051).sum := by decide
  have hdescent : baseEnd_2209051 < baseStart_2209051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209071 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_2209071 : Nat := 118140960795 + 2209071 * 2 ^ 59
def prefixEnd_2209071 : Nat := 4983230072969 + 3 ^ 40 * 2209071 * 2
def baseEnd_2209071 : Nat := 1134315222908431733253173

theorem tailTrace_2209071 : CollatzResearch.WordTrace tailWord_2209071 prefixEnd_2209071 1134315222908431733253173 := by
  unfold tailWord_2209071
  simp only [CollatzResearch.WordTrace]
  refine ⟨80571438579920521135171067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53714292386613680756780711 80571438579920521135171067)
  ·
    refine ⟨120857157869880781702756601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80571438579920521135171067 120857157869880781702756601)
    ·
      refine ⟨90642868402410586277067451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120857157869880781702756601 90642868402410586277067451)
      ·
        refine ⟨135964302603615879415601177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90642868402410586277067451 135964302603615879415601177)
        ·
          refine ⟨101973226952711909561700883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135964302603615879415601177 101973226952711909561700883)
          ·
            refine ⟨152959840429067864342551325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101973226952711909561700883 152959840429067864342551325)
            ·
              refine ⟨57359940160900449128456747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152959840429067864342551325 57359940160900449128456747)
              ·
                refine ⟨86039910241350673692685121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57359940160900449128456747 86039910241350673692685121)
                ·
                  refine ⟨64529932681013005269513841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86039910241350673692685121 64529932681013005269513841)
                  ·
                    refine ⟨48397449510759753952135381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64529932681013005269513841 48397449510759753952135381)
                    ·
                      refine ⟨1134315222908431733253173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48397449510759753952135381 1134315222908431733253173)
                      ·
                        rfl

theorem cell23_2209071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_2209071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209071 prefixEnd_2209071 := by exact prefixLift 2209071
  have htrace : WordTrace (prefixWord ++ tailWord_2209071) baseStart_2209071 baseEnd_2209071 := by
    simpa [prefixWord, tailWord_2209071, baseEnd_2209071] using wordTrace_append hprefix tailTrace_2209071
  have hstable : (prefixWord ++ tailWord_2209071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209071).length < 2 ^ (prefixWord ++ tailWord_2209071).sum := by decide
  have hdescent : baseEnd_2209071 < baseStart_2209071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209072 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2]
def baseStart_2209072 : Nat := 118140960795 + 2209072 * 2 ^ 59
def prefixEnd_2209072 : Nat := 4983230072969 + 3 ^ 40 * 2209072 * 2
def baseEnd_2209072 : Nat := 1134315736389086229340669

theorem tailTrace_2209072 : CollatzResearch.WordTrace tailWord_2209072 prefixEnd_2209072 1134315736389086229340669 := by
  unfold tailWord_2209072
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285737526458449152978735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53714316701944598870638313 40285737526458449152978735)
  ·
    refine ⟨60428606289687673729468103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40285737526458449152978735 60428606289687673729468103)
    ·
      refine ⟨90642909434531510594202155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60428606289687673729468103 90642909434531510594202155)
      ·
        refine ⟨135964364151797265891303233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90642909434531510594202155 135964364151797265891303233)
        ·
          refine ⟨101973273113847949418477425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135964364151797265891303233 101973273113847949418477425)
          ·
            refine ⟨76479954835385962063858069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101973273113847949418477425 76479954835385962063858069)
            ·
              refine ⟨3584997882908716971743347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76479954835385962063858069 3584997882908716971743347)
              ·
                refine ⟨5377496824363075457615021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584997882908716971743347 5377496824363075457615021)
                ·
                  refine ⟨2016561309136153296605633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5377496824363075457615021 2016561309136153296605633)
                  ·
                    refine ⟨1512420981852114972454225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016561309136153296605633 1512420981852114972454225)
                    ·
                      refine ⟨1134315736389086229340669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512420981852114972454225 1134315736389086229340669)
                      ·
                        rfl

theorem cell23_2209072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 2, 2].length) (baseStart_2209072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209072 prefixEnd_2209072 := by exact prefixLift 2209072
  have htrace : WordTrace (prefixWord ++ tailWord_2209072) baseStart_2209072 baseEnd_2209072 := by
    simpa [prefixWord, tailWord_2209072, baseEnd_2209072] using wordTrace_append hprefix tailTrace_2209072
  have hstable : (prefixWord ++ tailWord_2209072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209072).length < 2 ^ (prefixWord ++ tailWord_2209072).sum := by decide
  have hdescent : baseEnd_2209072 < baseStart_2209072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209082 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_2209082 : Nat := 118140960795 + 2209082 * 2 ^ 59
def prefixEnd_2209082 : Nat := 4983230072969 + 3 ^ 40 * 2209082 * 2
def baseEnd_2209082 : Nat := 378106957065210396738541

theorem tailTrace_2209082 : CollatzResearch.WordTrace tailWord_2209082 prefixEnd_2209082 378106957065210396738541 := by
  unfold tailWord_2209082
  simp only [CollatzResearch.WordTrace]
  refine ⟨20142959945720167503455375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53714559855253780009214333 20142959945720167503455375)
  ·
    refine ⟨30214439918580251255183063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20142959945720167503455375 30214439918580251255183063)
    ·
      refine ⟨45321659877870376882774595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30214439918580251255183063 45321659877870376882774595)
      ·
        refine ⟨67982489816805565324161893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45321659877870376882774595 67982489816805565324161893)
        ·
          refine ⟨12746716840651043498280355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67982489816805565324161893 12746716840651043498280355)
          ·
            refine ⟨19120075260976565247420533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12746716840651043498280355 19120075260976565247420533)
            ·
              refine ⟨1792507055716552991945675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19120075260976565247420533 1792507055716552991945675)
              ·
                refine ⟨2688760583574829487918513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792507055716552991945675 2688760583574829487918513)
                ·
                  refine ⟨2016570437681122115938885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2688760583574829487918513 2016570437681122115938885)
                  ·
                    refine ⟨378106957065210396738541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2016570437681122115938885 378106957065210396738541)
                    ·
                      rfl

theorem cell23_2209082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_2209082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209082 prefixEnd_2209082 := by exact prefixLift 2209082
  have htrace : WordTrace (prefixWord ++ tailWord_2209082) baseStart_2209082 baseEnd_2209082 := by
    simpa [prefixWord, tailWord_2209082, baseEnd_2209082] using wordTrace_append hprefix tailTrace_2209082
  have hstable : (prefixWord ++ tailWord_2209082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209082).length < 2 ^ (prefixWord ++ tailWord_2209082).sum := by decide
  have hdescent : baseEnd_2209082 < baseStart_2209082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209089 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2209089 : Nat := 118140960795 + 2209089 * 2 ^ 59
def prefixEnd_2209089 : Nat := 4983230072969 + 3 ^ 40 * 2209089 * 2
def baseEnd_2209089 : Nat := 1134324465560212662828091

theorem tailTrace_2209089 : CollatzResearch.WordTrace tailWord_2209089 prefixEnd_2209089 1134324465560212662828091 := by
  unfold tailWord_2209089
  simp only [CollatzResearch.WordTrace]
  refine ⟨80572095093855310209326321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53714730062570206806217547 80572095093855310209326321)
  ·
    refine ⟨60429071320391482656994741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80572095093855310209326321 60429071320391482656994741)
    ·
      refine ⟨5665225436286701499093257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60429071320391482656994741 5665225436286701499093257)
      ·
        refine ⟨4248919077215026124319943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5665225436286701499093257 4248919077215026124319943)
        ·
          refine ⟨6373378615822539186479915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248919077215026124319943 6373378615822539186479915)
          ·
            refine ⟨9560067923733808779719873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6373378615822539186479915 9560067923733808779719873)
            ·
              refine ⟨7170050942800356584789905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9560067923733808779719873 7170050942800356584789905)
              ·
                refine ⟨5377538207100267438592429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7170050942800356584789905 5377538207100267438592429)
                ·
                  refine ⟨2016576827662600289472161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5377538207100267438592429 2016576827662600289472161)
                  ·
                    refine ⟨1512432620746950217104121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016576827662600289472161 1512432620746950217104121)
                    ·
                      refine ⟨1134324465560212662828091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512432620746950217104121 1134324465560212662828091)
                      ·
                        rfl

theorem cell23_2209089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2209089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209089 prefixEnd_2209089 := by exact prefixLift 2209089
  have htrace : WordTrace (prefixWord ++ tailWord_2209089) baseStart_2209089 baseEnd_2209089 := by
    simpa [prefixWord, tailWord_2209089, baseEnd_2209089] using wordTrace_append hprefix tailTrace_2209089
  have hstable : (prefixWord ++ tailWord_2209089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209089).length < 2 ^ (prefixWord ++ tailWord_2209089).sum := by decide
  have hdescent : baseEnd_2209089 < baseStart_2209089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209095 : List Nat := [1, 1, 4, 1, 2, 5, 2, 7]
def baseStart_2209095 : Nat := 118140960795 + 2209095 * 2 ^ 59
def prefixEnd_2209095 : Nat := 4983230072969 + 3 ^ 40 * 2209095 * 2
def baseEnd_2209095 : Nat := 42012131349782949605669

theorem tailTrace_2209095 : CollatzResearch.WordTrace tailWord_2209095 prefixEnd_2209095 42012131349782949605669 := by
  unfold tailWord_2209095
  simp only [CollatzResearch.WordTrace]
  refine ⟨80572313931833573234044739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53714875954555715489363159 80572313931833573234044739)
  ·
    refine ⟨120858470897750359851067109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80572313931833573234044739 120858470897750359851067109)
    ·
      refine ⟨22660963293328192472075083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120858470897750359851067109 22660963293328192472075083)
      ·
        refine ⟨33991444939992288708112625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22660963293328192472075083 33991444939992288708112625)
        ·
          refine ⟨25493583704994216531084469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33991444939992288708112625 25493583704994216531084469)
          ·
            refine ⟨2390023472343207799789169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25493583704994216531084469 2390023472343207799789169)
            ·
              refine ⟨1792517604257405849841877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390023472343207799789169 1792517604257405849841877)
              ·
                refine ⟨42012131349782949605669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1792517604257405849841877 42012131349782949605669)
                ·
                  rfl

theorem cell23_2209095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 7].length) (baseStart_2209095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209095 prefixEnd_2209095 := by exact prefixLift 2209095
  have htrace : WordTrace (prefixWord ++ tailWord_2209095) baseStart_2209095 baseEnd_2209095 := by
    simpa [prefixWord, tailWord_2209095, baseEnd_2209095] using wordTrace_append hprefix tailTrace_2209095
  have hstable : (prefixWord ++ tailWord_2209095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209095).length < 2 ^ (prefixWord ++ tailWord_2209095).sum := by decide
  have hdescent : baseEnd_2209095 < baseStart_2209095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209105 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_2209105 : Nat := 118140960795 + 2209105 * 2 ^ 59
def prefixEnd_2209105 : Nat := 4983230072969 + 3 ^ 40 * 2209105 * 2
def baseEnd_2209105 : Nat := 1134332681250684600228017

theorem tailTrace_2209105 : CollatzResearch.WordTrace tailWord_2209105 prefixEnd_2209105 1134332681250684600228017 := by
  unfold tailWord_2209105
  simp only [CollatzResearch.WordTrace]
  refine ⟨80572678661797344941908769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53715119107864896627939179 80572678661797344941908769)
  ·
    refine ⟨60429508996348008706431577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80572678661797344941908769 60429508996348008706431577)
    ·
      refine ⟨45322131747261006529823683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60429508996348008706431577 45322131747261006529823683)
      ·
        refine ⟨67983197620891509794735525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45322131747261006529823683 67983197620891509794735525)
        ·
          refine ⟨12746849553917158086512911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67983197620891509794735525 12746849553917158086512911)
          ·
            refine ⟨19120274330875737129769367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12746849553917158086512911 19120274330875737129769367)
            ·
              refine ⟨28680411496313605694654051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19120274330875737129769367 28680411496313605694654051)
              ·
                refine ⟨43020617244470408541981077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28680411496313605694654051 43020617244470408541981077)
                ·
                  refine ⟨2016591433334550400405363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43020617244470408541981077 2016591433334550400405363)
                  ·
                    refine ⟨3024887150001825600608045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2016591433334550400405363 3024887150001825600608045)
                    ·
                      refine ⟨1134332681250684600228017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024887150001825600608045 1134332681250684600228017)
                      ·
                        rfl

theorem cell23_2209105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_2209105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209105 prefixEnd_2209105 := by exact prefixLift 2209105
  have htrace : WordTrace (prefixWord ++ tailWord_2209105) baseStart_2209105 baseEnd_2209105 := by
    simpa [prefixWord, tailWord_2209105, baseEnd_2209105] using wordTrace_append hprefix tailTrace_2209105
  have hstable : (prefixWord ++ tailWord_2209105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209105).length < 2 ^ (prefixWord ++ tailWord_2209105).sum := by decide
  have hdescent : baseEnd_2209105 < baseStart_2209105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209122 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2209122 : Nat := 118140960795 + 2209122 * 2 ^ 59
def prefixEnd_2209122 : Nat := 4983230072969 + 3 ^ 40 * 2209122 * 2
def baseEnd_2209122 : Nat := 1134341410421811033715439

theorem tailTrace_2209122 : CollatzResearch.WordTrace tailWord_2209122 prefixEnd_2209122 1134341410421811033715439 := by
  unfold tailWord_2209122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20143324675683939211319405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53715532468490504563518413 20143324675683939211319405)
  ·
    refine ⟨7553746753381477204244777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20143324675683939211319405 7553746753381477204244777)
    ·
      refine ⟨5665310065036107903183583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7553746753381477204244777 5665310065036107903183583)
      ·
        refine ⟨8497965097554161854775375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665310065036107903183583 8497965097554161854775375)
        ·
          refine ⟨12746947646331242782163063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8497965097554161854775375 12746947646331242782163063)
          ·
            refine ⟨19120421469496864173244595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12746947646331242782163063 19120421469496864173244595)
            ·
              refine ⟨28680632204245296259866893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19120421469496864173244595 28680632204245296259866893)
              ·
                refine ⟨10755237076591986097450085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28680632204245296259866893 10755237076591986097450085)
                ·
                  refine ⟨2016606951860997393271891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10755237076591986097450085 2016606951860997393271891)
                  ·
                    refine ⟨3024910427791496089907837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2016606951860997393271891 3024910427791496089907837)
                    ·
                      refine ⟨1134341410421811033715439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3024910427791496089907837 1134341410421811033715439)
                      ·
                        rfl

theorem cell23_2209122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2209122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209122 prefixEnd_2209122 := by exact prefixLift 2209122
  have htrace : WordTrace (prefixWord ++ tailWord_2209122) baseStart_2209122 baseEnd_2209122 := by
    simpa [prefixWord, tailWord_2209122, baseEnd_2209122] using wordTrace_append hprefix tailTrace_2209122
  have hstable : (prefixWord ++ tailWord_2209122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209122).length < 2 ^ (prefixWord ++ tailWord_2209122).sum := by decide
  have hdescent : baseEnd_2209122 < baseStart_2209122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209138 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_2209138 : Nat := 118140960795 + 2209138 * 2 ^ 59
def prefixEnd_2209138 : Nat := 4983230072969 + 3 ^ 40 * 2209138 * 2
def baseEnd_2209138 : Nat := 378116542037427657038455

theorem tailTrace_2209138 : CollatzResearch.WordTrace tailWord_2209138 prefixEnd_2209138 378116542037427657038455 := by
  unfold tailWord_2209138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20143470567669447894465017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53715921513785194385240045 20143470567669447894465017)
  ·
    refine ⟨15107602925752085920848763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20143470567669447894465017 15107602925752085920848763)
    ·
      refine ⟨22661404388628128881273145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15107602925752085920848763 22661404388628128881273145)
      ·
        refine ⟨16996053291471096660954859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22661404388628128881273145 16996053291471096660954859)
        ·
          refine ⟨25494079937206644991432289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16996053291471096660954859 25494079937206644991432289)
          ·
            refine ⟨19120559952904983743574217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25494079937206644991432289 19120559952904983743574217)
            ·
              refine ⟨14340419964678737807680663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19120559952904983743574217 14340419964678737807680663)
              ·
                refine ⟨21510629947018106711520995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14340419964678737807680663 21510629947018106711520995)
                ·
                  refine ⟨32265944920527160067281493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21510629947018106711520995 32265944920527160067281493)
                  ·
                    refine ⟨378116542037427657038455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32265944920527160067281493 378116542037427657038455)
                    ·
                      rfl

theorem cell23_2209138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_2209138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209138 prefixEnd_2209138 := by exact prefixLift 2209138
  have htrace : WordTrace (prefixWord ++ tailWord_2209138) baseStart_2209138 baseEnd_2209138 := by
    simpa [prefixWord, tailWord_2209138, baseEnd_2209138] using wordTrace_append hprefix tailTrace_2209138
  have hstable : (prefixWord ++ tailWord_2209138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209138).length < 2 ^ (prefixWord ++ tailWord_2209138).sum := by decide
  have hdescent : baseEnd_2209138 < baseStart_2209138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209148 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2209148 : Nat := 118140960795 + 2209148 * 2 ^ 59
def prefixEnd_2209148 : Nat := 4983230072969 + 3 ^ 40 * 2209148 * 2
def baseEnd_2209148 : Nat := 1134354760918827931990319

theorem tailTrace_2209148 : CollatzResearch.WordTrace tailWord_2209148 prefixEnd_2209148 1134354760918827931990319 := by
  unfold tailWord_2209148
  simp only [CollatzResearch.WordTrace]
  refine ⟨40287123500320781642862049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53716164667094375523816065 40287123500320781642862049)
  ·
    refine ⟨30215342625240586232146537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40287123500320781642862049 30215342625240586232146537)
    ·
      refine ⟨22661506968930439674109903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30215342625240586232146537 22661506968930439674109903)
      ·
        refine ⟨33992260453395659511164855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22661506968930439674109903 33992260453395659511164855)
        ·
          refine ⟨50988390680093489266747283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33992260453395659511164855 50988390680093489266747283)
          ·
            refine ⟨76482586020140233900120925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50988390680093489266747283 76482586020140233900120925)
            ·
              refine ⟨28680969757552587712545347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76482586020140233900120925 28680969757552587712545347)
              ·
                refine ⟨43021454636328881568818021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28680969757552587712545347 43021454636328881568818021)
                ·
                  refine ⟨8066522744311665294153379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43021454636328881568818021 8066522744311665294153379)
                  ·
                    refine ⟨12099784116467497941230069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8066522744311665294153379 12099784116467497941230069)
                    ·
                      refine ⟨1134354760918827931990319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12099784116467497941230069 1134354760918827931990319)
                      ·
                        rfl

theorem cell23_2209148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2209148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209148 prefixEnd_2209148 := by exact prefixLift 2209148
  have htrace : WordTrace (prefixWord ++ tailWord_2209148) baseStart_2209148 baseEnd_2209148 := by
    simpa [prefixWord, tailWord_2209148, baseEnd_2209148] using wordTrace_append hprefix tailTrace_2209148
  have hstable : (prefixWord ++ tailWord_2209148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209148).length < 2 ^ (prefixWord ++ tailWord_2209148).sum := by decide
  have hdescent : baseEnd_2209148 < baseStart_2209148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209188 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2209188 : Nat := 118140960795 + 2209188 * 2 ^ 59
def prefixEnd_2209188 : Nat := 4983230072969 + 3 ^ 40 * 2209188 * 2
def baseEnd_2209188 : Nat := 1134375300145007775490135

theorem tailTrace_2209188 : CollatzResearch.WordTrace tailWord_2209188 prefixEnd_2209188 1134375300145007775490135 := by
  unfold tailWord_2209188
  simp only [CollatzResearch.WordTrace]
  refine ⟨40287852960248325058590109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53717137280331100078120145 40287852960248325058590109)
  ·
    refine ⟨15107944860093121896971291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40287852960248325058590109 15107944860093121896971291)
    ·
      refine ⟨22661917290139682845456937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15107944860093121896971291 22661917290139682845456937)
      ·
        refine ⟨16996437967604762134092703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22661917290139682845456937 16996437967604762134092703)
        ·
          refine ⟨25494656951407143201139055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16996437967604762134092703 25494656951407143201139055)
          ·
            refine ⟨38241985427110714801708583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25494656951407143201139055 38241985427110714801708583)
            ·
              refine ⟨57362978140666072202562875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38241985427110714801708583 57362978140666072202562875)
              ·
                refine ⟨86044467210999108303844313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57362978140666072202562875 86044467210999108303844313)
                ·
                  refine ⟨64533350408249331227883235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86044467210999108303844313 64533350408249331227883235)
                  ·
                    refine ⟨96800025612373996841824853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64533350408249331227883235 96800025612373996841824853)
                    ·
                      refine ⟨1134375300145007775490135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 96800025612373996841824853 1134375300145007775490135)
                      ·
                        rfl

theorem cell23_2209188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2209188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209188 prefixEnd_2209188 := by exact prefixLift 2209188
  have htrace : WordTrace (prefixWord ++ tailWord_2209188) baseStart_2209188 baseEnd_2209188 := by
    simpa [prefixWord, tailWord_2209188, baseEnd_2209188] using wordTrace_append hprefix tailTrace_2209188
  have hstable : (prefixWord ++ tailWord_2209188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209188).length < 2 ^ (prefixWord ++ tailWord_2209188).sum := by decide
  have hdescent : baseEnd_2209188 < baseStart_2209188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209208 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2209208 : Nat := 118140960795 + 2209208 * 2 ^ 59
def prefixEnd_2209208 : Nat := 4983230072969 + 3 ^ 40 * 2209208 * 2
def baseEnd_2209208 : Nat := 1134385569758097697240043

theorem tailTrace_2209208 : CollatzResearch.WordTrace tailWord_2209208 prefixEnd_2209208 1134385569758097697240043 := by
  unfold tailWord_2209208
  simp only [CollatzResearch.WordTrace]
  refine ⟨40288217690212096766454139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53717623586949462355272185 40288217690212096766454139)
  ·
    refine ⟨60432326535318145149681209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40288217690212096766454139 60432326535318145149681209)
    ·
      refine ⟨45324244901488608862260907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60432326535318145149681209 45324244901488608862260907)
      ·
        refine ⟨67986367352232913293391361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45324244901488608862260907 67986367352232913293391361)
        ·
          refine ⟨50989775514174684970043521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67986367352232913293391361 50989775514174684970043521)
          ·
            refine ⟨38242331635631013727532641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50989775514174684970043521 38242331635631013727532641)
            ·
              refine ⟨28681748726723260295649481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38242331635631013727532641 28681748726723260295649481)
              ·
                refine ⟨21511311545042445221737111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28681748726723260295649481 21511311545042445221737111)
                ·
                  refine ⟨32266967317563667832605667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21511311545042445221737111 32266967317563667832605667)
                  ·
                    refine ⟨48400450976345501748908501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32266967317563667832605667 48400450976345501748908501)
                    ·
                      refine ⟨1134385569758097697240043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48400450976345501748908501 1134385569758097697240043)
                      ·
                        rfl

theorem cell23_2209208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2209208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209208 prefixEnd_2209208 := by exact prefixLift 2209208
  have htrace : WordTrace (prefixWord ++ tailWord_2209208) baseStart_2209208 baseEnd_2209208 := by
    simpa [prefixWord, tailWord_2209208, baseEnd_2209208] using wordTrace_append hprefix tailTrace_2209208
  have hstable : (prefixWord ++ tailWord_2209208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209208).length < 2 ^ (prefixWord ++ tailWord_2209208).sum := by decide
  have hdescent : baseEnd_2209208 < baseStart_2209208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209235 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 10, 2]
def baseStart_2209235 : Nat := 118140960795 + 2209235 * 2 ^ 59
def prefixEnd_2209235 : Nat := 4983230072969 + 3 ^ 40 * 2209235 * 2
def baseEnd_2209235 : Nat := 1134399433735769091602419

theorem tailTrace_2209235 : CollatzResearch.WordTrace tailWord_2209235 prefixEnd_2209235 1134399433735769091602419 := by
  unfold tailWord_2209235
  simp only [CollatzResearch.WordTrace]
  refine ⟨80577420151326377144141159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53718280100884251429427439 80577420151326377144141159)
  ·
    refine ⟨120866130226989565716211739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80577420151326377144141159 120866130226989565716211739)
    ·
      refine ⟨181299195340484348574317609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120866130226989565716211739 181299195340484348574317609)
      ·
        refine ⟨135974396505363261430738207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181299195340484348574317609 135974396505363261430738207)
        ·
          refine ⟨203961594758044892146107311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135974396505363261430738207 203961594758044892146107311)
          ·
            refine ⟨305942392137067338219160967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203961594758044892146107311 305942392137067338219160967)
            ·
              refine ⟨458913588205601007328741451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305942392137067338219160967 458913588205601007328741451)
              ·
                refine ⟨688370382308401510993112177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458913588205601007328741451 688370382308401510993112177)
                ·
                  refine ⟨516277786731301133244834133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688370382308401510993112177 516277786731301133244834133)
                  ·
                    refine ⟨1512532578314358788803225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 516277786731301133244834133 1512532578314358788803225)
                    ·
                      refine ⟨1134399433735769091602419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512532578314358788803225 1134399433735769091602419)
                      ·
                        rfl

theorem cell23_2209235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10, 2].length) (baseStart_2209235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209235 prefixEnd_2209235 := by exact prefixLift 2209235
  have htrace : WordTrace (prefixWord ++ tailWord_2209235) baseStart_2209235 baseEnd_2209235 := by
    simpa [prefixWord, tailWord_2209235, baseEnd_2209235] using wordTrace_append hprefix tailTrace_2209235
  have hstable : (prefixWord ++ tailWord_2209235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209235).length < 2 ^ (prefixWord ++ tailWord_2209235).sum := by decide
  have hdescent : baseEnd_2209235 < baseStart_2209235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209262 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2209262 : Nat := 118140960795 + 2209262 * 2 ^ 59
def prefixEnd_2209262 : Nat := 4983230072969 + 3 ^ 40 * 2209262 * 2
def baseEnd_2209262 : Nat := 378137765904480161988265

theorem tailTrace_2209262 : CollatzResearch.WordTrace tailWord_2209262 prefixEnd_2209262 378137765904480161988265 := by
  unfold tailWord_2209262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10072300615278570094421755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53718936614819040503582693 10072300615278570094421755)
  ·
    refine ⟨15108450922917855141632633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10072300615278570094421755 15108450922917855141632633)
    ·
      refine ⟨11331338192188391356224475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15108450922917855141632633 11331338192188391356224475)
      ·
        refine ⟨16997007288282587034336713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331338192188391356224475 16997007288282587034336713)
        ·
          refine ⟨12747755466211940275752535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16997007288282587034336713 12747755466211940275752535)
          ·
            refine ⟨19121633199317910413628803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12747755466211940275752535 19121633199317910413628803)
            ·
              refine ⟨28682449798976865620443205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19121633199317910413628803 28682449798976865620443205)
              ·
                refine ⟨5377959337308162303833101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28682449798976865620443205 5377959337308162303833101)
                ·
                  refine ⟨2016734751490560863937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5377959337308162303833101 2016734751490560863937413)
                  ·
                    refine ⟨378137765904480161988265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2016734751490560863937413 378137765904480161988265)
                    ·
                      rfl

theorem cell23_2209262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2209262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209262 prefixEnd_2209262 := by exact prefixLift 2209262
  have htrace : WordTrace (prefixWord ++ tailWord_2209262) baseStart_2209262 baseEnd_2209262 := by
    simpa [prefixWord, tailWord_2209262, baseEnd_2209262] using wordTrace_append hprefix tailTrace_2209262
  have hstable : (prefixWord ++ tailWord_2209262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209262).length < 2 ^ (prefixWord ++ tailWord_2209262).sum := by decide
  have hdescent : baseEnd_2209262 < baseStart_2209262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209322 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2209322 : Nat := 118140960795 + 2209322 * 2 ^ 59
def prefixEnd_2209322 : Nat := 4983230072969 + 3 ^ 40 * 2209322 * 2
def baseEnd_2209322 : Nat := 378148035517570083738173

theorem tailTrace_2209322 : CollatzResearch.WordTrace tailWord_2209322 prefixEnd_2209322 378148035517570083738173 := by
  unfold tailWord_2209322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20145148325502797750639555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53720395534674127335038813 20145148325502797750639555)
  ·
    refine ⟨30217722488254196625959333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20145148325502797750639555 30217722488254196625959333)
    ·
      refine ⟨5665822966547661867367375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30217722488254196625959333 5665822966547661867367375)
      ·
        refine ⟨8498734449821492801051063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665822966547661867367375 8498734449821492801051063)
        ·
          refine ⟨12748101674732239201576595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498734449821492801051063 12748101674732239201576595)
          ·
            refine ⟨19122152512098358802364893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12748101674732239201576595 19122152512098358802364893)
            ·
              refine ⟨7170807192036884550886835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19122152512098358802364893 7170807192036884550886835)
              ·
                refine ⟨10756210788055326826330253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7170807192036884550886835 10756210788055326826330253)
                ·
                  refine ⟨4033579045520747559873845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10756210788055326826330253 4033579045520747559873845)
                  ·
                    refine ⟨378148035517570083738173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4033579045520747559873845 378148035517570083738173)
                    ·
                      rfl

theorem cell23_2209322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2209322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209322 prefixEnd_2209322 := by exact prefixLift 2209322
  have htrace : WordTrace (prefixWord ++ tailWord_2209322) baseStart_2209322 baseEnd_2209322 := by
    simpa [prefixWord, tailWord_2209322, baseEnd_2209322] using wordTrace_append hprefix tailTrace_2209322
  have hstable : (prefixWord ++ tailWord_2209322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209322).length < 2 ^ (prefixWord ++ tailWord_2209322).sum := by decide
  have hdescent : baseEnd_2209322 < baseStart_2209322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209335 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 3, 6]
def baseStart_2209335 : Nat := 118140960795 + 2209335 * 2 ^ 59
def prefixEnd_2209335 : Nat := 4983230072969 + 3 ^ 40 * 2209335 * 2
def baseEnd_2209335 : Nat := 378150260600406233450653

theorem tailTrace_2209335 : CollatzResearch.WordTrace tailWord_2209335 prefixEnd_2209335 378150260600406233450653 := by
  unfold tailWord_2209335
  simp only [CollatzResearch.WordTrace]
  refine ⟨80581067450964094222781459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53720711633976062815187639 80581067450964094222781459)
  ·
    refine ⟨120871601176446141334172189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80581067450964094222781459 120871601176446141334172189)
    ·
      refine ⟨45326850441167303000314571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120871601176446141334172189 45326850441167303000314571)
      ·
        refine ⟨67990275661750954500471857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45326850441167303000314571 67990275661750954500471857)
        ·
          refine ⟨50992706746313215875353893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67990275661750954500471857 50992706746313215875353893)
          ·
            refine ⟨9561132514933727976628855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50992706746313215875353893 9561132514933727976628855)
            ·
              refine ⟨14341698772400591964943283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9561132514933727976628855 14341698772400591964943283)
              ·
                refine ⟨21512548158600887947414925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14341698772400591964943283 21512548158600887947414925)
                ·
                  refine ⟨8067205559475332980280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21512548158600887947414925 8067205559475332980280597)
                  ·
                    refine ⟨378150260600406233450653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8067205559475332980280597 378150260600406233450653)
                    ·
                      rfl

theorem cell23_2209335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_2209335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209335 prefixEnd_2209335 := by exact prefixLift 2209335
  have htrace : WordTrace (prefixWord ++ tailWord_2209335) baseStart_2209335 baseEnd_2209335 := by
    simpa [prefixWord, tailWord_2209335, baseEnd_2209335] using wordTrace_append hprefix tailTrace_2209335
  have hstable : (prefixWord ++ tailWord_2209335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209335).length < 2 ^ (prefixWord ++ tailWord_2209335).sum := by decide
  have hdescent : baseEnd_2209335 < baseStart_2209335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209355 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_2209355 : Nat := 118140960795 + 2209355 * 2 ^ 59
def prefixEnd_2209355 : Nat := 4983230072969 + 3 ^ 40 * 2209355 * 2
def baseEnd_2209355 : Nat := 1134461051414308622101867

theorem tailTrace_2209355 : CollatzResearch.WordTrace tailWord_2209355 prefixEnd_2209355 1134461051414308622101867 := by
  unfold tailWord_2209355
  simp only [CollatzResearch.WordTrace]
  refine ⟨80581796910891637638509519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53721197940594425092339679 80581796910891637638509519)
  ·
    refine ⟨120872695366337456457764279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80581796910891637638509519 120872695366337456457764279)
    ·
      refine ⟨181309043049506184686646419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120872695366337456457764279 181309043049506184686646419)
      ·
        refine ⟨271963564574259277029969629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181309043049506184686646419 271963564574259277029969629)
        ·
          refine ⟨101986336715347228886238611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271963564574259277029969629 101986336715347228886238611)
          ·
            refine ⟨152979505073020843329357917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101986336715347228886238611 152979505073020843329357917)
            ·
              refine ⟨57367314402382816248509219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152979505073020843329357917 57367314402382816248509219)
              ·
                refine ⟨86050971603574224372763829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57367314402382816248509219 86050971603574224372763829)
                ·
                  refine ⟨8067278587835083534946609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86050971603574224372763829 8067278587835083534946609)
                  ·
                    refine ⟨6050458940876312651209957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8067278587835083534946609 6050458940876312651209957)
                    ·
                      refine ⟨1134461051414308622101867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6050458940876312651209957 1134461051414308622101867)
                      ·
                        rfl

theorem cell23_2209355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_2209355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209355 prefixEnd_2209355 := by exact prefixLift 2209355
  have htrace : WordTrace (prefixWord ++ tailWord_2209355) baseStart_2209355 baseEnd_2209355 := by
    simpa [prefixWord, tailWord_2209355, baseEnd_2209355] using wordTrace_append hprefix tailTrace_2209355
  have hstable : (prefixWord ++ tailWord_2209355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209355).length < 2 ^ (prefixWord ++ tailWord_2209355).sum := by decide
  have hdescent : baseEnd_2209355 < baseStart_2209355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209359 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 3, 2, 2]
def baseStart_2209359 : Nat := 118140960795 + 2209359 * 2 ^ 59
def prefixEnd_2209359 : Nat := 4983230072969 + 3 ^ 40 * 2209359 * 2
def baseEnd_2209359 : Nat := 1134463105336926606451849

theorem tailTrace_2209359 : CollatzResearch.WordTrace tailWord_2209359 prefixEnd_2209359 1134463105336926606451849 := by
  unfold tailWord_2209359
  simp only [CollatzResearch.WordTrace]
  refine ⟨80581942802877146321655131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53721295201918097547770087 80581942802877146321655131)
  ·
    refine ⟨120872914204315719482482697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80581942802877146321655131 120872914204315719482482697)
    ·
      refine ⟨90654685653236789611862023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120872914204315719482482697 90654685653236789611862023)
      ·
        refine ⟨135982028479855184417793035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90654685653236789611862023 135982028479855184417793035)
        ·
          refine ⟨203973042719782776626689553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135982028479855184417793035 203973042719782776626689553)
          ·
            refine ⟨152979782039837082470017165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203973042719782776626689553 152979782039837082470017165)
            ·
              refine ⟨57367418264938905926256437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152979782039837082470017165 57367418264938905926256437)
              ·
                refine ⟨5378195462338022430586541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57367418264938905926256437 5378195462338022430586541)
                ·
                  refine ⟨2016823298376758411469953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5378195462338022430586541 2016823298376758411469953)
                  ·
                    refine ⟨1512617473782568808602465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016823298376758411469953 1512617473782568808602465)
                    ·
                      refine ⟨1134463105336926606451849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512617473782568808602465 1134463105336926606451849)
                      ·
                        rfl

theorem cell23_2209359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2, 2].length) (baseStart_2209359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209359 prefixEnd_2209359 := by exact prefixLift 2209359
  have htrace : WordTrace (prefixWord ++ tailWord_2209359) baseStart_2209359 baseEnd_2209359 := by
    simpa [prefixWord, tailWord_2209359, baseEnd_2209359] using wordTrace_append hprefix tailTrace_2209359
  have hstable : (prefixWord ++ tailWord_2209359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209359).length < 2 ^ (prefixWord ++ tailWord_2209359).sum := by decide
  have hdescent : baseEnd_2209359 < baseStart_2209359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209425 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_2209425 : Nat := 118140960795 + 2209425 * 2 ^ 59
def prefixEnd_2209425 : Nat := 4983230072969 + 3 ^ 40 * 2209425 * 2
def baseEnd_2209425 : Nat := 378165665020041116075515

theorem tailTrace_2209425 : CollatzResearch.WordTrace tailWord_2209425 prefixEnd_2209425 378165665020041116075515 := by
  unfold tailWord_2209425
  simp only [CollatzResearch.WordTrace]
  refine ⟨80584350020638039593557729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53722900013758693062371819 80584350020638039593557729)
  ·
    refine ⟨60438262515478529695168297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80584350020638039593557729 60438262515478529695168297)
    ·
      refine ⟨45328696886608897271376223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60438262515478529695168297 45328696886608897271376223)
      ·
        refine ⟨67993045329913345907064335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45328696886608897271376223 67993045329913345907064335)
        ·
          refine ⟨101989567994870018860596503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67993045329913345907064335 101989567994870018860596503)
          ·
            refine ⟨152984351992305028290894755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101989567994870018860596503 152984351992305028290894755)
            ·
              refine ⟨229476527988457542436342133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152984351992305028290894755 229476527988457542436342133)
              ·
                refine ⟨21513424498917894603407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229476527988457542436342133 21513424498917894603407075)
                ·
                  refine ⟨32270136748376841905110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21513424498917894603407075 32270136748376841905110613)
                  ·
                    refine ⟨378165665020041116075515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32270136748376841905110613 378165665020041116075515)
                    ·
                      rfl

theorem cell23_2209425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_2209425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209425 prefixEnd_2209425 := by exact prefixLift 2209425
  have htrace : WordTrace (prefixWord ++ tailWord_2209425) baseStart_2209425 baseEnd_2209425 := by
    simpa [prefixWord, tailWord_2209425, baseEnd_2209425] using wordTrace_append hprefix tailTrace_2209425
  have hstable : (prefixWord ++ tailWord_2209425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209425).length < 2 ^ (prefixWord ++ tailWord_2209425).sum := by decide
  have hdescent : baseEnd_2209425 < baseStart_2209425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209466 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_2209466 : Nat := 118140960795 + 2209466 * 2 ^ 59
def prefixEnd_2209466 : Nat := 4983230072969 + 3 ^ 40 * 2209466 * 2
def baseEnd_2209466 : Nat := 1134518047766957687813857

theorem tailTrace_2209466 : CollatzResearch.WordTrace tailWord_2209466 prefixEnd_2209466 1134518047766957687813857 := by
  unfold tailWord_2209466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20146461353372375898950063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53723896942326335730533501 20146461353372375898950063)
  ·
    refine ⟨30219692030058563848425095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20146461353372375898950063 30219692030058563848425095)
    ·
      refine ⟨45329538045087845772637643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30219692030058563848425095 45329538045087845772637643)
      ·
        refine ⟨67994307067631768658956465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45329538045087845772637643 67994307067631768658956465)
        ·
          refine ⟨50995730300723826494217349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67994307067631768658956465 50995730300723826494217349)
          ·
            refine ⟨9561699431385717467665753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50995730300723826494217349 9561699431385717467665753)
            ·
              refine ⟨7171274573539288100749315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9561699431385717467665753 7171274573539288100749315)
              ·
                refine ⟨10756911860308932151123973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171274573539288100749315 10756911860308932151123973)
                ·
                  refine ⟨2016920973807924778335745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10756911860308932151123973 2016920973807924778335745)
                  ·
                    refine ⟨1512690730355943583751809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016920973807924778335745 1512690730355943583751809)
                    ·
                      refine ⟨1134518047766957687813857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512690730355943583751809 1134518047766957687813857)
                      ·
                        rfl

theorem cell23_2209466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_2209466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209466 prefixEnd_2209466 := by exact prefixLift 2209466
  have htrace : WordTrace (prefixWord ++ tailWord_2209466) baseStart_2209466 baseEnd_2209466 := by
    simpa [prefixWord, tailWord_2209466, baseEnd_2209466] using wordTrace_append hprefix tailTrace_2209466
  have hstable : (prefixWord ++ tailWord_2209466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209466).length < 2 ^ (prefixWord ++ tailWord_2209466).sum := by decide
  have hdescent : baseEnd_2209466 < baseStart_2209466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209526 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2209526 : Nat := 118140960795 + 2209526 * 2 ^ 59
def prefixEnd_2209526 : Nat := 4983230072969 + 3 ^ 40 * 2209526 * 2
def baseEnd_2209526 : Nat := 1134548856606227453063581

theorem tailTrace_2209526 : CollatzResearch.WordTrace tailWord_2209526 prefixEnd_2209526 1134548856606227453063581 := by
  unfold tailWord_2209526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036752112079508365186527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53725355862181422561989621 5036752112079508365186527)
  ·
    refine ⟨7555128168119262547779791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036752112079508365186527 7555128168119262547779791)
    ·
      refine ⟨11332692252178893821669687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7555128168119262547779791 11332692252178893821669687)
      ·
        refine ⟨16999038378268340732504531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11332692252178893821669687 16999038378268340732504531)
        ·
          refine ⟨25498557567402511098756797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16999038378268340732504531 25498557567402511098756797)
          ·
            refine ⟨9561959087775941662033799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25498557567402511098756797 9561959087775941662033799)
            ·
              refine ⟨14342938631663912493050699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9561959087775941662033799 14342938631663912493050699)
              ·
                refine ⟨21514407947495868739576049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14342938631663912493050699 21514407947495868739576049)
                ·
                  refine ⟨16135805960621901554682037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21514407947495868739576049 16135805960621901554682037)
                  ·
                    refine ⟨1512731808808303270751441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16135805960621901554682037 1512731808808303270751441)
                    ·
                      refine ⟨1134548856606227453063581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512731808808303270751441 1134548856606227453063581)
                      ·
                        rfl

theorem cell23_2209526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2209526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209526 prefixEnd_2209526 := by exact prefixLift 2209526
  have htrace : WordTrace (prefixWord ++ tailWord_2209526) baseStart_2209526 baseEnd_2209526 := by
    simpa [prefixWord, tailWord_2209526, baseEnd_2209526] using wordTrace_append hprefix tailTrace_2209526
  have hstable : (prefixWord ++ tailWord_2209526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209526).length < 2 ^ (prefixWord ++ tailWord_2209526).sum := by decide
  have hdescent : baseEnd_2209526 < baseStart_2209526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209539 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 6, 2]
def baseStart_2209539 : Nat := 118140960795 + 2209539 * 2 ^ 59
def prefixEnd_2209539 : Nat := 4983230072969 + 3 ^ 40 * 2209539 * 2
def baseEnd_2209539 : Nat := 1134555531854735902201021

theorem tailTrace_2209539 : CollatzResearch.WordTrace tailWord_2209539 prefixEnd_2209539 1134555531854735902201021 := by
  unfold tailWord_2209539
  simp only [CollatzResearch.WordTrace]
  refine ⟨80588507942225037063207671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53725671961483358042138447 80588507942225037063207671)
  ·
    refine ⟨120882761913337555594811507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80588507942225037063207671 120882761913337555594811507)
    ·
      refine ⟨181324142870006333392217261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120882761913337555594811507 181324142870006333392217261)
      ·
        refine ⟨67996553576252375022081473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181324142870006333392217261 67996553576252375022081473)
        ·
          refine ⟨50997415182189281266561105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67996553576252375022081473 50997415182189281266561105)
          ·
            refine ⟨38248061386641960949920829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50997415182189281266561105 38248061386641960949920829)
            ·
              refine ⟨14343023019990735356220311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38248061386641960949920829 14343023019990735356220311)
              ·
                refine ⟨21514534529986103034330467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14343023019990735356220311 21514534529986103034330467)
                ·
                  refine ⟨32271801794979154551495701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21514534529986103034330467 32271801794979154551495701)
                  ·
                    refine ⟨1512740709139647869601361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32271801794979154551495701 1512740709139647869601361)
                    ·
                      refine ⟨1134555531854735902201021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512740709139647869601361 1134555531854735902201021)
                      ·
                        rfl

theorem cell23_2209539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_2209539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209539 prefixEnd_2209539 := by exact prefixLift 2209539
  have htrace : WordTrace (prefixWord ++ tailWord_2209539) baseStart_2209539 baseEnd_2209539 := by
    simpa [prefixWord, tailWord_2209539, baseEnd_2209539] using wordTrace_append hprefix tailTrace_2209539
  have hstable : (prefixWord ++ tailWord_2209539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209539).length < 2 ^ (prefixWord ++ tailWord_2209539).sum := by decide
  have hdescent : baseEnd_2209539 < baseStart_2209539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209616 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2]
def baseStart_2209616 : Nat := 118140960795 + 2209616 * 2 ^ 59
def prefixEnd_2209616 : Nat := 4983230072969 + 3 ^ 40 * 2209616 * 2
def baseEnd_2209616 : Nat := 1134595069865132100938167

theorem tailTrace_2209616 : CollatzResearch.WordTrace tailWord_2209616 prefixEnd_2209616 1134595069865132100938167 := by
  unfold tailWord_2209616
  simp only [CollatzResearch.WordTrace]
  refine ⟨40295658181473039606880351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53727544241964052809173801 40295658181473039606880351)
  ·
    refine ⟨60443487272209559410320527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40295658181473039606880351 60443487272209559410320527)
    ·
      refine ⟨90665230908314339115480791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60443487272209559410320527 90665230908314339115480791)
      ·
        refine ⟨135997846362471508673221187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90665230908314339115480791 135997846362471508673221187)
        ·
          refine ⟨203996769543707263009831781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135997846362471508673221187 203996769543707263009831781)
          ·
            refine ⟨38249394289445111814343459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203996769543707263009831781 38249394289445111814343459)
            ·
              refine ⟨57374091434167667721515189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38249394289445111814343459 57374091434167667721515189)
              ·
                refine ⟨5378821071953218848892049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57374091434167667721515189 5378821071953218848892049)
                ·
                  refine ⟨4034115803964914136669037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5378821071953218848892049 4034115803964914136669037)
                  ·
                    refine ⟨1512793426486842801250889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4034115803964914136669037 1512793426486842801250889)
                    ·
                      refine ⟨1134595069865132100938167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512793426486842801250889 1134595069865132100938167)
                      ·
                        rfl

theorem cell23_2209616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2].length) (baseStart_2209616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209616 prefixEnd_2209616 := by exact prefixLift 2209616
  have htrace : WordTrace (prefixWord ++ tailWord_2209616) baseStart_2209616 baseEnd_2209616 := by
    simpa [prefixWord, tailWord_2209616, baseEnd_2209616] using wordTrace_append hprefix tailTrace_2209616
  have hstable : (prefixWord ++ tailWord_2209616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209616).length < 2 ^ (prefixWord ++ tailWord_2209616).sum := by decide
  have hdescent : baseEnd_2209616 < baseStart_2209616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209649 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_2209649 : Nat := 118140960795 + 2209649 * 2 ^ 59
def prefixEnd_2209649 : Nat := 4983230072969 + 3 ^ 40 * 2209649 * 2
def baseEnd_2209649 : Nat := 1134612014726730471825515

theorem tailTrace_2209649 : CollatzResearch.WordTrace tailWord_2209649 prefixEnd_2209649 1134612014726730471825515 := by
  unfold tailWord_2209649
  simp only [CollatzResearch.WordTrace]
  refine ⟨80592519971826525849712001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53728346647884350566474667 80592519971826525849712001)
  ·
    refine ⟨60444389978869894387284001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80592519971826525849712001 60444389978869894387284001)
    ·
      refine ⟨45333292484152420790463001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60444389978869894387284001 45333292484152420790463001)
      ·
        refine ⟨33999969363114315592847251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45333292484152420790463001 33999969363114315592847251)
        ·
          refine ⟨50999954044671473389270877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33999969363114315592847251 50999954044671473389270877)
          ·
            refine ⟨19124982766751802520976579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50999954044671473389270877 19124982766751802520976579)
            ·
              refine ⟨28687474150127703781464869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19124982766751802520976579 28687474150127703781464869)
              ·
                refine ⟨5378901403148944459024663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28687474150127703781464869 5378901403148944459024663)
                ·
                  refine ⟨8068352104723416688536995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378901403148944459024663 8068352104723416688536995)
                  ·
                    refine ⟨12102528157085125032805493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8068352104723416688536995 12102528157085125032805493)
                    ·
                      refine ⟨1134612014726730471825515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12102528157085125032805493 1134612014726730471825515)
                      ·
                        rfl

theorem cell23_2209649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_2209649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209649 prefixEnd_2209649 := by exact prefixLift 2209649
  have htrace : WordTrace (prefixWord ++ tailWord_2209649) baseStart_2209649 baseEnd_2209649 := by
    simpa [prefixWord, tailWord_2209649, baseEnd_2209649] using wordTrace_append hprefix tailTrace_2209649
  have hstable : (prefixWord ++ tailWord_2209649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209649).length < 2 ^ (prefixWord ++ tailWord_2209649).sum := by decide
  have hdescent : baseEnd_2209649 < baseStart_2209649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209659 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4]
def baseStart_2209659 : Nat := 118140960795 + 2209659 * 2 ^ 59
def prefixEnd_2209659 : Nat := 4983230072969 + 3 ^ 40 * 2209659 * 2
def baseEnd_2209659 : Nat := 1134617149533275432700469

theorem tailTrace_2209659 : CollatzResearch.WordTrace tailWord_2209659 prefixEnd_2209659 1134617149533275432700469 := by
  unfold tailWord_2209659
  simp only [CollatzResearch.WordTrace]
  refine ⟨80592884701790297557576031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53728589801193531705050687 80592884701790297557576031)
  ·
    refine ⟨120889327052685446336364047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80592884701790297557576031 120889327052685446336364047)
    ·
      refine ⟨181333990579028169504546071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120889327052685446336364047 181333990579028169504546071)
      ·
        refine ⟨272000985868542254256819107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181333990579028169504546071 272000985868542254256819107)
        ·
          refine ⟨408001478802813381385228661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272000985868542254256819107 408001478802813381385228661)
          ·
            refine ⟨38250138637763754504865187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 408001478802813381385228661 38250138637763754504865187)
            ·
              refine ⟨57375207956645631757297781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38250138637763754504865187 57375207956645631757297781)
              ·
                refine ⟨5378925745935527977246667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57375207956645631757297781 5378925745935527977246667)
                ·
                  refine ⟨8068388618903291965870001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378925745935527977246667 8068388618903291965870001)
                  ·
                    refine ⟨6051291464177468974402501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8068388618903291965870001 6051291464177468974402501)
                    ·
                      refine ⟨1134617149533275432700469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6051291464177468974402501 1134617149533275432700469)
                      ·
                        rfl

theorem cell23_2209659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_2209659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209659 prefixEnd_2209659 := by exact prefixLift 2209659
  have htrace : WordTrace (prefixWord ++ tailWord_2209659) baseStart_2209659 baseEnd_2209659 := by
    simpa [prefixWord, tailWord_2209659, baseEnd_2209659] using wordTrace_append hprefix tailTrace_2209659
  have hstable : (prefixWord ++ tailWord_2209659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209659).length < 2 ^ (prefixWord ++ tailWord_2209659).sum := by decide
  have hdescent : baseEnd_2209659 < baseStart_2209659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209713 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2209713 : Nat := 118140960795 + 2209713 * 2 ^ 59
def prefixEnd_2209713 : Nat := 4983230072969 + 3 ^ 40 * 2209713 * 2
def baseEnd_2209713 : Nat := 1134644877488618221425221

theorem tailTrace_2209713 : CollatzResearch.WordTrace tailWord_2209713 prefixEnd_2209713 1134644877488618221425221 := by
  unfold tailWord_2209713
  simp only [CollatzResearch.WordTrace]
  refine ⟨80594854243594664780041793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53729902829063109853361195 80594854243594664780041793)
  ·
    refine ⟨60446140682695998585031345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80594854243594664780041793 60446140682695998585031345)
    ·
      refine ⟨45334605512021998938773509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60446140682695998585031345 45334605512021998938773509)
      ·
        refine ⟨8500238533504124801020033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45334605512021998938773509 8500238533504124801020033)
        ·
          refine ⟨6375178900128093600765025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8500238533504124801020033 6375178900128093600765025)
          ·
            refine ⟨4781384175096070200573769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6375178900128093600765025 4781384175096070200573769)
            ·
              refine ⟨3586038131322052650430327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4781384175096070200573769 3586038131322052650430327)
              ·
                refine ⟨5379057196983078975645491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586038131322052650430327 5379057196983078975645491)
                ·
                  refine ⟨8068585795474618463468237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379057196983078975645491 8068585795474618463468237)
                  ·
                    refine ⟨3025719673302981923800589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8068585795474618463468237 3025719673302981923800589)
                    ·
                      refine ⟨1134644877488618221425221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3025719673302981923800589 1134644877488618221425221)
                      ·
                        rfl

theorem cell23_2209713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2209713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209713 prefixEnd_2209713 := by exact prefixLift 2209713
  have htrace : WordTrace (prefixWord ++ tailWord_2209713) baseStart_2209713 baseEnd_2209713 := by
    simpa [prefixWord, tailWord_2209713, baseEnd_2209713] using wordTrace_append hprefix tailTrace_2209713
  have hstable : (prefixWord ++ tailWord_2209713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209713).length < 2 ^ (prefixWord ++ tailWord_2209713).sum := by decide
  have hdescent : baseEnd_2209713 < baseStart_2209713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209719 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_2209719 : Nat := 118140960795 + 2209719 * 2 ^ 59
def prefixEnd_2209719 : Nat := 4983230072969 + 3 ^ 40 * 2209719 * 2
def baseEnd_2209719 : Nat := 1134647958372545197950193

theorem tailTrace_2209719 : CollatzResearch.WordTrace tailWord_2209719 prefixEnd_2209719 1134647958372545197950193 := by
  unfold tailWord_2209719
  simp only [CollatzResearch.WordTrace]
  refine ⟨80595073081572927804760211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53730048721048618536506807 80595073081572927804760211)
  ·
    refine ⟨120892609622359391707140317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80595073081572927804760211 120892609622359391707140317)
    ·
      refine ⟨45334728608384771890177619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120892609622359391707140317 45334728608384771890177619)
      ·
        refine ⟨68002092912577157835266429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45334728608384771890177619 68002092912577157835266429)
        ·
          refine ⟨25500784842216434188224911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68002092912577157835266429 25500784842216434188224911)
          ·
            refine ⟨38251177263324651282337367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25500784842216434188224911 38251177263324651282337367)
            ·
              refine ⟨57376765894986976923506051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38251177263324651282337367 57376765894986976923506051)
              ·
                refine ⟨86065148842480465385259077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57376765894986976923506051 86065148842480465385259077)
                ·
                  refine ⟨16137215407965087259736077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86065148842480465385259077 16137215407965087259736077)
                  ·
                    refine ⟨6051455777986907722401029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16137215407965087259736077 6051455777986907722401029)
                    ·
                      refine ⟨1134647958372545197950193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6051455777986907722401029 1134647958372545197950193)
                      ·
                        rfl

theorem cell23_2209719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_2209719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209719 prefixEnd_2209719 := by exact prefixLift 2209719
  have htrace : WordTrace (prefixWord ++ tailWord_2209719) baseStart_2209719 baseEnd_2209719 := by
    simpa [prefixWord, tailWord_2209719, baseEnd_2209719] using wordTrace_append hprefix tailTrace_2209719
  have hstable : (prefixWord ++ tailWord_2209719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209719).length < 2 ^ (prefixWord ++ tailWord_2209719).sum := by decide
  have hdescent : baseEnd_2209719 < baseStart_2209719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209739 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_2209739 : Nat := 118140960795 + 2209739 * 2 ^ 59
def prefixEnd_2209739 : Nat := 4983230072969 + 3 ^ 40 * 2209739 * 2
def baseEnd_2209739 : Nat := 1134658227985635119700101

theorem tailTrace_2209739 : CollatzResearch.WordTrace tailWord_2209739 prefixEnd_2209739 1134658227985635119700101 := by
  unfold tailWord_2209739
  simp only [CollatzResearch.WordTrace]
  refine ⟨80595802541500471220488271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53730535027666980813658847 80595802541500471220488271)
  ·
    refine ⟨120893703812250706830732407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80595802541500471220488271 120893703812250706830732407)
    ·
      refine ⟨181340555718376060246098611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120893703812250706830732407 181340555718376060246098611)
      ·
        refine ⟨272010833577564090369147917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181340555718376060246098611 272010833577564090369147917)
        ·
          refine ⟨102004062591586533888430469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272010833577564090369147917 102004062591586533888430469)
          ·
            refine ⟨19125761735922475104080713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102004062591586533888430469 19125761735922475104080713)
            ·
              refine ⟨14344321301941856328060535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19125761735922475104080713 14344321301941856328060535)
              ·
                refine ⟨21516481952912784492090803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14344321301941856328060535 21516481952912784492090803)
                ·
                  refine ⟨32274722929369176738136205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21516481952912784492090803 32274722929369176738136205)
                  ·
                    refine ⟨12103021098513441276801077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32274722929369176738136205 12103021098513441276801077)
                    ·
                      refine ⟨1134658227985635119700101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12103021098513441276801077 1134658227985635119700101)
                      ·
                        rfl

theorem cell23_2209739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_2209739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209739 prefixEnd_2209739 := by exact prefixLift 2209739
  have htrace : WordTrace (prefixWord ++ tailWord_2209739) baseStart_2209739 baseEnd_2209739 := by
    simpa [prefixWord, tailWord_2209739, baseEnd_2209739] using wordTrace_append hprefix tailTrace_2209739
  have hstable : (prefixWord ++ tailWord_2209739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209739).length < 2 ^ (prefixWord ++ tailWord_2209739).sum := by decide
  have hdescent : baseEnd_2209739 < baseStart_2209739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209740 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2209740 : Nat := 118140960795 + 2209740 * 2 ^ 59
def prefixEnd_2209740 : Nat := 4983230072969 + 3 ^ 40 * 2209740 * 2
def baseEnd_2209740 : Nat := 1134658741466289615787597

theorem tailTrace_2209740 : CollatzResearch.WordTrace tailWord_2209740 prefixEnd_2209740 1134658741466289615787597 := by
  unfold tailWord_2209740
  simp only [CollatzResearch.WordTrace]
  refine ⟨40297919507248424195637337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53730559342997898927516449 40297919507248424195637337)
  ·
    refine ⟨30223439630436318146728003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40297919507248424195637337 30223439630436318146728003)
    ·
      refine ⟨45335159445654477220092005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30223439630436318146728003 45335159445654477220092005)
      ·
        refine ⟨8500342396060214478767251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45335159445654477220092005 8500342396060214478767251)
        ·
          refine ⟨12750513594090321718150877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8500342396060214478767251 12750513594090321718150877)
          ·
            refine ⟨4781442597783870644306579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12750513594090321718150877 4781442597783870644306579)
            ·
              refine ⟨7172163896675805966459869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781442597783870644306579 7172163896675805966459869)
              ·
                refine ⟨2689561461253427237422451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7172163896675805966459869 2689561461253427237422451)
                ·
                  refine ⟨4034342191880140856133677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689561461253427237422451 4034342191880140856133677)
                  ·
                    refine ⟨1512878321955052821050129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4034342191880140856133677 1512878321955052821050129)
                    ·
                      refine ⟨1134658741466289615787597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1512878321955052821050129 1134658741466289615787597)
                      ·
                        rfl

theorem cell23_2209740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2209740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209740 prefixEnd_2209740 := by exact prefixLift 2209740
  have htrace : WordTrace (prefixWord ++ tailWord_2209740) baseStart_2209740 baseEnd_2209740 := by
    simpa [prefixWord, tailWord_2209740, baseEnd_2209740] using wordTrace_append hprefix tailTrace_2209740
  have hstable : (prefixWord ++ tailWord_2209740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209740).length < 2 ^ (prefixWord ++ tailWord_2209740).sum := by decide
  have hdescent : baseEnd_2209740 < baseStart_2209740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2209809 : Nat := 118140960795 + 2209809 * 2 ^ 59
def prefixEnd_2209809 : Nat := 4983230072969 + 3 ^ 40 * 2209809 * 2
def baseEnd_2209809 : Nat := 1134694171631449845824779

theorem tailTrace_2209809 : CollatzResearch.WordTrace tailWord_2209809 prefixEnd_2209809 1134694171631449845824779 := by
  unfold tailWord_2209809
  simp only [CollatzResearch.WordTrace]
  refine ⟨80598355651246873175536481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53732237100831248783690987 80598355651246873175536481)
  ·
    refine ⟨60448766738435154881652361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80598355651246873175536481 60448766738435154881652361)
    ·
      refine ⟨45336575053826366161239271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60448766738435154881652361 45336575053826366161239271)
      ·
        refine ⟨68004862580739549241858907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45336575053826366161239271 68004862580739549241858907)
        ·
          refine ⟨102007293871109323862788361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68004862580739549241858907 102007293871109323862788361)
          ·
            refine ⟨76505470403331992897091271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102007293871109323862788361 76505470403331992897091271)
            ·
              refine ⟨114758205604997989345636907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76505470403331992897091271 114758205604997989345636907)
              ·
                refine ⟨172137308407496984018455361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114758205604997989345636907 172137308407496984018455361)
                ·
                  refine ⟨129102981305622738013841521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172137308407496984018455361 129102981305622738013841521)
                  ·
                    refine ⟨96827235979217053510381141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129102981305622738013841521 96827235979217053510381141)
                    ·
                      refine ⟨1134694171631449845824779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 96827235979217053510381141 1134694171631449845824779)
                      ·
                        rfl

theorem cell23_2209809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2209809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209809 prefixEnd_2209809 := by exact prefixLift 2209809
  have htrace : WordTrace (prefixWord ++ tailWord_2209809) baseStart_2209809 baseEnd_2209809 := by
    simpa [prefixWord, tailWord_2209809, baseEnd_2209809] using wordTrace_append hprefix tailTrace_2209809
  have hstable : (prefixWord ++ tailWord_2209809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209809).length < 2 ^ (prefixWord ++ tailWord_2209809).sum := by decide
  have hdescent : baseEnd_2209809 < baseStart_2209809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209816 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2209816 : Nat := 118140960795 + 2209816 * 2 ^ 59
def prefixEnd_2209816 : Nat := 4983230072969 + 3 ^ 40 * 2209816 * 2
def baseEnd_2209816 : Nat := 1134697765996031318437247

theorem tailTrace_2209816 : CollatzResearch.WordTrace tailWord_2209816 prefixEnd_2209816 1134697765996031318437247 := by
  unfold tailWord_2209816
  simp only [CollatzResearch.WordTrace]
  refine ⟨40299305481110756685520651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53732407308147675580694201 40299305481110756685520651)
  ·
    refine ⟨60448958221666135028280977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40299305481110756685520651 60448958221666135028280977)
    ·
      refine ⟨45336718666249601271210733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60448958221666135028280977 45336718666249601271210733)
      ·
        refine ⟨17001269499843600476704025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45336718666249601271210733 17001269499843600476704025)
        ·
          refine ⟨12750952124882700357528019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17001269499843600476704025 12750952124882700357528019)
          ·
            refine ⟨19126428187324050536292029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12750952124882700357528019 19126428187324050536292029)
            ·
              refine ⟨7172410570246518951109511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19126428187324050536292029 7172410570246518951109511)
              ·
                refine ⟨10758615855369778426664267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7172410570246518951109511 10758615855369778426664267)
                ·
                  refine ⟨16137923783054667639996401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10758615855369778426664267 16137923783054667639996401)
                  ·
                    refine ⟨12103442837291000729997301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16137923783054667639996401 12103442837291000729997301)
                    ·
                      refine ⟨1134697765996031318437247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12103442837291000729997301 1134697765996031318437247)
                      ·
                        rfl

theorem cell23_2209816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2209816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209816 prefixEnd_2209816 := by exact prefixLift 2209816
  have htrace : WordTrace (prefixWord ++ tailWord_2209816) baseStart_2209816 baseEnd_2209816 := by
    simpa [prefixWord, tailWord_2209816, baseEnd_2209816] using wordTrace_append hprefix tailTrace_2209816
  have hstable : (prefixWord ++ tailWord_2209816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209816).length < 2 ^ (prefixWord ++ tailWord_2209816).sum := by decide
  have hdescent : baseEnd_2209816 < baseStart_2209816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209819 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 8]
def baseStart_2209819 : Nat := 118140960795 + 2209819 * 2 ^ 59
def prefixEnd_2209819 : Nat := 4983230072969 + 3 ^ 40 * 2209819 * 2
def baseEnd_2209819 : Nat := 378233102145998268899911

theorem tailTrace_2209819 : CollatzResearch.WordTrace tailWord_2209819 prefixEnd_2209819 378233102145998268899911 := by
  unfold tailWord_2209819
  simp only [CollatzResearch.WordTrace]
  refine ⟨80598720381210644883400511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53732480254140429922267007 80598720381210644883400511)
  ·
    refine ⟨120898080571815967325100767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80598720381210644883400511 120898080571815967325100767)
    ·
      refine ⟨181347120857723950987651151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120898080571815967325100767 181347120857723950987651151)
      ·
        refine ⟨272020681286585926481476727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181347120857723950987651151 272020681286585926481476727)
        ·
          refine ⟨408031021929878889722215091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272020681286585926481476727 408031021929878889722215091)
          ·
            refine ⟨612046532894818334583322637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408031021929878889722215091 612046532894818334583322637)
            ·
              refine ⟨229517449835556875468745989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612046532894818334583322637 229517449835556875468745989)
              ·
                refine ⟨43034521844166914150389873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229517449835556875468745989 43034521844166914150389873)
                ·
                  refine ⟨32275891383125185612792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43034521844166914150389873 32275891383125185612792405)
                  ·
                    refine ⟨378233102145998268899911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32275891383125185612792405 378233102145998268899911)
                    ·
                      rfl

theorem cell23_2209819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_2209819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209819 prefixEnd_2209819 := by exact prefixLift 2209819
  have htrace : WordTrace (prefixWord ++ tailWord_2209819) baseStart_2209819 baseEnd_2209819 := by
    simpa [prefixWord, tailWord_2209819, baseEnd_2209819] using wordTrace_append hprefix tailTrace_2209819
  have hstable : (prefixWord ++ tailWord_2209819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209819).length < 2 ^ (prefixWord ++ tailWord_2209819).sum := by decide
  have hdescent : baseEnd_2209819 < baseStart_2209819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209863 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_2209863 : Nat := 118140960795 + 2209863 * 2 ^ 59
def prefixEnd_2209863 : Nat := 4983230072969 + 3 ^ 40 * 2209863 * 2
def baseEnd_2209863 : Nat := 1134721899586792634549531

theorem tailTrace_2209863 : CollatzResearch.WordTrace tailWord_2209863 prefixEnd_2209863 1134721899586792634549531 := by
  unfold tailWord_2209863
  simp only [CollatzResearch.WordTrace]
  refine ⟨80600325193051240398002243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53733550128700826932001495 80600325193051240398002243)
  ·
    refine ⟨120900487789576860597003365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80600325193051240398002243 120900487789576860597003365)
    ·
      refine ⟨22668841460545661361938131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120900487789576860597003365 22668841460545661361938131)
      ·
        refine ⟨34003262190818492042907197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22668841460545661361938131 34003262190818492042907197)
        ·
          refine ⟨12751223321556934516090199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34003262190818492042907197 12751223321556934516090199)
          ·
            refine ⟨19126834982335401774135299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12751223321556934516090199 19126834982335401774135299)
            ·
              refine ⟨28690252473503102661202949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19126834982335401774135299 28690252473503102661202949)
              ·
                refine ⟨5379422338781831748975553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28690252473503102661202949 5379422338781831748975553)
                ·
                  refine ⟨4034566754086373811731665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5379422338781831748975553 4034566754086373811731665)
                  ·
                    refine ⟨3025925065564780358798749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4034566754086373811731665 3025925065564780358798749)
                    ·
                      refine ⟨1134721899586792634549531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3025925065564780358798749 1134721899586792634549531)
                      ·
                        rfl

theorem cell23_2209863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_2209863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209863 prefixEnd_2209863 := by exact prefixLift 2209863
  have htrace : WordTrace (prefixWord ++ tailWord_2209863) baseStart_2209863 baseEnd_2209863 := by
    simpa [prefixWord, tailWord_2209863, baseEnd_2209863] using wordTrace_append hprefix tailTrace_2209863
  have hstable : (prefixWord ++ tailWord_2209863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209863).length < 2 ^ (prefixWord ++ tailWord_2209863).sum := by decide
  have hdescent : baseEnd_2209863 < baseStart_2209863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209927 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_2209927 : Nat := 118140960795 + 2209927 * 2 ^ 59
def prefixEnd_2209927 : Nat := 4983230072969 + 3 ^ 40 * 2209927 * 2
def baseEnd_2209927 : Nat := 1134754762348680384149237

theorem tailTrace_2209927 : CollatzResearch.WordTrace tailWord_2209927 prefixEnd_2209927 1134754762348680384149237 := by
  unfold tailWord_2209927
  simp only [CollatzResearch.WordTrace]
  refine ⟨80602659464819379328332035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53735106309879586218888023 80602659464819379328332035)
  ·
    refine ⟨120903989197229068992498053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80602659464819379328332035 120903989197229068992498053)
    ·
      refine ⟨22669497974480450436093385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120903989197229068992498053 22669497974480450436093385)
      ·
        refine ⟨17002123480860337827070039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22669497974480450436093385 17002123480860337827070039)
        ·
          refine ⟨25503185221290506740605059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17002123480860337827070039 25503185221290506740605059)
          ·
            refine ⟨38254777831935760110907589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25503185221290506740605059 38254777831935760110907589)
            ·
              refine ⟨7172770843487955020795173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38254777831935760110907589 7172770843487955020795173)
              ·
                refine ⟨1344894533153991566399095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7172770843487955020795173 1344894533153991566399095)
                ·
                  refine ⟨2017341799730987349598643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344894533153991566399095 2017341799730987349598643)
                  ·
                    refine ⟨3026012699596481024397965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2017341799730987349598643 3026012699596481024397965)
                    ·
                      refine ⟨1134754762348680384149237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3026012699596481024397965 1134754762348680384149237)
                      ·
                        rfl

theorem cell23_2209927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_2209927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209927 prefixEnd_2209927 := by exact prefixLift 2209927
  have htrace : WordTrace (prefixWord ++ tailWord_2209927) baseStart_2209927 baseEnd_2209927 := by
    simpa [prefixWord, tailWord_2209927, baseEnd_2209927] using wordTrace_append hprefix tailTrace_2209927
  have hstable : (prefixWord ++ tailWord_2209927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209927).length < 2 ^ (prefixWord ++ tailWord_2209927).sum := by decide
  have hdescent : baseEnd_2209927 < baseStart_2209927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209970 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2209970 : Nat := 118140960795 + 2209970 * 2 ^ 59
def prefixEnd_2209970 : Nat := 4983230072969 + 3 ^ 40 * 2209970 * 2
def baseEnd_2209970 : Nat := 1134776842016823715911539

theorem tailTrace_2209970 : CollatzResearch.WordTrace tailWord_2209970 prefixEnd_2209970 1134776842016823715911539 := by
  unfold tailWord_2209970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151056950915899418036841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53736151869109065114764909 20151056950915899418036841)
  ·
    refine ⟨15113292713186924563527631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20151056950915899418036841 15113292713186924563527631)
    ·
      refine ⟨22669939069780386845291447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15113292713186924563527631 22669939069780386845291447)
      ·
        refine ⟨34004908604670580267937171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22669939069780386845291447 34004908604670580267937171)
        ·
          refine ⟨51007362907005870401905757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34004908604670580267937171 51007362907005870401905757)
          ·
            refine ⟨19127761090127201400714659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51007362907005870401905757 19127761090127201400714659)
            ·
              refine ⟨28691641635190802101071989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19127761090127201400714659 28691641635190802101071989)
              ·
                refine ⟨2689841403299137696975499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28691641635190802101071989 2689841403299137696975499)
                ·
                  refine ⟨4034762104948706545463249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689841403299137696975499 4034762104948706545463249)
                  ·
                    refine ⟨3026071578711529909097437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4034762104948706545463249 3026071578711529909097437)
                    ·
                      refine ⟨1134776842016823715911539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3026071578711529909097437 1134776842016823715911539)
                      ·
                        rfl

theorem cell23_2209970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2209970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209970 prefixEnd_2209970 := by exact prefixLift 2209970
  have htrace : WordTrace (prefixWord ++ tailWord_2209970) baseStart_2209970 baseEnd_2209970 := by
    simpa [prefixWord, tailWord_2209970, baseEnd_2209970] using wordTrace_append hprefix tailTrace_2209970
  have hstable : (prefixWord ++ tailWord_2209970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209970).length < 2 ^ (prefixWord ++ tailWord_2209970).sum := by decide
  have hdescent : baseEnd_2209970 < baseStart_2209970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209984 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2]
def baseStart_2209984 : Nat := 118140960795 + 2209984 * 2 ^ 59
def prefixEnd_2209984 : Nat := 4983230072969 + 3 ^ 40 * 2209984 * 2
def baseEnd_2209984 : Nat := 1134784030745986661136475

theorem tailTrace_2209984 : CollatzResearch.WordTrace tailWord_2209984 prefixEnd_2209984 1134784030745986661136475 := by
  unfold tailWord_2209984
  simp only [CollatzResearch.WordTrace]
  refine ⟨40302369212806439031578503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53736492283741918708771337 40302369212806439031578503)
  ·
    refine ⟨60453553819209658547367755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40302369212806439031578503 60453553819209658547367755)
    ·
      refine ⟨90680330728814487821051633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60453553819209658547367755 90680330728814487821051633)
      ·
        refine ⟨68010248046610865865788725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90680330728814487821051633 68010248046610865865788725)
        ·
          refine ⟨6375960754369768674917693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68010248046610865865788725 6375960754369768674917693)
          ·
            refine ⟨2390985282888663253094135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6375960754369768674917693 2390985282888663253094135)
            ·
              refine ⟨3586477924332994879641203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2390985282888663253094135 3586477924332994879641203)
              ·
                refine ⟨5379716886499492319461805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586477924332994879641203 5379716886499492319461805)
                ·
                  refine ⟨2017393832437309619798177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5379716886499492319461805 2017393832437309619798177)
                  ·
                    refine ⟨1513045374327982214848633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017393832437309619798177 1513045374327982214848633)
                    ·
                      refine ⟨1134784030745986661136475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513045374327982214848633 1134784030745986661136475)
                      ·
                        rfl

theorem cell23_2209984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_2209984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2209984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2209984 prefixEnd_2209984 := by exact prefixLift 2209984
  have htrace : WordTrace (prefixWord ++ tailWord_2209984) baseStart_2209984 baseEnd_2209984 := by
    simpa [prefixWord, tailWord_2209984, baseEnd_2209984] using wordTrace_append hprefix tailTrace_2209984
  have hstable : (prefixWord ++ tailWord_2209984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209984).length < 2 ^ (prefixWord ++ tailWord_2209984).sum := by decide
  have hdescent : baseEnd_2209984 < baseStart_2209984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210018 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2210018 : Nat := 118140960795 + 2210018 * 2 ^ 59
def prefixEnd_2210018 : Nat := 4983230072969 + 3 ^ 40 * 2210018 * 2
def baseEnd_2210018 : Nat := 1134801489088239528111319

theorem tailTrace_2210018 : CollatzResearch.WordTrace tailWord_2210018 prefixEnd_2210018 1134801489088239528111319 := by
  unfold tailWord_2210018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151494626872425467473677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53737319004993134579929805 20151494626872425467473677)
  ·
    refine ⟨7556810485077159550302629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20151494626872425467473677 7556810485077159550302629)
    ·
      refine ⟨1416901965951967415681743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7556810485077159550302629 1416901965951967415681743)
      ·
        refine ⟨2125352948927951123522615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416901965951967415681743 2125352948927951123522615)
        ·
          refine ⟨3188029423391926685283923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125352948927951123522615 3188029423391926685283923)
          ·
            refine ⟨4782044135087890027925885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188029423391926685283923 4782044135087890027925885)
            ·
              refine ⟨1793266550657958760472207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4782044135087890027925885 1793266550657958760472207)
              ·
                refine ⟨2689899825986938140708311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793266550657958760472207 2689899825986938140708311)
                ·
                  refine ⟨4034849738980407211062467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689899825986938140708311 4034849738980407211062467)
                  ·
                    refine ⟨6052274608470610816593701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4034849738980407211062467 6052274608470610816593701)
                    ·
                      refine ⟨1134801489088239528111319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6052274608470610816593701 1134801489088239528111319)
                      ·
                        rfl

theorem cell23_2210018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2210018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210018 prefixEnd_2210018 := by exact prefixLift 2210018
  have htrace : WordTrace (prefixWord ++ tailWord_2210018) baseStart_2210018 baseEnd_2210018 := by
    simpa [prefixWord, tailWord_2210018, baseEnd_2210018] using wordTrace_append hprefix tailTrace_2210018
  have hstable : (prefixWord ++ tailWord_2210018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210018).length < 2 ^ (prefixWord ++ tailWord_2210018).sum := by decide
  have hdescent : baseEnd_2210018 < baseStart_2210018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210034 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2210034 : Nat := 118140960795 + 2210034 * 2 ^ 59
def prefixEnd_2210034 : Nat := 4983230072969 + 3 ^ 40 * 2210034 * 2
def baseEnd_2210034 : Nat := 1134809704778711465511245

theorem tailTrace_2210034 : CollatzResearch.WordTrace tailWord_2210034 prefixEnd_2210034 1134809704778711465511245 := by
  unfold tailWord_2210034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151640518857934150619289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53737708050287824401651437 20151640518857934150619289)
  ·
    refine ⟨15113730389143450612964467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20151640518857934150619289 15113730389143450612964467)
    ·
      refine ⟨22670595583715175919446701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15113730389143450612964467 22670595583715175919446701)
      ·
        refine ⟨8501473343893190969792513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22670595583715175919446701 8501473343893190969792513)
        ·
          refine ⟨6376105007919893227344385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8501473343893190969792513 6376105007919893227344385)
          ·
            refine ⟨4782078755939919920508289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6376105007919893227344385 4782078755939919920508289)
            ·
              refine ⟨3586559066954939940381217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782078755939919920508289 3586559066954939940381217)
              ·
                refine ⟨2689919300216204955285913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3586559066954939940381217 2689919300216204955285913)
                ·
                  refine ⟨2017439475162153716464435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2689919300216204955285913 2017439475162153716464435)
                  ·
                    refine ⟨3026159212743230574696653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2017439475162153716464435 3026159212743230574696653)
                    ·
                      refine ⟨1134809704778711465511245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3026159212743230574696653 1134809704778711465511245)
                      ·
                        rfl

theorem cell23_2210034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2210034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210034 prefixEnd_2210034 := by exact prefixLift 2210034
  have htrace : WordTrace (prefixWord ++ tailWord_2210034) baseStart_2210034 baseEnd_2210034 := by
    simpa [prefixWord, tailWord_2210034, baseEnd_2210034] using wordTrace_append hprefix tailTrace_2210034
  have hstable : (prefixWord ++ tailWord_2210034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210034).length < 2 ^ (prefixWord ++ tailWord_2210034).sum := by decide
  have hdescent : baseEnd_2210034 < baseStart_2210034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210050 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2210050 : Nat := 118140960795 + 2210050 * 2 ^ 59
def prefixEnd_2210050 : Nat := 4983230072969 + 3 ^ 40 * 2210050 * 2
def baseEnd_2210050 : Nat := 378272640156394467637057

theorem tailTrace_2210050 : CollatzResearch.WordTrace tailWord_2210050 prefixEnd_2210050 378272640156394467637057 := by
  unfold tailWord_2210050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151786410843442833764901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53738097095582514223373069 20151786410843442833764901)
  ·
    refine ⟨3778459952033145531330919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20151786410843442833764901 3778459952033145531330919)
    ·
      refine ⟨5667689928049718296996379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778459952033145531330919 5667689928049718296996379)
      ·
        refine ⟨8501534892074577445494569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667689928049718296996379 8501534892074577445494569)
        ·
          refine ⟨6376151169055933084120927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8501534892074577445494569 6376151169055933084120927)
          ·
            refine ⟨9564226753583899626181391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6376151169055933084120927 9564226753583899626181391)
            ·
              refine ⟨14346340130375849439272087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9564226753583899626181391 14346340130375849439272087)
              ·
                refine ⟨21519510195563774158908131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14346340130375849439272087 21519510195563774158908131)
                ·
                  refine ⟨32279265293345661238362197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21519510195563774158908131 32279265293345661238362197)
                  ·
                    refine ⟨378272640156394467637057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32279265293345661238362197 378272640156394467637057)
                    ·
                      rfl

theorem cell23_2210050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2210050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210050 prefixEnd_2210050 := by exact prefixLift 2210050
  have htrace : WordTrace (prefixWord ++ tailWord_2210050) baseStart_2210050 baseEnd_2210050 := by
    simpa [prefixWord, tailWord_2210050, baseEnd_2210050] using wordTrace_append hprefix tailTrace_2210050
  have hstable : (prefixWord ++ tailWord_2210050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210050).length < 2 ^ (prefixWord ++ tailWord_2210050).sum := by decide
  have hdescent : baseEnd_2210050 < baseStart_2210050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210057 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 1, 4, 2]
def baseStart_2210057 : Nat := 118140960795 + 2210057 * 2 ^ 59
def prefixEnd_2210057 : Nat := 4983230072969 + 3 ^ 40 * 2210057 * 2
def baseEnd_2210057 : Nat := 1134821514833764875523639

theorem tailTrace_2210057 : CollatzResearch.WordTrace tailWord_2210057 prefixEnd_2210057 1134821514833764875523639 := by
  unfold tailWord_2210057
  simp only [CollatzResearch.WordTrace]
  refine ⟨80607400954348411530564425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53738267302898941020376283 80607400954348411530564425)
  ·
    refine ⟨60455550715761308647923319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80607400954348411530564425 60455550715761308647923319)
    ·
      refine ⟨90683326073641962971884979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60455550715761308647923319 90683326073641962971884979)
      ·
        refine ⟨136024989110462944457827469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90683326073641962971884979 136024989110462944457827469)
        ·
          refine ⟨51009370916423604171685301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136024989110462944457827469 51009370916423604171685301)
          ·
            refine ⟨4782128523414712891095497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51009370916423604171685301 4782128523414712891095497)
            ·
              refine ⟨3586596392561034668321623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782128523414712891095497 3586596392561034668321623)
              ·
                refine ⟨5379894588841552002482435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586596392561034668321623 5379894588841552002482435)
                ·
                  refine ⟨8069841883262328003723653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379894588841552002482435 8069841883262328003723653)
                  ·
                    refine ⟨1513095353111686500698185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8069841883262328003723653 1513095353111686500698185)
                    ·
                      refine ⟨1134821514833764875523639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513095353111686500698185 1134821514833764875523639)
                      ·
                        rfl

theorem cell23_2210057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4, 2].length) (baseStart_2210057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210057 prefixEnd_2210057 := by exact prefixLift 2210057
  have htrace : WordTrace (prefixWord ++ tailWord_2210057) baseStart_2210057 baseEnd_2210057 := by
    simpa [prefixWord, tailWord_2210057, baseEnd_2210057] using wordTrace_append hprefix tailTrace_2210057
  have hstable : (prefixWord ++ tailWord_2210057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210057).length < 2 ^ (prefixWord ++ tailWord_2210057).sum := by decide
  have hdescent : baseEnd_2210057 < baseStart_2210057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210078 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2210078 : Nat := 118140960795 + 2210078 * 2 ^ 59
def prefixEnd_2210078 : Nat := 4983230072969 + 3 ^ 40 * 2210078 * 2
def baseEnd_2210078 : Nat := 1134832297927509293361043

theorem tailTrace_2210078 : CollatzResearch.WordTrace tailWord_2210078 prefixEnd_2210078 1134832297927509293361043 := by
  unfold tailWord_2210078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076020860909041514634861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53738777924848221411385925 10076020860909041514634861)
  ·
    refine ⟨3778507822840890567988073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10076020860909041514634861 3778507822840890567988073)
    ·
      refine ⟨2833880867130667925991055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3778507822840890567988073 2833880867130667925991055)
      ·
        refine ⟨4250821300696001888986583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2833880867130667925991055 4250821300696001888986583)
        ·
          refine ⟨6376231951044002833479875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250821300696001888986583 6376231951044002833479875)
          ·
            refine ⟨9564347926566004250219813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6376231951044002833479875 9564347926566004250219813)
            ·
              refine ⟨1793315236231125796916215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9564347926566004250219813 1793315236231125796916215)
              ·
                refine ⟨2689972854346688695374323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793315236231125796916215 2689972854346688695374323)
                ·
                  refine ⟨4034959281520033043061485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689972854346688695374323 4034959281520033043061485)
                  ·
                    refine ⟨1513109730570012391148057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4034959281520033043061485 1513109730570012391148057)
                    ·
                      refine ⟨1134832297927509293361043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513109730570012391148057 1134832297927509293361043)
                      ·
                        rfl

theorem cell23_2210078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2210078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210078 prefixEnd_2210078 := by exact prefixLift 2210078
  have htrace : WordTrace (prefixWord ++ tailWord_2210078) baseStart_2210078 baseEnd_2210078 := by
    simpa [prefixWord, tailWord_2210078, baseEnd_2210078] using wordTrace_append hprefix tailTrace_2210078
  have hstable : (prefixWord ++ tailWord_2210078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210078).length < 2 ^ (prefixWord ++ tailWord_2210078).sum := by decide
  have hdescent : baseEnd_2210078 < baseStart_2210078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210103 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_2210103 : Nat := 118140960795 + 2210103 * 2 ^ 59
def prefixEnd_2210103 : Nat := 4983230072969 + 3 ^ 40 * 2210103 * 2
def baseEnd_2210103 : Nat := 1134845134943871695548427

theorem tailTrace_2210103 : CollatzResearch.WordTrace tailWord_2210103 prefixEnd_2210103 1134845134943871695548427 := by
  unfold tailWord_2210103
  simp only [CollatzResearch.WordTrace]
  refine ⟨80609078712181761386738963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53739385808121174257825975 80609078712181761386738963)
  ·
    refine ⟨120913618068272642080108445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80609078712181761386738963 120913618068272642080108445)
    ·
      refine ⟨45342606775602240780040667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120913618068272642080108445 45342606775602240780040667)
      ·
        refine ⟨68013910163403361170061001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45342606775602240780040667 68013910163403361170061001)
        ·
          refine ⟨51010432622552520877545751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68013910163403361170061001 51010432622552520877545751)
          ·
            refine ⟨76515648933828781316318627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51010432622552520877545751 76515648933828781316318627)
            ·
              refine ⟨114773473400743171974477941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76515648933828781316318627 114773473400743171974477941)
              ·
                refine ⟨10760013131319672372607307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114773473400743171974477941 10760013131319672372607307)
                ·
                  refine ⟨16140019696979508558910961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10760013131319672372607307 16140019696979508558910961)
                  ·
                    refine ⟨12105014772734631419183221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16140019696979508558910961 12105014772734631419183221)
                    ·
                      refine ⟨1134845134943871695548427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12105014772734631419183221 1134845134943871695548427)
                      ·
                        rfl

theorem cell23_2210103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_2210103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210103 prefixEnd_2210103 := by exact prefixLift 2210103
  have htrace : WordTrace (prefixWord ++ tailWord_2210103) baseStart_2210103 baseEnd_2210103 := by
    simpa [prefixWord, tailWord_2210103, baseEnd_2210103] using wordTrace_append hprefix tailTrace_2210103
  have hstable : (prefixWord ++ tailWord_2210103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210103).length < 2 ^ (prefixWord ++ tailWord_2210103).sum := by decide
  have hdescent : baseEnd_2210103 < baseStart_2210103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210110 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2210110 : Nat := 118140960795 + 2210110 * 2 ^ 59
def prefixEnd_2210110 : Nat := 4983230072969 + 3 ^ 40 * 2210110 * 2
def baseEnd_2210110 : Nat := 378282909769484389386965

theorem tailTrace_2210110 : CollatzResearch.WordTrace tailWord_2210110 prefixEnd_2210110 378282909769484389386965 := by
  unfold tailWord_2210110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076166752894550197780473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53739556015437601054829189 10076166752894550197780473)
  ·
    refine ⟨7557125064670912648335355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10076166752894550197780473 7557125064670912648335355)
    ·
      refine ⟨11335687597006368972503033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7557125064670912648335355 11335687597006368972503033)
      ·
        refine ⟨8501765697754776729377275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11335687597006368972503033 8501765697754776729377275)
        ·
          refine ⟨12752648546632165094065913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8501765697754776729377275 12752648546632165094065913)
          ·
            refine ⟨9564486409974123820549435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12752648546632165094065913 9564486409974123820549435)
            ·
              refine ⟨14346729614961185730824153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9564486409974123820549435 14346729614961185730824153)
              ·
                refine ⟨10760047211220889298118115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14346729614961185730824153 10760047211220889298118115)
                ·
                  refine ⟨16140070816831333947177173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10760047211220889298118115 16140070816831333947177173)
                  ·
                    refine ⟨378282909769484389386965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16140070816831333947177173 378282909769484389386965)
                    ·
                      rfl

theorem cell23_2210110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2210110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210110 prefixEnd_2210110 := by exact prefixLift 2210110
  have htrace : WordTrace (prefixWord ++ tailWord_2210110) baseStart_2210110 baseEnd_2210110 := by
    simpa [prefixWord, tailWord_2210110, baseEnd_2210110] using wordTrace_append hprefix tailTrace_2210110
  have hstable : (prefixWord ++ tailWord_2210110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210110).length < 2 ^ (prefixWord ++ tailWord_2210110).sum := by decide
  have hdescent : baseEnd_2210110 < baseStart_2210110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210130 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2210130 : Nat := 118140960795 + 2210130 * 2 ^ 59
def prefixEnd_2210130 : Nat := 4983230072969 + 3 ^ 40 * 2210130 * 2
def baseEnd_2210130 : Nat := 1134858998921543089910803

theorem tailTrace_2210130 : CollatzResearch.WordTrace tailWord_2210130 prefixEnd_2210130 1134858998921543089910803 := by
  unfold tailWord_2210130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20152515870770986249492961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53740042322055963331981229 20152515870770986249492961)
  ·
    refine ⟨15114386903078239687119721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20152515870770986249492961 15114386903078239687119721)
    ·
      refine ⟨11335790177308679765339791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15114386903078239687119721 11335790177308679765339791)
      ·
        refine ⟨17003685265963019648009687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11335790177308679765339791 17003685265963019648009687)
        ·
          refine ⟨25505527898944529472014531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17003685265963019648009687 25505527898944529472014531)
          ·
            refine ⟨38258291848416794208021797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25505527898944529472014531 38258291848416794208021797)
            ·
              refine ⟨7173429721578148914004087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38258291848416794208021797 7173429721578148914004087)
              ·
                refine ⟨10760144582367223371006131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7173429721578148914004087 10760144582367223371006131)
                ·
                  refine ⟨16140216873550835056509197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10760144582367223371006131 16140216873550835056509197)
                  ·
                    refine ⟨6052581327581563146190949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16140216873550835056509197 6052581327581563146190949)
                    ·
                      refine ⟨1134858998921543089910803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6052581327581563146190949 1134858998921543089910803)
                      ·
                        rfl

theorem cell23_2210130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2210130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210130 prefixEnd_2210130 := by exact prefixLift 2210130
  have htrace : WordTrace (prefixWord ++ tailWord_2210130) baseStart_2210130 baseEnd_2210130 := by
    simpa [prefixWord, tailWord_2210130, baseEnd_2210130] using wordTrace_append hprefix tailTrace_2210130
  have hstable : (prefixWord ++ tailWord_2210130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210130).length < 2 ^ (prefixWord ++ tailWord_2210130).sum := by decide
  have hdescent : baseEnd_2210130 < baseStart_2210130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210143 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2210143 : Nat := 118140960795 + 2210143 * 2 ^ 59
def prefixEnd_2210143 : Nat := 4983230072969 + 3 ^ 40 * 2210143 * 2
def baseEnd_2210143 : Nat := 1134865674170051539048243

theorem tailTrace_2210143 : CollatzResearch.WordTrace tailWord_2210143 prefixEnd_2210143 1134865674170051539048243 := by
  unfold tailWord_2210143
  simp only [CollatzResearch.WordTrace]
  refine ⟨80610537632036848218195083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53740358421357898812130055 80610537632036848218195083)
  ·
    refine ⟨120915806448055272327292625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80610537632036848218195083 120915806448055272327292625)
    ·
      refine ⟨90686854836041454245469469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120915806448055272327292625 90686854836041454245469469)
      ·
        refine ⟨34007570563515545342051051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90686854836041454245469469 34007570563515545342051051)
        ·
          refine ⟨51011355845273318013076577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34007570563515545342051051 51011355845273318013076577)
          ·
            refine ⟨38258516883954988509807433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51011355845273318013076577 38258516883954988509807433)
            ·
              refine ⟨28693887662966241382355575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38258516883954988509807433 28693887662966241382355575)
              ·
                refine ⟨43040831494449362073533363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28693887662966241382355575 43040831494449362073533363)
                ·
                  refine ⟨64561247241674043110300045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43040831494449362073533363 64561247241674043110300045)
                  ·
                    refine ⟨24210467715627766166362517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64561247241674043110300045 24210467715627766166362517)
                    ·
                      refine ⟨1134865674170051539048243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24210467715627766166362517 1134865674170051539048243)
                      ·
                        rfl

theorem cell23_2210143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2210143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210143 prefixEnd_2210143 := by exact prefixLift 2210143
  have htrace : WordTrace (prefixWord ++ tailWord_2210143) baseStart_2210143 baseEnd_2210143 := by
    simpa [prefixWord, tailWord_2210143, baseEnd_2210143] using wordTrace_append hprefix tailTrace_2210143
  have hstable : (prefixWord ++ tailWord_2210143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210143).length < 2 ^ (prefixWord ++ tailWord_2210143).sum := by decide
  have hdescent : baseEnd_2210143 < baseStart_2210143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210153 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 8]
def baseStart_2210153 : Nat := 118140960795 + 2210153 * 2 ^ 59
def prefixEnd_2210153 : Nat := 4983230072969 + 3 ^ 40 * 2210153 * 2
def baseEnd_2210153 : Nat := 126096756552955166658133

theorem tailTrace_2210153 : CollatzResearch.WordTrace tailWord_2210153 prefixEnd_2210153 126096756552955166658133 := by
  unfold tailWord_2210153
  simp only [CollatzResearch.WordTrace]
  refine ⟨80610902362000619926059113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53740601574667079950706075 80610902362000619926059113)
  ·
    refine ⟨60458176771500464944544335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80610902362000619926059113 60458176771500464944544335)
    ·
      refine ⟨90687265157250697416816503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60458176771500464944544335 90687265157250697416816503)
      ·
        refine ⟨136030897735876046125224755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90687265157250697416816503 136030897735876046125224755)
        ·
          refine ⟨204046346603814069187837133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136030897735876046125224755 204046346603814069187837133)
          ·
            refine ⟨76517379976430275945438925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204046346603814069187837133 76517379976430275945438925)
            ·
              refine ⟨28694017491161353479539597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76517379976430275945438925 28694017491161353479539597)
              ·
                refine ⟨10760256559185507554827349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28694017491161353479539597 10760256559185507554827349)
                ·
                  refine ⟨126096756552955166658133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10760256559185507554827349 126096756552955166658133)
                  ·
                    rfl

theorem cell23_2210153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_2210153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210153 prefixEnd_2210153 := by exact prefixLift 2210153
  have htrace : WordTrace (prefixWord ++ tailWord_2210153) baseStart_2210153 baseEnd_2210153 := by
    simpa [prefixWord, tailWord_2210153, baseEnd_2210153] using wordTrace_append hprefix tailTrace_2210153
  have hstable : (prefixWord ++ tailWord_2210153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210153).length < 2 ^ (prefixWord ++ tailWord_2210153).sum := by decide
  have hdescent : baseEnd_2210153 < baseStart_2210153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210203 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_2210203 : Nat := 118140960795 + 2210203 * 2 ^ 59
def prefixEnd_2210203 : Nat := 4983230072969 + 3 ^ 40 * 2210203 * 2
def baseEnd_2210203 : Nat := 1134896483009321304297967

theorem tailTrace_2210203 : CollatzResearch.WordTrace tailWord_2210203 prefixEnd_2210203 1134896483009321304297967 := by
  unfold tailWord_2210203
  simp only [CollatzResearch.WordTrace]
  refine ⟨80612726011819478465379263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53741817341212985643586175 80612726011819478465379263)
  ·
    refine ⟨120919089017729217698068895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80612726011819478465379263 120919089017729217698068895)
    ·
      refine ⟨181378633526593826547103343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120919089017729217698068895 181378633526593826547103343)
      ·
        refine ⟨272067950289890739820655015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181378633526593826547103343 272067950289890739820655015)
        ·
          refine ⟨408101925434836109730982523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272067950289890739820655015 408101925434836109730982523)
          ·
            refine ⟨612152888152254164596473785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408101925434836109730982523 612152888152254164596473785)
            ·
              refine ⟨459114666114190623447355339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612152888152254164596473785 459114666114190623447355339)
              ·
                refine ⟨688671999171285935171033009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459114666114190623447355339 688671999171285935171033009)
                ·
                  refine ⟨516503999378464451378274757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688671999171285935171033009 516503999378464451378274757)
                  ·
                    refine ⟨96844499883462084633426517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516503999378464451378274757 96844499883462084633426517)
                    ·
                      refine ⟨1134896483009321304297967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 96844499883462084633426517 1134896483009321304297967)
                      ·
                        rfl

theorem cell23_2210203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_2210203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210203 prefixEnd_2210203 := by exact prefixLift 2210203
  have htrace : WordTrace (prefixWord ++ tailWord_2210203) baseStart_2210203 baseEnd_2210203 := by
    simpa [prefixWord, tailWord_2210203, baseEnd_2210203] using wordTrace_append hprefix tailTrace_2210203
  have hstable : (prefixWord ++ tailWord_2210203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210203).length < 2 ^ (prefixWord ++ tailWord_2210203).sum := by decide
  have hdescent : baseEnd_2210203 < baseStart_2210203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210237 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2210237 : Nat := 118140960795 + 2210237 * 2 ^ 59
def prefixEnd_2210237 : Nat := 4983230072969 + 3 ^ 40 * 2210237 * 2
def baseEnd_2210237 : Nat := 1134913941351574171272811

theorem tailTrace_2210237 : CollatzResearch.WordTrace tailWord_2210237 prefixEnd_2210237 1134913941351574171272811 := by
  unfold tailWord_2210237
  simp only [CollatzResearch.WordTrace]
  refine ⟨80613966093696302272116965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53742644062464201514744643 80613966093696302272116965)
  ·
    refine ⟨15115118642568056676021931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80613966093696302272116965 15115118642568056676021931)
    ·
      refine ⟨22672677963852085014032897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15115118642568056676021931 22672677963852085014032897)
      ·
        refine ⟨17004508472889063760524673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22672677963852085014032897 17004508472889063760524673)
        ·
          refine ⟨12753381354666797820393505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17004508472889063760524673 12753381354666797820393505)
          ·
            refine ⟨9565036016000098365295129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12753381354666797820393505 9565036016000098365295129)
            ·
              refine ⟨7173777012000073773971347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9565036016000098365295129 7173777012000073773971347)
              ·
                refine ⟨10760665518000110660957021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7173777012000073773971347 10760665518000110660957021)
                ·
                  refine ⟨4035249569250041497858883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10760665518000110660957021 4035249569250041497858883)
                  ·
                    refine ⟨6052874353875062246788325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035249569250041497858883 6052874353875062246788325)
                    ·
                      refine ⟨1134913941351574171272811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6052874353875062246788325 1134913941351574171272811)
                      ·
                        rfl

theorem cell23_2210237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2210237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210237 prefixEnd_2210237 := by exact prefixLift 2210237
  have htrace : WordTrace (prefixWord ++ tailWord_2210237) baseStart_2210237 baseEnd_2210237 := by
    simpa [prefixWord, tailWord_2210237, baseEnd_2210237] using wordTrace_append hprefix tailTrace_2210237
  have hstable : (prefixWord ++ tailWord_2210237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210237).length < 2 ^ (prefixWord ++ tailWord_2210237).sum := by decide
  have hdescent : baseEnd_2210237 < baseStart_2210237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210254 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_2210254 : Nat := 118140960795 + 2210254 * 2 ^ 59
def prefixEnd_2210254 : Nat := 4983230072969 + 3 ^ 40 * 2210254 * 2
def baseEnd_2210254 : Nat := 1134922670522700604760233

theorem tailTrace_2210254 : CollatzResearch.WordTrace tailWord_2210254 prefixEnd_2210254 1134922670522700604760233 := by
  unfold tailWord_2210254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076823266829339271935727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53743057423089809450323877 10076823266829339271935727)
  ·
    refine ⟨15115234900244008907903591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10076823266829339271935727 15115234900244008907903591)
    ·
      refine ⟨22672852350366013361855387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15115234900244008907903591 22672852350366013361855387)
      ·
        refine ⟨34009278525549020042783081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22672852350366013361855387 34009278525549020042783081)
        ·
          refine ⟨25506958894161765032087311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34009278525549020042783081 25506958894161765032087311)
          ·
            refine ⟨38260438341242647548130967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25506958894161765032087311 38260438341242647548130967)
            ·
              refine ⟨57390657511863971322196451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38260438341242647548130967 57390657511863971322196451)
              ·
                refine ⟨86085986267795956983294677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57390657511863971322196451 86085986267795956983294677)
                ·
                  refine ⟨2017640303151467741795969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 86085986267795956983294677 2017640303151467741795969)
                  ·
                    refine ⟨1513230227363600806346977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017640303151467741795969 1513230227363600806346977)
                    ·
                      refine ⟨1134922670522700604760233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513230227363600806346977 1134922670522700604760233)
                      ·
                        rfl

theorem cell23_2210254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_2210254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210254 prefixEnd_2210254 := by exact prefixLift 2210254
  have htrace : WordTrace (prefixWord ++ tailWord_2210254) baseStart_2210254 baseEnd_2210254 := by
    simpa [prefixWord, tailWord_2210254, baseEnd_2210254] using wordTrace_append hprefix tailTrace_2210254
  have hstable : (prefixWord ++ tailWord_2210254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210254).length < 2 ^ (prefixWord ++ tailWord_2210254).sum := by decide
  have hdescent : baseEnd_2210254 < baseStart_2210254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210271 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 3, 2, 2]
def baseStart_2210271 : Nat := 118140960795 + 2210271 * 2 ^ 59
def prefixEnd_2210271 : Nat := 4983230072969 + 3 ^ 40 * 2210271 * 2
def baseEnd_2210271 : Nat := 1134931399693827038247655

theorem tailTrace_2210271 : CollatzResearch.WordTrace tailWord_2210271 prefixEnd_2210271 1134931399693827038247655 := by
  unfold tailWord_2210271
  simp only [CollatzResearch.WordTrace]
  refine ⟨80615206175573126078854667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53743470783715417385903111 80615206175573126078854667)
  ·
    refine ⟨120922809263359689118282001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80615206175573126078854667 120922809263359689118282001)
    ·
      refine ⟨90692106947519766838711501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120922809263359689118282001 90692106947519766838711501)
      ·
        refine ⟨34009540105319912564516813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90692106947519766838711501 34009540105319912564516813)
        ·
          refine ⟨12753577539494967211693805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34009540105319912564516813 12753577539494967211693805)
          ·
            refine ⟨4782591577310612704385177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12753577539494967211693805 4782591577310612704385177)
            ·
              refine ⟨3586943682982959528288883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782591577310612704385177 3586943682982959528288883)
              ·
                refine ⟨5380415524474439292433325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586943682982959528288883 5380415524474439292433325)
                ·
                  refine ⟨2017655821677914734662497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5380415524474439292433325 2017655821677914734662497)
                  ·
                    refine ⟨1513241866258436050996873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017655821677914734662497 1513241866258436050996873)
                    ·
                      refine ⟨1134931399693827038247655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513241866258436050996873 1134931399693827038247655)
                      ·
                        rfl

theorem cell23_2210271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_2210271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210271 prefixEnd_2210271 := by exact prefixLift 2210271
  have htrace : WordTrace (prefixWord ++ tailWord_2210271) baseStart_2210271 baseEnd_2210271 := by
    simpa [prefixWord, tailWord_2210271, baseEnd_2210271] using wordTrace_append hprefix tailTrace_2210271
  have hstable : (prefixWord ++ tailWord_2210271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210271).length < 2 ^ (prefixWord ++ tailWord_2210271).sum := by decide
  have hdescent : baseEnd_2210271 < baseStart_2210271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210305 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_2210305 : Nat := 118140960795 + 2210305 * 2 ^ 59
def prefixEnd_2210305 : Nat := 4983230072969 + 3 ^ 40 * 2210305 * 2
def baseEnd_2210305 : Nat := 1134948858036079905222499

theorem tailTrace_2210305 : CollatzResearch.WordTrace tailWord_2210305 prefixEnd_2210305 1134948858036079905222499 := by
  unfold tailWord_2210305
  simp only [CollatzResearch.WordTrace]
  refine ⟨80616446257449949885592369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53744297504966633257061579 80616446257449949885592369)
  ·
    refine ⟨60462334693087462414194277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80616446257449949885592369 60462334693087462414194277)
    ·
      refine ⟨11336687754953899202661427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60462334693087462414194277 11336687754953899202661427)
      ·
        refine ⟨17005031632430848803992141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11336687754953899202661427 17005031632430848803992141)
        ·
          refine ⟨6376886862161568301497053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17005031632430848803992141 6376886862161568301497053)
          ·
            refine ⟨2391332573310588113061395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6376886862161568301497053 2391332573310588113061395)
            ·
              refine ⟨3586998859965882169592093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391332573310588113061395 3586998859965882169592093)
              ·
                refine ⟨1345124572487205813597035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3586998859965882169592093 1345124572487205813597035)
                ·
                  refine ⟨2017686858730808720395553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345124572487205813597035 2017686858730808720395553)
                  ·
                    refine ⟨1513265144048106540296665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017686858730808720395553 1513265144048106540296665)
                    ·
                      refine ⟨1134948858036079905222499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513265144048106540296665 1134948858036079905222499)
                      ·
                        rfl

theorem cell23_2210305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_2210305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210305 prefixEnd_2210305 := by exact prefixLift 2210305
  have htrace : WordTrace (prefixWord ++ tailWord_2210305) baseStart_2210305 baseEnd_2210305 := by
    simpa [prefixWord, tailWord_2210305, baseEnd_2210305] using wordTrace_append hprefix tailTrace_2210305
  have hstable : (prefixWord ++ tailWord_2210305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210305).length < 2 ^ (prefixWord ++ tailWord_2210305).sum := by decide
  have hdescent : baseEnd_2210305 < baseStart_2210305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210372 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2210372 : Nat := 118140960795 + 2210372 * 2 ^ 59
def prefixEnd_2210372 : Nat := 4983230072969 + 3 ^ 40 * 2210372 * 2
def baseEnd_2210372 : Nat := 1134983261239931143084691

theorem tailTrace_2210372 : CollatzResearch.WordTrace tailWord_2210372 prefixEnd_2210372 1134983261239931143084691 := by
  unfold tailWord_2210372
  simp only [CollatzResearch.WordTrace]
  refine ⟨40309444974103610164140685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53745926632138146885520913 40309444974103610164140685)
  ·
    refine ⟨15116041865288853811552757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40309444974103610164140685 15116041865288853811552757)
    ·
      refine ⟨1417128924870830044833071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15116041865288853811552757 1417128924870830044833071)
      ·
        refine ⟨2125693387306245067249607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417128924870830044833071 2125693387306245067249607)
        ·
          refine ⟨3188540080959367600874411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125693387306245067249607 3188540080959367600874411)
          ·
            refine ⟨4782810121439051401311617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188540080959367600874411 4782810121439051401311617)
            ·
              refine ⟨3587107591079288550983713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782810121439051401311617 3587107591079288550983713)
              ·
                refine ⟨2690330693309466413237785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587107591079288550983713 2690330693309466413237785)
                ·
                  refine ⟨2017748019982099809928339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690330693309466413237785 2017748019982099809928339)
                  ·
                    refine ⟨3026622029973149714892509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2017748019982099809928339 3026622029973149714892509)
                    ·
                      refine ⟨1134983261239931143084691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3026622029973149714892509 1134983261239931143084691)
                      ·
                        rfl

theorem cell23_2210372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2210372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210372 prefixEnd_2210372 := by exact prefixLift 2210372
  have htrace : WordTrace (prefixWord ++ tailWord_2210372) baseStart_2210372 baseEnd_2210372 := by
    simpa [prefixWord, tailWord_2210372, baseEnd_2210372] using wordTrace_append hprefix tailTrace_2210372
  have hstable : (prefixWord ++ tailWord_2210372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210372).length < 2 ^ (prefixWord ++ tailWord_2210372).sum := by decide
  have hdescent : baseEnd_2210372 < baseStart_2210372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210378 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_2210378 : Nat := 118140960795 + 2210378 * 2 ^ 59
def prefixEnd_2210378 : Nat := 4983230072969 + 3 ^ 40 * 2210378 * 2
def baseEnd_2210378 : Nat := 1134986342123858119609663

theorem tailTrace_2210378 : CollatzResearch.WordTrace tailWord_2210378 prefixEnd_2210378 1134986342123858119609663 := by
  unfold tailWord_2210378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20154777196546370838249947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53746072524123655568666525 20154777196546370838249947)
  ·
    refine ⟨30232165794819556257374921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20154777196546370838249947 30232165794819556257374921)
    ·
      refine ⟨22674124346114667193031191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30232165794819556257374921 22674124346114667193031191)
      ·
        refine ⟨34011186519172000789546787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22674124346114667193031191 34011186519172000789546787)
        ·
          refine ⟨51016779778758001184320181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34011186519172000789546787 51016779778758001184320181)
          ·
            refine ⟨4782823104258562611030017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51016779778758001184320181 4782823104258562611030017)
            ·
              refine ⟨3587117328193921958272513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782823104258562611030017 3587117328193921958272513)
              ·
                refine ⟨2690337996145441468704385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587117328193921958272513 2690337996145441468704385)
                ·
                  refine ⟨2017753497109081101528289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690337996145441468704385 2017753497109081101528289)
                  ·
                    refine ⟨1513315122831810826146217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017753497109081101528289 1513315122831810826146217)
                    ·
                      refine ⟨1134986342123858119609663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513315122831810826146217 1134986342123858119609663)
                      ·
                        rfl

theorem cell23_2210378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_2210378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210378 prefixEnd_2210378 := by exact prefixLift 2210378
  have htrace : WordTrace (prefixWord ++ tailWord_2210378) baseStart_2210378 baseEnd_2210378 := by
    simpa [prefixWord, tailWord_2210378, baseEnd_2210378] using wordTrace_append hprefix tailTrace_2210378
  have hstable : (prefixWord ++ tailWord_2210378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210378).length < 2 ^ (prefixWord ++ tailWord_2210378).sum := by decide
  have hdescent : baseEnd_2210378 < baseStart_2210378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210404 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_2210404 : Nat := 118140960795 + 2210404 * 2 ^ 59
def prefixEnd_2210404 : Nat := 4983230072969 + 3 ^ 40 * 2210404 * 2
def baseEnd_2210404 : Nat := 1134999692620875017884543

theorem tailTrace_2210404 : CollatzResearch.WordTrace tailWord_2210404 prefixEnd_2210404 1134999692620875017884543 := by
  unfold tailWord_2210404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40310028542045644896723133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53746704722727526528964177 40310028542045644896723133)
  ·
    refine ⟨15116260703267116836271175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40310028542045644896723133 15116260703267116836271175)
    ·
      refine ⟨22674391054900675254406763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15116260703267116836271175 22674391054900675254406763)
      ·
        refine ⟨34011586582351012881610145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22674391054900675254406763 34011586582351012881610145)
        ·
          refine ⟨25508689936763259661207609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34011586582351012881610145 25508689936763259661207609)
          ·
            refine ⟨19131517452572444745905707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25508689936763259661207609 19131517452572444745905707)
            ·
              refine ⟨28697276178858667118858561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19131517452572444745905707 28697276178858667118858561)
              ·
                refine ⟨21522957134144000339143921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28697276178858667118858561 21522957134144000339143921)
                ·
                  refine ⟨16142217850608000254357941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21522957134144000339143921 16142217850608000254357941)
                  ·
                    refine ⟨1513332923494500023846057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16142217850608000254357941 1513332923494500023846057)
                    ·
                      refine ⟨1134999692620875017884543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513332923494500023846057 1134999692620875017884543)
                      ·
                        rfl

theorem cell23_2210404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_2210404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210404 prefixEnd_2210404 := by exact prefixLift 2210404
  have htrace : WordTrace (prefixWord ++ tailWord_2210404) baseStart_2210404 baseEnd_2210404 := by
    simpa [prefixWord, tailWord_2210404, baseEnd_2210404] using wordTrace_append hprefix tailTrace_2210404
  have hstable : (prefixWord ++ tailWord_2210404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210404).length < 2 ^ (prefixWord ++ tailWord_2210404).sum := by decide
  have hdescent : baseEnd_2210404 < baseStart_2210404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210414 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2210414 : Nat := 118140960795 + 2210414 * 2 ^ 59
def prefixEnd_2210414 : Nat := 4983230072969 + 3 ^ 40 * 2210414 * 2
def baseEnd_2210414 : Nat := 378334942475806659586499

theorem tailTrace_2210414 : CollatzResearch.WordTrace tailWord_2210414 prefixEnd_2210414 378334942475806659586499 := by
  unfold tailWord_2210414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077552726756882687663787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53746947876036707667540197 10077552726756882687663787)
  ·
    refine ⟨15116329090135324031495681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10077552726756882687663787 15116329090135324031495681)
    ·
      refine ⟨11337246817601493023621761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15116329090135324031495681 11337246817601493023621761)
      ·
        refine ⟨8502935113201119767716321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11337246817601493023621761 8502935113201119767716321)
        ·
          refine ⟨6377201334900839825787241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8502935113201119767716321 6377201334900839825787241)
          ·
            refine ⟨4782901001175629869340431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6377201334900839825787241 4782901001175629869340431)
            ·
              refine ⟨7174351501763444804010647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4782901001175629869340431 7174351501763444804010647)
              ·
                refine ⟨10761527252645167206015971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7174351501763444804010647 10761527252645167206015971)
                ·
                  refine ⟨16142290878967750809023957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10761527252645167206015971 16142290878967750809023957)
                  ·
                    refine ⟨378334942475806659586499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16142290878967750809023957 378334942475806659586499)
                    ·
                      rfl

theorem cell23_2210414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2210414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210414 prefixEnd_2210414 := by exact prefixLift 2210414
  have htrace : WordTrace (prefixWord ++ tailWord_2210414) baseStart_2210414 baseEnd_2210414 := by
    simpa [prefixWord, tailWord_2210414, baseEnd_2210414] using wordTrace_append hprefix tailTrace_2210414
  have hstable : (prefixWord ++ tailWord_2210414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210414).length < 2 ^ (prefixWord ++ tailWord_2210414).sum := by decide
  have hdescent : baseEnd_2210414 < baseStart_2210414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210507 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_2210507 : Nat := 118140960795 + 2210507 * 2 ^ 59
def prefixEnd_2210507 : Nat := 4983230072969 + 3 ^ 40 * 2210507 * 2
def baseEnd_2210507 : Nat := 1135052581128288114896569

theorem tailTrace_2210507 : CollatzResearch.WordTrace tailWord_2210507 prefixEnd_2210507 1135052581128288114896569 := by
  unfold tailWord_2210507
  simp only [CollatzResearch.WordTrace]
  refine ⟨80623813802718138384445775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53749209201812092256297183 80623813802718138384445775)
  ·
    refine ⟨120935720704077207576668663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80623813802718138384445775 120935720704077207576668663)
    ·
      refine ⟨181403581056115811365002995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120935720704077207576668663 181403581056115811365002995)
      ·
        refine ⟨272105371584173717047504493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181403581056115811365002995 272105371584173717047504493)
        ·
          refine ⟨102039514344065143892814185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272105371584173717047504493 102039514344065143892814185)
          ·
            refine ⟨76529635758048857919610639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102039514344065143892814185 76529635758048857919610639)
            ·
              refine ⟨114794453637073286879415959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76529635758048857919610639 114794453637073286879415959)
              ·
                refine ⟨172191680455609930319123939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114794453637073286879415959 172191680455609930319123939)
                ·
                  refine ⟨258287520683414895478685909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172191680455609930319123939 258287520683414895478685909)
                  ·
                    refine ⟨6053613766017536612781701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 258287520683414895478685909 6053613766017536612781701)
                    ·
                      refine ⟨1135052581128288114896569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6053613766017536612781701 1135052581128288114896569)
                      ·
                        rfl

theorem cell23_2210507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_2210507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210507 prefixEnd_2210507 := by exact prefixLift 2210507
  have htrace : WordTrace (prefixWord ++ tailWord_2210507) baseStart_2210507 baseEnd_2210507 := by
    simpa [prefixWord, tailWord_2210507, baseEnd_2210507] using wordTrace_append hprefix tailTrace_2210507
  have hstable : (prefixWord ++ tailWord_2210507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210507).length < 2 ^ (prefixWord ++ tailWord_2210507).sum := by decide
  have hdescent : baseEnd_2210507 < baseStart_2210507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210508 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 6]
def baseStart_2210508 : Nat := 118140960795 + 2210508 * 2 ^ 59
def prefixEnd_2210508 : Nat := 4983230072969 + 3 ^ 40 * 2210508 * 2
def baseEnd_2210508 : Nat := 126117010512104734553785

theorem tailTrace_2210508 : CollatzResearch.WordTrace tailWord_2210508 prefixEnd_2210508 126117010512104734553785 := by
  unfold tailWord_2210508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40311925137857257777616089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53749233517143010370154785 40311925137857257777616089)
  ·
    refine ⟨30233943853392943333212067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40311925137857257777616089 30233943853392943333212067)
    ·
      refine ⟨45350915780089414999818101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30233943853392943333212067 45350915780089414999818101)
      ·
        refine ⟨4251648354383382656232947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45350915780089414999818101 4251648354383382656232947)
        ·
          refine ⟨6377472531575073984349421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251648354383382656232947 6377472531575073984349421)
          ·
            refine ⟨2391552199340652744131033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6377472531575073984349421 2391552199340652744131033)
            ·
              refine ⟨1793664149505489558098275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2391552199340652744131033 1793664149505489558098275)
              ·
                refine ⟨2690496224258234337147413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793664149505489558098275 2690496224258234337147413)
                ·
                  refine ⟨126117010512104734553785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2690496224258234337147413 126117010512104734553785)
                  ·
                    rfl

theorem cell23_2210508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_2210508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210508 prefixEnd_2210508 := by exact prefixLift 2210508
  have htrace : WordTrace (prefixWord ++ tailWord_2210508) baseStart_2210508 baseEnd_2210508 := by
    simpa [prefixWord, tailWord_2210508, baseEnd_2210508] using wordTrace_append hprefix tailTrace_2210508
  have hstable : (prefixWord ++ tailWord_2210508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210508).length < 2 ^ (prefixWord ++ tailWord_2210508).sum := by decide
  have hdescent : baseEnd_2210508 < baseStart_2210508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210591 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2210591 : Nat := 118140960795 + 2210591 * 2 ^ 59
def prefixEnd_2210591 : Nat := 4983230072969 + 3 ^ 40 * 2210591 * 2
def baseEnd_2210591 : Nat := 1135095713503265786246183

theorem tailTrace_2210591 : CollatzResearch.WordTrace tailWord_2210591 prefixEnd_2210591 1135095713503265786246183 := by
  unfold tailWord_2210591
  simp only [CollatzResearch.WordTrace]
  refine ⟨80626877534413820730503627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53751251689609213820335751 80626877534413820730503627)
  ·
    refine ⟨120940316301620731095755441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80626877534413820730503627 120940316301620731095755441)
    ·
      refine ⟨90705237226215548321816581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120940316301620731095755441 90705237226215548321816581)
      ·
        refine ⟨17007231979915415310340609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90705237226215548321816581 17007231979915415310340609)
        ·
          refine ⟨12755423984936561482755457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17007231979915415310340609 12755423984936561482755457)
          ·
            refine ⟨9566567988702421112066593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12755423984936561482755457 9566567988702421112066593)
            ·
              refine ⟨7174925991526815834049945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9566567988702421112066593 7174925991526815834049945)
              ·
                refine ⟨5381194493645111875537459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7174925991526815834049945 5381194493645111875537459)
                ·
                  refine ⟨8071791740467667813306189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381194493645111875537459 8071791740467667813306189)
                  ·
                    refine ⟨3026921902675375429989821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8071791740467667813306189 3026921902675375429989821)
                    ·
                      refine ⟨1135095713503265786246183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3026921902675375429989821 1135095713503265786246183)
                      ·
                        rfl

theorem cell23_2210591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2210591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210591 prefixEnd_2210591 := by exact prefixLift 2210591
  have htrace : WordTrace (prefixWord ++ tailWord_2210591) baseStart_2210591 baseEnd_2210591 := by
    simpa [prefixWord, tailWord_2210591, baseEnd_2210591] using wordTrace_append hprefix tailTrace_2210591
  have hstable : (prefixWord ++ tailWord_2210591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210591).length < 2 ^ (prefixWord ++ tailWord_2210591).sum := by decide
  have hdescent : baseEnd_2210591 < baseStart_2210591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210592 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2210592 : Nat := 118140960795 + 2210592 * 2 ^ 59
def prefixEnd_2210592 : Nat := 4983230072969 + 3 ^ 40 * 2210592 * 2
def baseEnd_2210592 : Nat := 1135096226983920282333679

theorem tailTrace_2210592 : CollatzResearch.WordTrace tailWord_2210592 prefixEnd_2210592 1135096226983920282333679 := by
  unfold tailWord_2210592
  simp only [CollatzResearch.WordTrace]
  refine ⟨40313457003705098950645015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53751276004940131934193353 40313457003705098950645015)
  ·
    refine ⟨60470185505557648425967523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40313457003705098950645015 60470185505557648425967523)
    ·
      refine ⟨90705278258336472638951285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60470185505557648425967523 90705278258336472638951285)
      ·
        refine ⟨8503619836719044309901683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90705278258336472638951285 8503619836719044309901683)
        ·
          refine ⟨12755429755078566464852525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8503619836719044309901683 12755429755078566464852525)
          ·
            refine ⟨4783286158154462424319697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12755429755078566464852525 4783286158154462424319697)
            ·
              refine ⟨3587464618615846818239773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4783286158154462424319697 3587464618615846818239773)
              ·
                refine ⟨1345299231980942556839915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3587464618615846818239773 1345299231980942556839915)
                ·
                  refine ⟨2017948847971413835259873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345299231980942556839915 2017948847971413835259873)
                  ·
                    refine ⟨1513461635978560376444905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017948847971413835259873 1513461635978560376444905)
                    ·
                      refine ⟨1135096226983920282333679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513461635978560376444905 1135096226983920282333679)
                      ·
                        rfl

theorem cell23_2210592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2210592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210592 prefixEnd_2210592 := by exact prefixLift 2210592
  have htrace : WordTrace (prefixWord ++ tailWord_2210592) baseStart_2210592 baseEnd_2210592 := by
    simpa [prefixWord, tailWord_2210592, baseEnd_2210592] using wordTrace_append hprefix tailTrace_2210592
  have hstable : (prefixWord ++ tailWord_2210592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210592).length < 2 ^ (prefixWord ++ tailWord_2210592).sum := by decide
  have hdescent : baseEnd_2210592 < baseStart_2210592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210602 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2210602 : Nat := 118140960795 + 2210602 * 2 ^ 59
def prefixEnd_2210602 : Nat := 4983230072969 + 3 ^ 40 * 2210602 * 2
def baseEnd_2210602 : Nat := 378367120596821747736211

theorem tailTrace_2210602 : CollatzResearch.WordTrace tailWord_2210602 prefixEnd_2210602 378367120596821747736211 := by
  unfold tailWord_2210602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20156819684343492402288515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53751519158249313072769373 20156819684343492402288515)
  ·
    refine ⟨30235229526515238603432773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20156819684343492402288515 30235229526515238603432773)
    ·
      refine ⟨5669105536221607238143645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30235229526515238603432773 5669105536221607238143645)
      ·
        refine ⟨2125914576083102714303867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5669105536221607238143645 2125914576083102714303867)
        ·
          refine ⟨3188871864124654071455801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125914576083102714303867 3188871864124654071455801)
          ·
            refine ⟨2391653898093490553591851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3188871864124654071455801 2391653898093490553591851)
            ·
              refine ⟨3587480847140235830387777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391653898093490553591851 3587480847140235830387777)
              ·
                refine ⟨2690610635355176872790833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587480847140235830387777 2690610635355176872790833)
                ·
                  refine ⟨2017957976516382654593125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690610635355176872790833 2017957976516382654593125)
                  ·
                    refine ⟨378367120596821747736211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017957976516382654593125 378367120596821747736211)
                    ·
                      rfl

theorem cell23_2210602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2210602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210602 prefixEnd_2210602 := by exact prefixLift 2210602
  have htrace : WordTrace (prefixWord ++ tailWord_2210602) baseStart_2210602 baseEnd_2210602 := by
    simpa [prefixWord, tailWord_2210602, baseEnd_2210602] using wordTrace_append hprefix tailTrace_2210602
  have hstable : (prefixWord ++ tailWord_2210602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210602).length < 2 ^ (prefixWord ++ tailWord_2210602).sum := by decide
  have hdescent : baseEnd_2210602 < baseStart_2210602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210671 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 5]
def baseStart_2210671 : Nat := 118140960795 + 2210671 * 2 ^ 59
def prefixEnd_2210671 : Nat := 4983230072969 + 3 ^ 40 * 2210671 * 2
def baseEnd_2210671 : Nat := 126126310217291719249535

theorem tailTrace_2210671 : CollatzResearch.WordTrace tailWord_2210671 prefixEnd_2210671 126126310217291719249535 := by
  unfold tailWord_2210671
  simp only [CollatzResearch.WordTrace]
  refine ⟨80629795374123994393415867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53753196916082662928943911 80629795374123994393415867)
  ·
    refine ⟨120944693061185991590123801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80629795374123994393415867 120944693061185991590123801)
    ·
      refine ⟨90708519795889493692592851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120944693061185991590123801 90708519795889493692592851)
      ·
        refine ⟨136062779693834240538889277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90708519795889493692592851 136062779693834240538889277)
        ·
          refine ⟨51023542385187840202083479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136062779693834240538889277 51023542385187840202083479)
          ·
            refine ⟨76535313577781760303125219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51023542385187840202083479 76535313577781760303125219)
            ·
              refine ⟨114802970366672640454687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76535313577781760303125219 114802970366672640454687829)
              ·
                refine ⟨1345347308984445005328373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 114802970366672640454687829 1345347308984445005328373)
                ·
                  refine ⟨126126310217291719249535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345347308984445005328373 126126310217291719249535)
                  ·
                    rfl

theorem cell23_2210671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 5].length) (baseStart_2210671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210671 prefixEnd_2210671 := by exact prefixLift 2210671
  have htrace : WordTrace (prefixWord ++ tailWord_2210671) baseStart_2210671 baseEnd_2210671 := by
    simpa [prefixWord, tailWord_2210671, baseEnd_2210671] using wordTrace_append hprefix tailTrace_2210671
  have hstable : (prefixWord ++ tailWord_2210671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210671).length < 2 ^ (prefixWord ++ tailWord_2210671).sum := by decide
  have hdescent : baseEnd_2210671 < baseStart_2210671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210684 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_2210684 : Nat := 118140960795 + 2210684 * 2 ^ 59
def prefixEnd_2210684 : Nat := 4983230072969 + 3 ^ 40 * 2210684 * 2
def baseEnd_2210684 : Nat := 378381155734711307461085

theorem tailTrace_2210684 : CollatzResearch.WordTrace tailWord_2210684 prefixEnd_2210684 378381155734711307461085 := by
  unfold tailWord_2210684
  simp only [CollatzResearch.WordTrace]
  refine ⟨40315134761538448806819553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53753513015384598409092737 40315134761538448806819553)
  ·
    refine ⟨30236351071153836605114665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40315134761538448806819553 30236351071153836605114665)
    ·
      refine ⟨22677263303365377453835999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30236351071153836605114665 22677263303365377453835999)
      ·
        refine ⟨34015894955048066180753999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22677263303365377453835999 34015894955048066180753999)
        ·
          refine ⟨51023842432572099271130999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34015894955048066180753999 51023842432572099271130999)
          ·
            refine ⟨76535763648858148906696499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51023842432572099271130999 76535763648858148906696499)
            ·
              refine ⟨114803645473287223360044749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76535763648858148906696499 114803645473287223360044749)
              ·
                refine ⟨43051367052482708760016781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114803645473287223360044749 43051367052482708760016781)
                ·
                  refine ⟨16144262644681015785006293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43051367052482708760016781 16144262644681015785006293)
                  ·
                    refine ⟨378381155734711307461085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16144262644681015785006293 378381155734711307461085)
                    ·
                      rfl

theorem cell23_2210684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_2210684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210684 prefixEnd_2210684 := by exact prefixLift 2210684
  have htrace : WordTrace (prefixWord ++ tailWord_2210684) baseStart_2210684 baseEnd_2210684 := by
    simpa [prefixWord, tailWord_2210684, baseEnd_2210684] using wordTrace_append hprefix tailTrace_2210684
  have hstable : (prefixWord ++ tailWord_2210684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210684).length < 2 ^ (prefixWord ++ tailWord_2210684).sum := by decide
  have hdescent : baseEnd_2210684 < baseStart_2210684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210686 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2210686 : Nat := 118140960795 + 2210686 * 2 ^ 59
def prefixEnd_2210686 : Nat := 4983230072969 + 3 ^ 40 * 2210686 * 2
def baseEnd_2210686 : Nat := 1135144494165442914558247

theorem tailTrace_2210686 : CollatzResearch.WordTrace tailWord_2210686 prefixEnd_2210686 1135144494165442914558247 := by
  unfold tailWord_2210686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078792808633706494401489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53753561646046434636807941 10078792808633706494401489)
  ·
    refine ⟨7559094606475279870801117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10078792808633706494401489 7559094606475279870801117)
    ·
      refine ⟨2834660477428229951550419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7559094606475279870801117 2834660477428229951550419)
      ·
        refine ⟨4251990716142344927325629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2834660477428229951550419 4251990716142344927325629)
        ·
          refine ⟨1594496518553379347747111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4251990716142344927325629 1594496518553379347747111)
          ·
            refine ⟨2391744777830069021620667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594496518553379347747111 2391744777830069021620667)
            ·
              refine ⟨3587617166745103532431001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391744777830069021620667 3587617166745103532431001)
              ·
                refine ⟨2690712875058827649323251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587617166745103532431001 2690712875058827649323251)
                ·
                  refine ⟨4036069312588241473984877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690712875058827649323251 4036069312588241473984877)
                  ·
                    refine ⟨1513525992220590552744329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4036069312588241473984877 1513525992220590552744329)
                    ·
                      refine ⟨1135144494165442914558247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513525992220590552744329 1135144494165442914558247)
                      ·
                        rfl

theorem cell23_2210686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2210686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210686 prefixEnd_2210686 := by exact prefixLift 2210686
  have htrace : WordTrace (prefixWord ++ tailWord_2210686) baseStart_2210686 baseEnd_2210686 := by
    simpa [prefixWord, tailWord_2210686, baseEnd_2210686] using wordTrace_append hprefix tailTrace_2210686
  have hstable : (prefixWord ++ tailWord_2210686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210686).length < 2 ^ (prefixWord ++ tailWord_2210686).sum := by decide
  have hdescent : baseEnd_2210686 < baseStart_2210686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210722 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2210722 : Nat := 118140960795 + 2210722 * 2 ^ 59
def prefixEnd_2210722 : Nat := 4983230072969 + 3 ^ 40 * 2210722 * 2
def baseEnd_2210722 : Nat := 126129219941000530412009

theorem tailTrace_2210722 : CollatzResearch.WordTrace tailWord_2210722 prefixEnd_2210722 126129219941000530412009 := by
  unfold tailWord_2210722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20157913874234807525880605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53754436997959486735681613 20157913874234807525880605)
  ·
    refine ⟨7559217702838052822205227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20157913874234807525880605 7559217702838052822205227)
    ·
      refine ⟨11338826554257079233307841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7559217702838052822205227 11338826554257079233307841)
      ·
        refine ⟨8504119915692809424980881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11338826554257079233307841 8504119915692809424980881)
        ·
          refine ⟨6378089936769607068735661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8504119915692809424980881 6378089936769607068735661)
          ·
            refine ⟨2391783726288602650775873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6378089936769607068735661 2391783726288602650775873)
            ·
              refine ⟨1793837794716451988081905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2391783726288602650775873 1793837794716451988081905)
              ·
                refine ⟨1345378346037338991061429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793837794716451988081905 1345378346037338991061429)
                ·
                  refine ⟨126129219941000530412009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345378346037338991061429 126129219941000530412009)
                  ·
                    rfl

theorem cell23_2210722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2210722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210722 prefixEnd_2210722 := by exact prefixLift 2210722
  have htrace : WordTrace (prefixWord ++ tailWord_2210722) baseStart_2210722 baseEnd_2210722 := by
    simpa [prefixWord, tailWord_2210722, baseEnd_2210722] using wordTrace_append hprefix tailTrace_2210722
  have hstable : (prefixWord ++ tailWord_2210722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210722).length < 2 ^ (prefixWord ++ tailWord_2210722).sum := by decide
  have hdescent : baseEnd_2210722 < baseStart_2210722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210778 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_2210778 : Nat := 118140960795 + 2210778 * 2 ^ 59
def prefixEnd_2210778 : Nat := 4983230072969 + 3 ^ 40 * 2210778 * 2
def baseEnd_2210778 : Nat := 126132414931739617178647

theorem tailTrace_2210778 : CollatzResearch.WordTrace tailWord_2210778 prefixEnd_2210778 126132414931739617178647 := by
  unfold tailWord_2210778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20158424496184087916890247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53755798656490901111707325 20158424496184087916890247)
  ·
    refine ⟨30237636744276131875335371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20158424496184087916890247 30237636744276131875335371)
    ·
      refine ⟨45356455116414197813003057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30237636744276131875335371 45356455116414197813003057)
      ·
        refine ⟨34017341337310648359752293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45356455116414197813003057 34017341337310648359752293)
        ·
          refine ⟨6378251500745746567453555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34017341337310648359752293 6378251500745746567453555)
          ·
            refine ⟨9567377251118619851180333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378251500745746567453555 9567377251118619851180333)
            ·
              refine ⟨3587766469169482444192625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9567377251118619851180333 3587766469169482444192625)
              ·
                refine ⟨2690824851877111833144469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587766469169482444192625 2690824851877111833144469)
                ·
                  refine ⟨126132414931739617178647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2690824851877111833144469 126132414931739617178647)
                  ·
                    rfl

theorem cell23_2210778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_2210778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210778 prefixEnd_2210778 := by exact prefixLift 2210778
  have htrace : WordTrace (prefixWord ++ tailWord_2210778) baseStart_2210778 baseEnd_2210778 := by
    simpa [prefixWord, tailWord_2210778, baseEnd_2210778] using wordTrace_append hprefix tailTrace_2210778
  have hstable : (prefixWord ++ tailWord_2210778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210778).length < 2 ^ (prefixWord ++ tailWord_2210778).sum := by decide
  have hdescent : baseEnd_2210778 < baseStart_2210778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210821 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_2210821 : Nat := 118140960795 + 2210821 * 2 ^ 59
def prefixEnd_2210821 : Nat := 4983230072969 + 3 ^ 40 * 2210821 * 2
def baseEnd_2210821 : Nat := 378404604684599962123375

theorem tailTrace_2210821 : CollatzResearch.WordTrace tailWord_2210821 prefixEnd_2210821 378404604684599962123375 := by
  unfold tailWord_2210821
  simp only [CollatzResearch.WordTrace]
  refine ⟨80635266323580570011376317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53756844215720380007584211 80635266323580570011376317)
  ·
    refine ⟨30238224871342713754266119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80635266323580570011376317 30238224871342713754266119)
    ·
      refine ⟨45357337307014070631399179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30238224871342713754266119 45357337307014070631399179)
      ·
        refine ⟨68036005960521105947098769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45357337307014070631399179 68036005960521105947098769)
        ·
          refine ⟨51027004470390829460324077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68036005960521105947098769 51027004470390829460324077)
          ·
            refine ⟨19135126676396561047621529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51027004470390829460324077 19135126676396561047621529)
            ·
              refine ⟨14351345007297420785716147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19135126676396561047621529 14351345007297420785716147)
              ·
                refine ⟨21527017510946131178574221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14351345007297420785716147 21527017510946131178574221)
                ·
                  refine ⟨8072631566604799191965333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21527017510946131178574221 8072631566604799191965333)
                  ·
                    refine ⟨378404604684599962123375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8072631566604799191965333 378404604684599962123375)
                    ·
                      rfl

theorem cell23_2210821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_2210821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210821 prefixEnd_2210821 := by exact prefixLift 2210821
  have htrace : WordTrace (prefixWord ++ tailWord_2210821) baseStart_2210821 baseEnd_2210821 := by
    simpa [prefixWord, tailWord_2210821, baseEnd_2210821] using wordTrace_append hprefix tailTrace_2210821
  have hstable : (prefixWord ++ tailWord_2210821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210821).length < 2 ^ (prefixWord ++ tailWord_2210821).sum := by decide
  have hdescent : baseEnd_2210821 < baseStart_2210821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210841 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_2210841 : Nat := 118140960795 + 2210841 * 2 ^ 59
def prefixEnd_2210841 : Nat := 4983230072969 + 3 ^ 40 * 2210841 * 2
def baseEnd_2210841 : Nat := 1135224083666889808120033

theorem tailTrace_2210841 : CollatzResearch.WordTrace tailWord_2210841 prefixEnd_2210841 1135224083666889808120033 := by
  unfold tailWord_2210841
  simp only [CollatzResearch.WordTrace]
  refine ⟨80635995783508113427104377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53757330522338742284736251 80635995783508113427104377)
  ·
    refine ⟨60476996837631085070328283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80635995783508113427104377 60476996837631085070328283)
    ·
      refine ⟨90715495256446627605492425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60476996837631085070328283 90715495256446627605492425)
      ·
        refine ⟨68036621442334970704119319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90715495256446627605492425 68036621442334970704119319)
        ·
          refine ⟨102054932163502456056178979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68036621442334970704119319 102054932163502456056178979)
          ·
            refine ⟨153082398245253684084268469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102054932163502456056178979 153082398245253684084268469)
            ·
              refine ⟨14351474835492532882900169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153082398245253684084268469 14351474835492532882900169)
              ·
                refine ⟨10763606126619399662175127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14351474835492532882900169 10763606126619399662175127)
                ·
                  refine ⟨16145409189929099493262691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10763606126619399662175127 16145409189929099493262691)
                  ·
                    refine ⟨24218113784893649239894037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16145409189929099493262691 24218113784893649239894037)
                    ·
                      refine ⟨1135224083666889808120033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24218113784893649239894037 1135224083666889808120033)
                      ·
                        rfl

theorem cell23_2210841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_2210841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210841 prefixEnd_2210841 := by exact prefixLift 2210841
  have htrace : WordTrace (prefixWord ++ tailWord_2210841) baseStart_2210841 baseEnd_2210841 := by
    simpa [prefixWord, tailWord_2210841, baseEnd_2210841] using wordTrace_append hprefix tailTrace_2210841
  have hstable : (prefixWord ++ tailWord_2210841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210841).length < 2 ^ (prefixWord ++ tailWord_2210841).sum := by decide
  have hdescent : baseEnd_2210841 < baseStart_2210841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210851 : List Nat := [1, 1, 1, 4, 3, 2, 1, 10]
def baseStart_2210851 : Nat := 118140960795 + 2210851 * 2 ^ 59
def prefixEnd_2210851 : Nat := 4983230072969 + 3 ^ 40 * 2210851 * 2
def baseEnd_2210851 : Nat := 42045526610127213666481

theorem tailTrace_2210851 : CollatzResearch.WordTrace tailWord_2210851 prefixEnd_2210851 42045526610127213666481 := by
  unfold tailWord_2210851
  simp only [CollatzResearch.WordTrace]
  refine ⟨80636360513471885134968407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53757573675647923423312271 80636360513471885134968407)
  ·
    refine ⟨120954540770207827702452611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80636360513471885134968407 120954540770207827702452611)
    ·
      refine ⟨181431811155311741553678917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120954540770207827702452611 181431811155311741553678917)
      ·
        refine ⟨34018464591620951541314797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181431811155311741553678917 34018464591620951541314797)
        ·
          refine ⟨12756924221857856827993049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34018464591620951541314797 12756924221857856827993049)
          ·
            refine ⟨9567693166393392620994787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12756924221857856827993049 9567693166393392620994787)
            ·
              refine ⟨14351539749590088931492181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9567693166393392620994787 14351539749590088931492181)
              ·
                refine ⟨42045526610127213666481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14351539749590088931492181 42045526610127213666481)
                ·
                  rfl

theorem cell23_2210851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 10].length) (baseStart_2210851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210851 prefixEnd_2210851 := by exact prefixLift 2210851
  have htrace : WordTrace (prefixWord ++ tailWord_2210851) baseStart_2210851 baseEnd_2210851 := by
    simpa [prefixWord, tailWord_2210851, baseEnd_2210851] using wordTrace_append hprefix tailTrace_2210851
  have hstable : (prefixWord ++ tailWord_2210851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210851).length < 2 ^ (prefixWord ++ tailWord_2210851).sum := by decide
  have hdescent : baseEnd_2210851 < baseStart_2210851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210862 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2210862 : Nat := 118140960795 + 2210862 * 2 ^ 59
def prefixEnd_2210862 : Nat := 4983230072969 + 3 ^ 40 * 2210862 * 2
def baseEnd_2210862 : Nat := 1135234866760634225957437

theorem tailTrace_2210862 : CollatzResearch.WordTrace tailWord_2210862 prefixEnd_2210862 1135234866760634225957437 := by
  unfold tailWord_2210862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079595214554004251702355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53757841144288022675745893 10079595214554004251702355)
  ·
    refine ⟨15119392821831006377553533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079595214554004251702355 15119392821831006377553533)
    ·
      refine ⟨5669772308186627391582575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15119392821831006377553533 5669772308186627391582575)
      ·
        refine ⟨8504658462279941087373863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5669772308186627391582575 8504658462279941087373863)
        ·
          refine ⟨12756987693419911631060795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8504658462279941087373863 12756987693419911631060795)
          ·
            refine ⟨19135481540129867446591193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12756987693419911631060795 19135481540129867446591193)
            ·
              refine ⟨14351611155097400584943395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19135481540129867446591193 14351611155097400584943395)
              ·
                refine ⟨21527416732646100877415093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14351611155097400584943395 21527416732646100877415093)
                ·
                  refine ⟨2018195318685571957257665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21527416732646100877415093 2018195318685571957257665)
                  ·
                    refine ⟨1513646489014178967943249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2018195318685571957257665 1513646489014178967943249)
                    ·
                      refine ⟨1135234866760634225957437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513646489014178967943249 1135234866760634225957437)
                      ·
                        rfl

theorem cell23_2210862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2210862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210862 prefixEnd_2210862 := by exact prefixLift 2210862
  have htrace : WordTrace (prefixWord ++ tailWord_2210862) baseStart_2210862 baseEnd_2210862 := by
    simpa [prefixWord, tailWord_2210862, baseEnd_2210862] using wordTrace_append hprefix tailTrace_2210862
  have hstable : (prefixWord ++ tailWord_2210862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210862).length < 2 ^ (prefixWord ++ tailWord_2210862).sum := by decide
  have hdescent : baseEnd_2210862 < baseStart_2210862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210898 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2210898 : Nat := 118140960795 + 2210898 * 2 ^ 59
def prefixEnd_2210898 : Nat := 4983230072969 + 3 ^ 40 * 2210898 * 2
def baseEnd_2210898 : Nat := 378417784021398695035757

theorem tailTrace_2210898 : CollatzResearch.WordTrace tailWord_2210898 prefixEnd_2210898 378417784021398695035757 := by
  unfold tailWord_2210898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20159518686075403040482337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53758716496201074774619565 20159518686075403040482337)
  ·
    refine ⟨15119639014556552280361753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20159518686075403040482337 15119639014556552280361753)
    ·
      refine ⟨11339729260917414210271315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15119639014556552280361753 11339729260917414210271315)
      ·
        refine ⟨17009593891376121315406973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11339729260917414210271315 17009593891376121315406973)
        ·
          refine ⟨6378597709266045493277615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17009593891376121315406973 6378597709266045493277615)
          ·
            refine ⟨9567896563899068239916423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378597709266045493277615 9567896563899068239916423)
            ·
              refine ⟨14351844845848602359874635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9567896563899068239916423 14351844845848602359874635)
              ·
                refine ⟨21527767268772903539811953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14351844845848602359874635 21527767268772903539811953)
                ·
                  refine ⟨16145825451579677654858965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21527767268772903539811953 16145825451579677654858965)
                  ·
                    refine ⟨378417784021398695035757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16145825451579677654858965 378417784021398695035757)
                    ·
                      rfl

theorem cell23_2210898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2210898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210898 prefixEnd_2210898 := by exact prefixLift 2210898
  have htrace : WordTrace (prefixWord ++ tailWord_2210898) baseStart_2210898 baseEnd_2210898 := by
    simpa [prefixWord, tailWord_2210898, baseEnd_2210898] using wordTrace_append hprefix tailTrace_2210898
  have hstable : (prefixWord ++ tailWord_2210898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210898).length < 2 ^ (prefixWord ++ tailWord_2210898).sum := by decide
  have hdescent : baseEnd_2210898 < baseStart_2210898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210922 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2210922 : Nat := 118140960795 + 2210922 * 2 ^ 59
def prefixEnd_2210922 : Nat := 4983230072969 + 3 ^ 40 * 2210922 * 2
def baseEnd_2210922 : Nat := 1135265675599903991207161

theorem tailTrace_2210922 : CollatzResearch.WordTrace tailWord_2210922 prefixEnd_2210922 1135265675599903991207161 := by
  unfold tailWord_2210922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20159737524053666065200755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53759300064143109507202013 20159737524053666065200755)
  ·
    refine ⟨30239606286080499097801133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20159737524053666065200755 30239606286080499097801133)
    ·
      refine ⟨11339852357280187161675425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30239606286080499097801133 11339852357280187161675425)
      ·
        refine ⟨8504889267960140371256569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11339852357280187161675425 8504889267960140371256569)
        ·
          refine ⟨6378666950970105278442427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8504889267960140371256569 6378666950970105278442427)
          ·
            refine ⟨9568000426455157917663641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378666950970105278442427 9568000426455157917663641)
            ·
              refine ⟨7176000319841368438247731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9568000426455157917663641 7176000319841368438247731)
              ·
                refine ⟨10764000479762052657371597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7176000319841368438247731 10764000479762052657371597)
                ·
                  refine ⟨4036500179910769746514349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10764000479762052657371597 4036500179910769746514349)
                  ·
                    refine ⟨1513687567466538654942881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4036500179910769746514349 1513687567466538654942881)
                    ·
                      refine ⟨1135265675599903991207161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513687567466538654942881 1135265675599903991207161)
                      ·
                        rfl

theorem cell23_2210922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2210922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210922 prefixEnd_2210922 := by exact prefixLift 2210922
  have htrace : WordTrace (prefixWord ++ tailWord_2210922) baseStart_2210922 baseEnd_2210922 := by
    simpa [prefixWord, tailWord_2210922, baseEnd_2210922] using wordTrace_append hprefix tailTrace_2210922
  have hstable : (prefixWord ++ tailWord_2210922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210922).length < 2 ^ (prefixWord ++ tailWord_2210922).sum := by decide
  have hdescent : baseEnd_2210922 < baseStart_2210922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210933 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2210933 : Nat := 118140960795 + 2210933 * 2 ^ 59
def prefixEnd_2210933 : Nat := 4983230072969 + 3 ^ 40 * 2210933 * 2
def baseEnd_2210933 : Nat := 1135271323887103448169611

theorem tailTrace_2210933 : CollatzResearch.WordTrace tailWord_2210933 prefixEnd_2210933 1135271323887103448169611 := by
  unfold tailWord_2210933
  simp only [CollatzResearch.WordTrace]
  refine ⟨80639351299174813139453453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53759567532783208759635635 80639351299174813139453453)
  ·
    refine ⟨30239756737190554927295045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80639351299174813139453453 30239756737190554927295045)
    ·
      refine ⟨5669954388223229048867821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30239756737190554927295045 5669954388223229048867821)
      ·
        refine ⟨2126232895583710893325433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5669954388223229048867821 2126232895583710893325433)
        ·
          refine ⟨1594674671687783169994075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2126232895583710893325433 1594674671687783169994075)
          ·
            refine ⟨2392012007531674754991113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594674671687783169994075 2392012007531674754991113)
            ·
              refine ⟨1794009005648756066243335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392012007531674754991113 1794009005648756066243335)
              ·
                refine ⟨2691013508473134099365003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794009005648756066243335 2691013508473134099365003)
                ·
                  refine ⟨4036520262709701149047505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691013508473134099365003 4036520262709701149047505)
                  ·
                    refine ⟨3027390197032275861785629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4036520262709701149047505 3027390197032275861785629)
                    ·
                      refine ⟨1135271323887103448169611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3027390197032275861785629 1135271323887103448169611)
                      ·
                        rfl

theorem cell23_2210933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2210933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210933 prefixEnd_2210933 := by exact prefixLift 2210933
  have htrace : WordTrace (prefixWord ++ tailWord_2210933) baseStart_2210933 baseEnd_2210933 := by
    simpa [prefixWord, tailWord_2210933, baseEnd_2210933] using wordTrace_append hprefix tailTrace_2210933
  have hstable : (prefixWord ++ tailWord_2210933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210933).length < 2 ^ (prefixWord ++ tailWord_2210933).sum := by decide
  have hdescent : baseEnd_2210933 < baseStart_2210933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210935 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_2210935 : Nat := 118140960795 + 2210935 * 2 ^ 59
def prefixEnd_2210935 : Nat := 4983230072969 + 3 ^ 40 * 2210935 * 2
def baseEnd_2210935 : Nat := 1135272350848412440344601

theorem tailTrace_2210935 : CollatzResearch.WordTrace tailWord_2210935 prefixEnd_2210935 1135272350848412440344601 := by
  unfold tailWord_2210935
  simp only [CollatzResearch.WordTrace]
  refine ⟨80639424245167567481026259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53759616163445044987350839 80639424245167567481026259)
  ·
    refine ⟨120959136367751351221539389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80639424245167567481026259 120959136367751351221539389)
    ·
      refine ⟨45359676137906756708077271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120959136367751351221539389 45359676137906756708077271)
      ·
        refine ⟨68039514206860135062115907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45359676137906756708077271 68039514206860135062115907)
        ·
          refine ⟨102059271310290202593173861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68039514206860135062115907 102059271310290202593173861)
          ·
            refine ⟨19136113370679412986220099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102059271310290202593173861 19136113370679412986220099)
            ·
              refine ⟨28704170056019119479330149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19136113370679412986220099 28704170056019119479330149)
              ·
                refine ⟨5382031885503584902374403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28704170056019119479330149 5382031885503584902374403)
                ·
                  refine ⟨8073047828255377353561605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382031885503584902374403 8073047828255377353561605)
                  ·
                    refine ⟨1513696467797883253792801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8073047828255377353561605 1513696467797883253792801)
                    ·
                      refine ⟨1135272350848412440344601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513696467797883253792801 1135272350848412440344601)
                      ·
                        rfl

theorem cell23_2210935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_2210935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2210935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2210935 prefixEnd_2210935 := by exact prefixLift 2210935
  have htrace : WordTrace (prefixWord ++ tailWord_2210935) baseStart_2210935 baseEnd_2210935 := by
    simpa [prefixWord, tailWord_2210935, baseEnd_2210935] using wordTrace_append hprefix tailTrace_2210935
  have hstable : (prefixWord ++ tailWord_2210935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210935).length < 2 ^ (prefixWord ++ tailWord_2210935).sum := by decide
  have hdescent : baseEnd_2210935 < baseStart_2210935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
