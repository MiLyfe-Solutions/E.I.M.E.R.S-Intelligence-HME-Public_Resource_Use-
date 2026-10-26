import V185TrunkScan23Chunk0648

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3836852 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3836852 : Nat := 118140960795 + 3836852 * 2 ^ 59
def prefixEnd_3836852 : Nat := 4983230072969 + 3 ^ 40 * 3836852 * 2
def baseEnd_3836852 : Nat := 218905475129414170289405

theorem tailTrace_3836852 : CollatzResearch.WordTrace tailWord_3836852 prefixEnd_3836852 218905475129414170289405 := by
  unfold tailWord_3836852
  simp only [CollatzResearch.WordTrace]
  refine ⟨69970744547873980498516405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93294326063831973998021873 69970744547873980498516405)
  ·
    refine ⟨6559757301363185671735913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69970744547873980498516405 6559757301363185671735913)
    ·
      refine ⟨4919817976022389253801935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6559757301363185671735913 4919817976022389253801935)
      ·
        refine ⟨7379726964033583880702903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919817976022389253801935 7379726964033583880702903)
        ·
          refine ⟨11069590446050375821054355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379726964033583880702903 11069590446050375821054355)
          ·
            refine ⟨16604385669075563731581533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11069590446050375821054355 16604385669075563731581533)
            ·
              refine ⟨6226644625903336399343075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16604385669075563731581533 6226644625903336399343075)
              ·
                refine ⟨9339966938855004599014613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226644625903336399343075 9339966938855004599014613)
                ·
                  refine ⟨218905475129414170289405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9339966938855004599014613 218905475129414170289405)
                  ·
                    rfl

theorem cell23_3836852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3836852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836852 prefixEnd_3836852 := by exact prefixLift 3836852
  have htrace : WordTrace (prefixWord ++ tailWord_3836852) baseStart_3836852 baseEnd_3836852 := by
    simpa [prefixWord, tailWord_3836852, baseEnd_3836852] using wordTrace_append hprefix tailTrace_3836852
  have hstable : (prefixWord ++ tailWord_3836852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836852).length < 2 ^ (prefixWord ++ tailWord_3836852).sum := by decide
  have hdescent : baseEnd_3836852 < baseStart_3836852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836858 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_3836858 : Nat := 118140960795 + 3836858 * 2 ^ 59
def prefixEnd_3836858 : Nat := 4983230072969 + 3 ^ 40 * 3836858 * 2
def baseEnd_3836858 : Nat := 1970152357048654509129617

theorem tailTrace_3836858 : CollatzResearch.WordTrace tailWord_3836858 prefixEnd_3836858 1970152357048654509129617 := by
  unfold tailWord_3836858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985426983431556005437807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93294471955817482681167485 34985426983431556005437807)
  ·
    refine ⟨52478140475147334008156711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34985426983431556005437807 52478140475147334008156711)
    ·
      refine ⟨78717210712721001012235067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52478140475147334008156711 78717210712721001012235067)
      ·
        refine ⟨118075816069081501518352601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78717210712721001012235067 118075816069081501518352601)
        ·
          refine ⟨88556862051811126138764451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118075816069081501518352601 88556862051811126138764451)
          ·
            refine ⟨132835293077716689208146677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88556862051811126138764451 132835293077716689208146677)
            ·
              refine ⟨12453308726035939613263751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132835293077716689208146677 12453308726035939613263751)
              ·
                refine ⟨18679963089053909419895627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12453308726035939613263751 18679963089053909419895627)
                ·
                  refine ⟨28019944633580864129843441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18679963089053909419895627 28019944633580864129843441)
                  ·
                    refine ⟨21014958475185648097382581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28019944633580864129843441 21014958475185648097382581)
                    ·
                      refine ⟨1970152357048654509129617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21014958475185648097382581 1970152357048654509129617)
                      ·
                        rfl

theorem cell23_3836858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_3836858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836858 prefixEnd_3836858 := by exact prefixLift 3836858
  have htrace : WordTrace (prefixWord ++ tailWord_3836858) baseStart_3836858 baseEnd_3836858 := by
    simpa [prefixWord, tailWord_3836858, baseEnd_3836858] using wordTrace_append hprefix tailTrace_3836858
  have hstable : (prefixWord ++ tailWord_3836858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836858).length < 2 ^ (prefixWord ++ tailWord_3836858).sum := by decide
  have hdescent : baseEnd_3836858 < baseStart_3836858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836882 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3836882 : Nat := 118140960795 + 3836882 * 2 ^ 59
def prefixEnd_3836882 : Nat := 4983230072969 + 3 ^ 40 * 3836882 * 2
def baseEnd_3836882 : Nat := 656721560194787471743169

theorem tailTrace_3836882 : CollatzResearch.WordTrace tailWord_3836882 prefixEnd_3836882 656721560194787471743169 := by
  unfold tailWord_3836882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985645821409819030156225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93295055523759517413749933 34985645821409819030156225)
  ·
    refine ⟨26239234366057364272617169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34985645821409819030156225 26239234366057364272617169)
    ·
      refine ⟨19679425774543023204462877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26239234366057364272617169 19679425774543023204462877)
      ·
        refine ⟨7379784665453633701673579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19679425774543023204462877 7379784665453633701673579)
        ·
          refine ⟨11069676998180450552510369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379784665453633701673579 11069676998180450552510369)
          ·
            refine ⟨8302257748635337914382777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11069676998180450552510369 8302257748635337914382777)
            ·
              refine ⟨6226693311476503435787083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302257748635337914382777 6226693311476503435787083)
              ·
                refine ⟨9340039967214755153680625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226693311476503435787083 9340039967214755153680625)
                ·
                  refine ⟨7005029975411066365260469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9340039967214755153680625 7005029975411066365260469)
                  ·
                    refine ⟨656721560194787471743169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7005029975411066365260469 656721560194787471743169)
                    ·
                      rfl

theorem cell23_3836882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3836882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836882 prefixEnd_3836882 := by exact prefixLift 3836882
  have htrace : WordTrace (prefixWord ++ tailWord_3836882) baseStart_3836882 baseEnd_3836882 := by
    simpa [prefixWord, tailWord_3836882, baseEnd_3836882] using wordTrace_append hprefix tailTrace_3836882
  have hstable : (prefixWord ++ tailWord_3836882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836882).length < 2 ^ (prefixWord ++ tailWord_3836882).sum := by decide
  have hdescent : baseEnd_3836882 < baseStart_3836882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836992 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_3836992 : Nat := 118140960795 + 3836992 * 2 ^ 59
def prefixEnd_3836992 : Nat := 4983230072969 + 3 ^ 40 * 3836992 * 2
def baseEnd_3836992 : Nat := 1970221163456356984854001

theorem tailTrace_3836992 : CollatzResearch.WordTrace tailWord_3836992 prefixEnd_3836992 1970221163456356984854001 := by
  unfold tailWord_3836992
  simp only [CollatzResearch.WordTrace]
  refine ⟨69973297657620382453564615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93297730210160509938086153 69973297657620382453564615)
  ·
    refine ⟨104959946486430573680346923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69973297657620382453564615 104959946486430573680346923)
    ·
      refine ⟨157439919729645860520520385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104959946486430573680346923 157439919729645860520520385)
      ·
        refine ⟨118079939797234395390390289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157439919729645860520520385 118079939797234395390390289)
        ·
          refine ⟨88559954847925796542792717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118079939797234395390390289 88559954847925796542792717)
          ·
            refine ⟨33209983067972173703547269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88559954847925796542792717 33209983067972173703547269)
            ·
              refine ⟨6226871825244782569415113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33209983067972173703547269 6226871825244782569415113)
              ·
                refine ⟨4670153868933586927061335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6226871825244782569415113 4670153868933586927061335)
                ·
                  refine ⟨7005230803400380390592003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670153868933586927061335 7005230803400380390592003)
                  ·
                    refine ⟨10507846205100570585888005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7005230803400380390592003 10507846205100570585888005)
                    ·
                      refine ⟨1970221163456356984854001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10507846205100570585888005 1970221163456356984854001)
                      ·
                        rfl

theorem cell23_3836992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_3836992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836992 prefixEnd_3836992 := by exact prefixLift 3836992
  have htrace : WordTrace (prefixWord ++ tailWord_3836992) baseStart_3836992 baseEnd_3836992 := by
    simpa [prefixWord, tailWord_3836992, baseEnd_3836992] using wordTrace_append hprefix tailTrace_3836992
  have hstable : (prefixWord ++ tailWord_3836992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836992).length < 2 ^ (prefixWord ++ tailWord_3836992).sum := by decide
  have hdescent : baseEnd_3836992 < baseStart_3836992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837042 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3837042 : Nat := 118140960795 + 3837042 * 2 ^ 59
def prefixEnd_3837042 : Nat := 4983230072969 + 3 ^ 40 * 3837042 * 2
def baseEnd_3837042 : Nat := 1970246837489081789228771

theorem tailTrace_3837042 : CollatzResearch.WordTrace tailWord_3837042 prefixEnd_3837042 1970246837489081789228771 := by
  unfold tailWord_3837042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34987104741264905861612345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93298945976706415630966253 34987104741264905861612345)
  ·
    refine ⟨26240328555948679396209259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34987104741264905861612345 26240328555948679396209259)
    ·
      refine ⟨39360492833923019094313889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26240328555948679396209259 39360492833923019094313889)
      ·
        refine ⟨29520369625442264320735417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39360492833923019094313889 29520369625442264320735417)
        ·
          refine ⟨22140277219081698240551563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29520369625442264320735417 22140277219081698240551563)
          ·
            refine ⟨33210415828622547360827345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22140277219081698240551563 33210415828622547360827345)
            ·
              refine ⟨24907811871466910520620509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33210415828622547360827345 24907811871466910520620509)
              ·
                refine ⟨9340429451800091445232691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24907811871466910520620509 9340429451800091445232691)
                ·
                  refine ⟨14010644177700137167849037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9340429451800091445232691 14010644177700137167849037)
                  ·
                    refine ⟨5253991566637551437943389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14010644177700137167849037 5253991566637551437943389)
                    ·
                      refine ⟨1970246837489081789228771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5253991566637551437943389 1970246837489081789228771)
                      ·
                        rfl

theorem cell23_3837042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3837042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837042 prefixEnd_3837042 := by exact prefixLift 3837042
  have htrace : WordTrace (prefixWord ++ tailWord_3837042) baseStart_3837042 baseEnd_3837042 := by
    simpa [prefixWord, tailWord_3837042, baseEnd_3837042] using wordTrace_append hprefix tailTrace_3837042
  have hstable : (prefixWord ++ tailWord_3837042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837042).length < 2 ^ (prefixWord ++ tailWord_3837042).sum := by decide
  have hdescent : baseEnd_3837042 < baseStart_3837042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837082 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3837082 : Nat := 118140960795 + 3837082 * 2 ^ 59
def prefixEnd_3837082 : Nat := 4983230072969 + 3 ^ 40 * 3837082 * 2
def baseEnd_3837082 : Nat := 1970267376715261632728587

theorem tailTrace_3837082 : CollatzResearch.WordTrace tailWord_3837082 prefixEnd_3837082 1970267376715261632728587 := by
  unfold tailWord_3837082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34987469471228677569476375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93299918589943140185270333 34987469471228677569476375)
  ·
    refine ⟨52481204206843016354214563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34987469471228677569476375 52481204206843016354214563)
    ·
      refine ⟨78721806310264524531321845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52481204206843016354214563 78721806310264524531321845)
      ·
        refine ⟨7380169341587299174811423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78721806310264524531321845 7380169341587299174811423)
        ·
          refine ⟨11070254012380948762217135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380169341587299174811423 11070254012380948762217135)
          ·
            refine ⟨16605381018571423143325703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070254012380948762217135 16605381018571423143325703)
            ·
              refine ⟨24908071527857134714988555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16605381018571423143325703 24908071527857134714988555)
              ·
                refine ⟨37362107291785702072482833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24908071527857134714988555 37362107291785702072482833)
                ·
                  refine ⟨28021580468839276554362125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37362107291785702072482833 28021580468839276554362125)
                  ·
                    refine ⟨10508092675814728707885797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28021580468839276554362125 10508092675814728707885797)
                    ·
                      refine ⟨1970267376715261632728587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10508092675814728707885797 1970267376715261632728587)
                      ·
                        rfl

theorem cell23_3837082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3837082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837082 prefixEnd_3837082 := by exact prefixLift 3837082
  have htrace : WordTrace (prefixWord ++ tailWord_3837082) baseStart_3837082 baseEnd_3837082 := by
    simpa [prefixWord, tailWord_3837082, baseEnd_3837082] using wordTrace_append hprefix tailTrace_3837082
  have hstable : (prefixWord ++ tailWord_3837082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837082).length < 2 ^ (prefixWord ++ tailWord_3837082).sum := by decide
  have hdescent : baseEnd_3837082 < baseStart_3837082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837086 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3837086 : Nat := 118140960795 + 3837086 * 2 ^ 59
def prefixEnd_3837086 : Nat := 4983230072969 + 3 ^ 40 * 3837086 * 2
def baseEnd_3837086 : Nat := 1970269430637879617078569

theorem tailTrace_3837086 : CollatzResearch.WordTrace tailWord_3837086 prefixEnd_3837086 1970269430637879617078569 := by
  unfold tailWord_3837086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493752972112527370131389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93300015851266812640700741 17493752972112527370131389)
  ·
    refine ⟨6560157364542197763799271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17493752972112527370131389 6560157364542197763799271)
    ·
      refine ⟨9840236046813296645698907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560157364542197763799271 9840236046813296645698907)
      ·
        refine ⟨14760354070219944968548361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9840236046813296645698907 14760354070219944968548361)
        ·
          refine ⟨11070265552664958726411271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14760354070219944968548361 11070265552664958726411271)
          ·
            refine ⟨16605398328997438089616907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070265552664958726411271 16605398328997438089616907)
            ·
              refine ⟨24908097493496157134425361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16605398328997438089616907 24908097493496157134425361)
              ·
                refine ⟨18681073120122117850819021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24908097493496157134425361 18681073120122117850819021)
                ·
                  refine ⟨7005402420045794194057133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18681073120122117850819021 7005402420045794194057133)
                  ·
                    refine ⟨2627025907517172822771425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7005402420045794194057133 2627025907517172822771425)
                    ·
                      refine ⟨1970269430637879617078569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627025907517172822771425 1970269430637879617078569)
                      ·
                        rfl

theorem cell23_3837086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3837086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837086 prefixEnd_3837086 := by exact prefixLift 3837086
  have htrace : WordTrace (prefixWord ++ tailWord_3837086) baseStart_3837086 baseEnd_3837086 := by
    simpa [prefixWord, tailWord_3837086, baseEnd_3837086] using wordTrace_append hprefix tailTrace_3837086
  have hstable : (prefixWord ++ tailWord_3837086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837086).length < 2 ^ (prefixWord ++ tailWord_3837086).sum := by decide
  have hdescent : baseEnd_3837086 < baseStart_3837086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837092 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_3837092 : Nat := 118140960795 + 3837092 * 2 ^ 59
def prefixEnd_3837092 : Nat := 4983230072969 + 3 ^ 40 * 3837092 * 2
def baseEnd_3837092 : Nat := 656757503840602197867847

theorem tailTrace_3837092 : CollatzResearch.WordTrace tailWord_3837092 prefixEnd_3837092 656757503840602197867847 := by
  unfold tailWord_3837092
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975121307439240992884765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93300161743252321323846353 69975121307439240992884765)
  ·
    refine ⟨26240670490289715372331787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69975121307439240992884765 26240670490289715372331787)
    ·
      refine ⟨39361005735434573058497681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26240670490289715372331787 39361005735434573058497681)
      ·
        refine ⟨29520754301575929793873261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39361005735434573058497681 29520754301575929793873261)
        ·
          refine ⟨11070282863090973672702473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29520754301575929793873261 11070282863090973672702473)
          ·
            refine ⟨8302712147318230254526855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11070282863090973672702473 8302712147318230254526855)
            ·
              refine ⟨12454068220977345381790283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302712147318230254526855 12454068220977345381790283)
              ·
                refine ⟨18681102331466018072685425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12454068220977345381790283 18681102331466018072685425)
                ·
                  refine ⟨14010826748599513554514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18681102331466018072685425 14010826748599513554514069)
                  ·
                    refine ⟨656757503840602197867847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14010826748599513554514069 656757503840602197867847)
                    ·
                      rfl

theorem cell23_3837092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_3837092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837092 prefixEnd_3837092 := by exact prefixLift 3837092
  have htrace : WordTrace (prefixWord ++ tailWord_3837092) baseStart_3837092 baseEnd_3837092 := by
    simpa [prefixWord, tailWord_3837092, baseEnd_3837092] using wordTrace_append hprefix tailTrace_3837092
  have hstable : (prefixWord ++ tailWord_3837092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837092).length < 2 ^ (prefixWord ++ tailWord_3837092).sum := by decide
  have hdescent : baseEnd_3837092 < baseStart_3837092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837120 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2]
def baseStart_3837120 : Nat := 118140960795 + 3837120 * 2 ^ 59
def prefixEnd_3837120 : Nat := 4983230072969 + 3 ^ 40 * 3837120 * 2
def baseEnd_3837120 : Nat := 1970286888980132484053413

theorem tailTrace_3837120 : CollatzResearch.WordTrace tailWord_3837120 prefixEnd_3837120 1970286888980132484053413 := by
  unfold tailWord_3837120
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975631929388521383894407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93300842572518028511859209 69975631929388521383894407)
  ·
    refine ⟨104963447894082782075841611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69975631929388521383894407 104963447894082782075841611)
    ·
      refine ⟨157445171841124173113762417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104963447894082782075841611 157445171841124173113762417)
      ·
        refine ⟨118083878880843129835321813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157445171841124173113762417 118083878880843129835321813)
        ·
          refine ⟨2767590911269760855515355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118083878880843129835321813 2767590911269760855515355)
          ·
            refine ⟨4151386366904641283273033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767590911269760855515355 4151386366904641283273033)
            ·
              refine ⟨3113539775178480962454775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151386366904641283273033 3113539775178480962454775)
              ·
                refine ⟨4670309662767721443682163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113539775178480962454775 4670309662767721443682163)
                ·
                  refine ⟨7005464494151582165523245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670309662767721443682163 7005464494151582165523245)
                  ·
                    refine ⟨2627049185306843312071217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7005464494151582165523245 2627049185306843312071217)
                    ·
                      refine ⟨1970286888980132484053413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627049185306843312071217 1970286888980132484053413)
                      ·
                        rfl

theorem cell23_3837120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_3837120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837120 prefixEnd_3837120 := by exact prefixLift 3837120
  have htrace : WordTrace (prefixWord ++ tailWord_3837120) baseStart_3837120 baseEnd_3837120 := by
    simpa [prefixWord, tailWord_3837120, baseEnd_3837120] using wordTrace_append hprefix tailTrace_3837120
  have hstable : (prefixWord ++ tailWord_3837120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837120).length < 2 ^ (prefixWord ++ tailWord_3837120).sum := by decide
  have hdescent : baseEnd_3837120 < baseStart_3837120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837145 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_3837145 : Nat := 118140960795 + 3837145 * 2 ^ 59
def prefixEnd_3837145 : Nat := 4983230072969 + 3 ^ 40 * 3837145 * 2
def baseEnd_3837145 : Nat := 1970299725996494886240797

theorem tailTrace_3837145 : CollatzResearch.WordTrace tailWord_3837145 prefixEnd_3837145 1970299725996494886240797 := by
  unfold tailWord_3837145
  simp only [CollatzResearch.WordTrace]
  refine ⟨139952175683686472037448889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93301450455790981358299259 139952175683686472037448889)
  ·
    refine ⟨104964131762764854028086667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139952175683686472037448889 104964131762764854028086667)
    ·
      refine ⟨157446197644147281042130001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104964131762764854028086667 157446197644147281042130001)
      ·
        refine ⟨118084648233110460781597501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157446197644147281042130001 118084648233110460781597501)
        ·
          refine ⟨44281743087416422793099063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118084648233110460781597501 44281743087416422793099063)
          ·
            refine ⟨66422614631124634189648595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44281743087416422793099063 66422614631124634189648595)
            ·
              refine ⟨99633921946686951284472893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66422614631124634189648595 99633921946686951284472893)
              ·
                refine ⟨37362720730007606731677335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99633921946686951284472893 37362720730007606731677335)
                ·
                  refine ⟨56044081095011410097516003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37362720730007606731677335 56044081095011410097516003)
                  ·
                    refine ⟨84066121642517115146274005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56044081095011410097516003 84066121642517115146274005)
                    ·
                      refine ⟨1970299725996494886240797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84066121642517115146274005 1970299725996494886240797)
                      ·
                        rfl

theorem cell23_3837145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_3837145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837145 prefixEnd_3837145 := by exact prefixLift 3837145
  have htrace : WordTrace (prefixWord ++ tailWord_3837145) baseStart_3837145 baseEnd_3837145 := by
    simpa [prefixWord, tailWord_3837145, baseEnd_3837145] using wordTrace_append hprefix tailTrace_3837145
  have hstable : (prefixWord ++ tailWord_3837145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837145).length < 2 ^ (prefixWord ++ tailWord_3837145).sum := by decide
  have hdescent : baseEnd_3837145 < baseStart_3837145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837186 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3837186 : Nat := 118140960795 + 3837186 * 2 ^ 59
def prefixEnd_3837186 : Nat := 4983230072969 + 3 ^ 40 * 3837186 * 2
def baseEnd_3837186 : Nat := 656773592901109741942703

theorem tailTrace_3837186 : CollatzResearch.WordTrace tailWord_3837186 prefixEnd_3837186 656773592901109741942703 := by
  unfold tailWord_3837186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34988417769134484009922853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93302447384358624026460941 34988417769134484009922853)
  ·
    refine ⟨6560328331712715751860535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34988417769134484009922853 6560328331712715751860535)
    ·
      refine ⟨9840492497569073627790803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560328331712715751860535 9840492497569073627790803)
      ·
        refine ⟨14760738746353610441686205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9840492497569073627790803 14760738746353610441686205)
        ·
          refine ⟨5535277029882603915632327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14760738746353610441686205 5535277029882603915632327)
          ·
            refine ⟨8302915544823905873448491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535277029882603915632327 8302915544823905873448491)
            ·
              refine ⟨12454373317235858810172737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302915544823905873448491 12454373317235858810172737)
              ·
                refine ⟨9340779987926894107629553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12454373317235858810172737 9340779987926894107629553)
                ·
                  refine ⟨7005584990945170580722165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9340779987926894107629553 7005584990945170580722165)
                  ·
                    refine ⟨656773592901109741942703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7005584990945170580722165 656773592901109741942703)
                    ·
                      rfl

theorem cell23_3837186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3837186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837186 prefixEnd_3837186 := by exact prefixLift 3837186
  have htrace : WordTrace (prefixWord ++ tailWord_3837186) baseStart_3837186 baseEnd_3837186 := by
    simpa [prefixWord, tailWord_3837186, baseEnd_3837186] using wordTrace_append hprefix tailTrace_3837186
  have hstable : (prefixWord ++ tailWord_3837186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837186).length < 2 ^ (prefixWord ++ tailWord_3837186).sum := by decide
  have hdescent : baseEnd_3837186 < baseStart_3837186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837226 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3837226 : Nat := 118140960795 + 3837226 * 2 ^ 59
def prefixEnd_3837226 : Nat := 4983230072969 + 3 ^ 40 * 3837226 * 2
def baseEnd_3837226 : Nat := 1970341317929509069327925

theorem tailTrace_3837226 : CollatzResearch.WordTrace tailWord_3837226 prefixEnd_3837226 1970341317929509069327925 := by
  unfold tailWord_3837226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34988782499098255717786883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93303419997595348580765021 34988782499098255717786883)
  ·
    refine ⟨52483173748647383576680325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34988782499098255717786883 52483173748647383576680325)
    ·
      refine ⟨9840595077871384420627561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52483173748647383576680325 9840595077871384420627561)
      ·
        refine ⟨7380446308403538315470671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840595077871384420627561 7380446308403538315470671)
        ·
          refine ⟨11070669462605307473206007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380446308403538315470671 11070669462605307473206007)
          ·
            refine ⟨16606004193907961209809011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070669462605307473206007 16606004193907961209809011)
            ·
              refine ⟨24909006290861941814713517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16606004193907961209809011 24909006290861941814713517)
              ·
                refine ⟨9340877359073228180517569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24909006290861941814713517 9340877359073228180517569)
                ·
                  refine ⟨7005658019304921135388177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9340877359073228180517569 7005658019304921135388177)
                  ·
                    refine ⟨5254243514478690851541133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7005658019304921135388177 5254243514478690851541133)
                    ·
                      refine ⟨1970341317929509069327925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5254243514478690851541133 1970341317929509069327925)
                      ·
                        rfl

theorem cell23_3837226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3837226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837226 prefixEnd_3837226 := by exact prefixLift 3837226
  have htrace : WordTrace (prefixWord ++ tailWord_3837226) baseStart_3837226 baseEnd_3837226 := by
    simpa [prefixWord, tailWord_3837226, baseEnd_3837226] using wordTrace_append hprefix tailTrace_3837226
  have hstable : (prefixWord ++ tailWord_3837226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837226).length < 2 ^ (prefixWord ++ tailWord_3837226).sum := by decide
  have hdescent : baseEnd_3837226 < baseStart_3837226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837277 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3837277 : Nat := 118140960795 + 3837277 * 2 ^ 59
def prefixEnd_3837277 : Nat := 4983230072969 + 3 ^ 40 * 3837277 * 2
def baseEnd_3837277 : Nat := 1970367505442888369790191

theorem tailTrace_3837277 : CollatzResearch.WordTrace tailWord_3837277 prefixEnd_3837277 1970367505442888369790191 := by
  unfold tailWord_3837277
  simp only [CollatzResearch.WordTrace]
  refine ⟨139956990119208258581254085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93304660079472172387502723 139956990119208258581254085)
  ·
    refine ⟨26241935647351548483985141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139956990119208258581254085 26241935647351548483985141)
    ·
      refine ⟨2460181466939207670373607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26241935647351548483985141 2460181466939207670373607)
      ·
        refine ⟨3690272200408811505560411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460181466939207670373607 3690272200408811505560411)
        ·
          refine ⟨5535408300613217258340617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690272200408811505560411 5535408300613217258340617)
          ·
            refine ⟨4151556225459912943755463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5535408300613217258340617 4151556225459912943755463)
            ·
              refine ⟨6227334338189869415633195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151556225459912943755463 6227334338189869415633195)
              ·
                refine ⟨9341001507284804123449793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227334338189869415633195 9341001507284804123449793)
                ·
                  refine ⟨7005751130463603092587345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341001507284804123449793 7005751130463603092587345)
                  ·
                    refine ⟨5254313347847702319440509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7005751130463603092587345 5254313347847702319440509)
                    ·
                      refine ⟨1970367505442888369790191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5254313347847702319440509 1970367505442888369790191)
                      ·
                        rfl

theorem cell23_3837277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3837277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837277 prefixEnd_3837277 := by exact prefixLift 3837277
  have htrace : WordTrace (prefixWord ++ tailWord_3837277) baseStart_3837277 baseEnd_3837277 := by
    simpa [prefixWord, tailWord_3837277, baseEnd_3837277] using wordTrace_append hprefix tailTrace_3837277
  have hstable : (prefixWord ++ tailWord_3837277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837277).length < 2 ^ (prefixWord ++ tailWord_3837277).sum := by decide
  have hdescent : baseEnd_3837277 < baseStart_3837277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837279 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_3837279 : Nat := 118140960795 + 3837279 * 2 ^ 59
def prefixEnd_3837279 : Nat := 4983230072969 + 3 ^ 40 * 3837279 * 2
def baseEnd_3837279 : Nat := 1970368532404197361965181

theorem tailTrace_3837279 : CollatzResearch.WordTrace tailWord_3837279 prefixEnd_3837279 1970368532404197361965181 := by
  unfold tailWord_3837279
  simp only [CollatzResearch.WordTrace]
  refine ⟨139957063065201012922826891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93304708710134008615217927 139957063065201012922826891)
  ·
    refine ⟨209935594597801519384240337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139957063065201012922826891 209935594597801519384240337)
    ·
      refine ⟨157451695948351139538180253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209935594597801519384240337 157451695948351139538180253)
      ·
        refine ⟨59044385980631677326817595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157451695948351139538180253 59044385980631677326817595)
        ·
          refine ⟨88566578970947515990226393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59044385980631677326817595 88566578970947515990226393)
          ·
            refine ⟨66424934228210636992669795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88566578970947515990226393 66424934228210636992669795)
            ·
              refine ⟨99637401342315955489004693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66424934228210636992669795 99637401342315955489004693)
              ·
                refine ⟨4670503187921060413547095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99637401342315955489004693 4670503187921060413547095)
                ·
                  refine ⟨7005754781881590620320643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670503187921060413547095 7005754781881590620320643)
                  ·
                    refine ⟨10508632172822385930480965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7005754781881590620320643 10508632172822385930480965)
                    ·
                      refine ⟨1970368532404197361965181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10508632172822385930480965 1970368532404197361965181)
                      ·
                        rfl

theorem cell23_3837279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_3837279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837279 prefixEnd_3837279 := by exact prefixLift 3837279
  have htrace : WordTrace (prefixWord ++ tailWord_3837279) baseStart_3837279 baseEnd_3837279 := by
    simpa [prefixWord, tailWord_3837279, baseEnd_3837279] using wordTrace_append hprefix tailTrace_3837279
  have hstable : (prefixWord ++ tailWord_3837279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837279).length < 2 ^ (prefixWord ++ tailWord_3837279).sum := by decide
  have hdescent : baseEnd_3837279 < baseStart_3837279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837283 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3837283 : Nat := 118140960795 + 3837283 * 2 ^ 59
def prefixEnd_3837283 : Nat := 4983230072969 + 3 ^ 40 * 3837283 * 2
def baseEnd_3837283 : Nat := 1970370586326815346315163

theorem tailTrace_3837283 : CollatzResearch.WordTrace tailWord_3837283 prefixEnd_3837283 1970370586326815346315163 := by
  unfold tailWord_3837283
  simp only [CollatzResearch.WordTrace]
  refine ⟨139957208957186521605972503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93304805971457681070648335 139957208957186521605972503)
  ·
    refine ⟨209935813435779782408958755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139957208957186521605972503 209935813435779782408958755)
    ·
      refine ⟨314903720153669673613438133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209935813435779782408958755 314903720153669673613438133)
      ·
        refine ⟨29522223764406531901259825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314903720153669673613438133 29522223764406531901259825)
        ·
          refine ⟨22141667823304898925944869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29522223764406531901259825 22141667823304898925944869)
          ·
            refine ⟨4151562716869668548614663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22141667823304898925944869 4151562716869668548614663)
            ·
              refine ⟨6227344075304502822921995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151562716869668548614663 6227344075304502822921995)
              ·
                refine ⟨9341016112956754234382993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227344075304502822921995 9341016112956754234382993)
                ·
                  refine ⟨7005762084717565675787245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341016112956754234382993 7005762084717565675787245)
                  ·
                    refine ⟨2627160781769087128420217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7005762084717565675787245 2627160781769087128420217)
                    ·
                      refine ⟨1970370586326815346315163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627160781769087128420217 1970370586326815346315163)
                      ·
                        rfl

theorem cell23_3837283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3837283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837283 prefixEnd_3837283 := by exact prefixLift 3837283
  have htrace : WordTrace (prefixWord ++ tailWord_3837283) baseStart_3837283 baseEnd_3837283 := by
    simpa [prefixWord, tailWord_3837283, baseEnd_3837283] using wordTrace_append hprefix tailTrace_3837283
  have hstable : (prefixWord ++ tailWord_3837283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837283).length < 2 ^ (prefixWord ++ tailWord_3837283).sum := by decide
  have hdescent : baseEnd_3837283 < baseStart_3837283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837293 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_3837293 : Nat := 118140960795 + 3837293 * 2 ^ 59
def prefixEnd_3837293 : Nat := 4983230072969 + 3 ^ 40 * 3837293 * 2
def baseEnd_3837293 : Nat := 656791907044453435730039

theorem tailTrace_3837293 : CollatzResearch.WordTrace tailWord_3837293 prefixEnd_3837293 656791907044453435730039 := by
  unfold tailWord_3837293
  simp only [CollatzResearch.WordTrace]
  refine ⟨139957573687150293313836533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93305049124766862209224355 139957573687150293313836533)
  ·
    refine ⟨13121022533170339998172175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139957573687150293313836533 13121022533170339998172175)
    ·
      refine ⟨19681533799755509997258263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121022533170339998172175 19681533799755509997258263)
      ·
        refine ⟨29522300699633264995887395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19681533799755509997258263 29522300699633264995887395)
        ·
          refine ⟨44283451049449897493831093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29522300699633264995887395 44283451049449897493831093)
          ·
            refine ⟨4151573535885927890046665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44283451049449897493831093 4151573535885927890046665)
            ·
              refine ⟨3113680151914445917534999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151573535885927890046665 3113680151914445917534999)
              ·
                refine ⟨4670520227871668876302499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113680151914445917534999 4670520227871668876302499)
                ·
                  refine ⟨7005780341807503314453749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670520227871668876302499 7005780341807503314453749)
                  ·
                    refine ⟨656791907044453435730039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7005780341807503314453749 656791907044453435730039)
                    ·
                      rfl

theorem cell23_3837293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_3837293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837293 prefixEnd_3837293 := by exact prefixLift 3837293
  have htrace : WordTrace (prefixWord ++ tailWord_3837293) baseStart_3837293 baseEnd_3837293 := by
    simpa [prefixWord, tailWord_3837293, baseEnd_3837293] using wordTrace_append hprefix tailTrace_3837293
  have hstable : (prefixWord ++ tailWord_3837293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837293).length < 2 ^ (prefixWord ++ tailWord_3837293).sum := by decide
  have hdescent : baseEnd_3837293 < baseStart_3837293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837296 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2]
def baseStart_3837296 : Nat := 118140960795 + 3837296 * 2 ^ 59
def prefixEnd_3837296 : Nat := 4983230072969 + 3 ^ 40 * 3837296 * 2
def baseEnd_3837296 : Nat := 1970377261575323795452603

theorem tailTrace_3837296 : CollatzResearch.WordTrace tailWord_3837296 prefixEnd_3837296 1970377261575323795452603 := by
  unfold tailWord_3837296
  simp only [CollatzResearch.WordTrace]
  refine ⟨69978841553069712413097871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93305122070759616550797161 69978841553069712413097871)
  ·
    refine ⟨104968262329604568619646807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69978841553069712413097871 104968262329604568619646807)
    ·
      refine ⟨157452393494406852929470211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104968262329604568619646807 157452393494406852929470211)
      ·
        refine ⟨236178590241610279394205317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157452393494406852929470211 236178590241610279394205317)
        ·
          refine ⟨44283485670301927386413497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236178590241610279394205317 44283485670301927386413497)
          ·
            refine ⟨33212614252726445539810123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44283485670301927386413497 33212614252726445539810123)
            ·
              refine ⟨49818921379089668309715185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33212614252726445539810123 49818921379089668309715185)
              ·
                refine ⟨37364191034317251232286389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49818921379089668309715185 37364191034317251232286389)
                ·
                  refine ⟨3502892909467242303026849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37364191034317251232286389 3502892909467242303026849)
                  ·
                    refine ⟨2627169682100431727270137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502892909467242303026849 2627169682100431727270137)
                    ·
                      refine ⟨1970377261575323795452603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627169682100431727270137 1970377261575323795452603)
                      ·
                        rfl

theorem cell23_3837296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2].length) (baseStart_3837296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837296 prefixEnd_3837296 := by exact prefixLift 3837296
  have htrace : WordTrace (prefixWord ++ tailWord_3837296) baseStart_3837296 baseEnd_3837296 := by
    simpa [prefixWord, tailWord_3837296, baseEnd_3837296] using wordTrace_append hprefix tailTrace_3837296
  have hstable : (prefixWord ++ tailWord_3837296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837296).length < 2 ^ (prefixWord ++ tailWord_3837296).sum := by decide
  have hdescent : baseEnd_3837296 < baseStart_3837296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837326 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3837326 : Nat := 118140960795 + 3837326 * 2 ^ 59
def prefixEnd_3837326 : Nat := 4983230072969 + 3 ^ 40 * 3837326 * 2
def baseEnd_3837326 : Nat := 1970392665994958678077465

theorem tailTrace_3837326 : CollatzResearch.WordTrace tailWord_3837326 prefixEnd_3837326 1970392665994958678077465 := by
  unfold tailWord_3837326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494847162003842493723479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93305851530687159966525221 17494847162003842493723479)
  ·
    refine ⟨26242270743005763740585219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17494847162003842493723479 26242270743005763740585219)
    ·
      refine ⟨39363406114508645610877829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26242270743005763740585219 39363406114508645610877829)
      ·
        refine ⟨7380638646470371052039593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39363406114508645610877829 7380638646470371052039593)
        ·
          refine ⟨5535478984852778289029695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7380638646470371052039593 5535478984852778289029695)
          ·
            refine ⟨8303218477279167433544543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535478984852778289029695 8303218477279167433544543)
            ·
              refine ⟨12454827715918751150316815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303218477279167433544543 12454827715918751150316815)
              ·
                refine ⟨18682241573878126725475223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12454827715918751150316815 18682241573878126725475223)
                ·
                  refine ⟨28023362360817190088212835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18682241573878126725475223 28023362360817190088212835)
                  ·
                    refine ⟨42035043541225785132319253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28023362360817190088212835 42035043541225785132319253)
                    ·
                      refine ⟨1970392665994958678077465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42035043541225785132319253 1970392665994958678077465)
                      ·
                        rfl

theorem cell23_3837326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3837326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837326 prefixEnd_3837326 := by exact prefixLift 3837326
  have htrace : WordTrace (prefixWord ++ tailWord_3837326) baseStart_3837326 baseEnd_3837326 := by
    simpa [prefixWord, tailWord_3837326, baseEnd_3837326] using wordTrace_append hprefix tailTrace_3837326
  have hstable : (prefixWord ++ tailWord_3837326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837326).length < 2 ^ (prefixWord ++ tailWord_3837326).sum := by decide
  have hdescent : baseEnd_3837326 < baseStart_3837326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837330 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3837330 : Nat := 118140960795 + 3837330 * 2 ^ 59
def prefixEnd_3837330 : Nat := 4983230072969 + 3 ^ 40 * 3837330 * 2
def baseEnd_3837330 : Nat := 1970394719917576662427447

theorem tailTrace_3837330 : CollatzResearch.WordTrace tailWord_3837330 prefixEnd_3837330 1970394719917576662427447 := by
  unfold tailWord_3837330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34989730797004062158233361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93305948792010832421955629 34989730797004062158233361)
  ·
    refine ⟨26242298097753046618675021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34989730797004062158233361 26242298097753046618675021)
    ·
      refine ⟨9840861786657392482003133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26242298097753046618675021 9840861786657392482003133)
      ·
        refine ⟨3690323169996522180751175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9840861786657392482003133 3690323169996522180751175)
        ·
          refine ⟨5535484754994783271126763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690323169996522180751175 5535484754994783271126763)
          ·
            refine ⟨8303227132492174906690145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535484754994783271126763 8303227132492174906690145)
            ·
              refine ⟨6227420349369131180017609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303227132492174906690145 6227420349369131180017609)
              ·
                refine ⟨4670565262026848385013207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227420349369131180017609 4670565262026848385013207)
                ·
                  refine ⟨7005847893040272577519811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670565262026848385013207 7005847893040272577519811)
                  ·
                    refine ⟨10508771839560408866279717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7005847893040272577519811 10508771839560408866279717)
                    ·
                      refine ⟨1970394719917576662427447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10508771839560408866279717 1970394719917576662427447)
                      ·
                        rfl

theorem cell23_3837330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3837330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837330 prefixEnd_3837330 := by exact prefixLift 3837330
  have htrace : WordTrace (prefixWord ++ tailWord_3837330) baseStart_3837330 baseEnd_3837330 := by
    simpa [prefixWord, tailWord_3837330, baseEnd_3837330] using wordTrace_append hprefix tailTrace_3837330
  have hstable : (prefixWord ++ tailWord_3837330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837330).length < 2 ^ (prefixWord ++ tailWord_3837330).sum := by decide
  have hdescent : baseEnd_3837330 < baseStart_3837330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837380 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3837380 : Nat := 118140960795 + 3837380 * 2 ^ 59
def prefixEnd_3837380 : Nat := 4983230072969 + 3 ^ 40 * 3837380 * 2
def baseEnd_3837380 : Nat := 1970420393950301466802217

theorem tailTrace_3837380 : CollatzResearch.WordTrace tailWord_3837380 prefixEnd_3837380 1970420393950301466802217 := by
  unfold tailWord_3837380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69980373418917553586126797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93307164558556738114835729 69980373418917553586126797)
  ·
    refine ⟨26242640032094082594797549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69980373418917553586126797 26242640032094082594797549)
    ·
      refine ⟨9840990012035280973049081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26242640032094082594797549 9840990012035280973049081)
      ·
        refine ⟨7380742509026460729786811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840990012035280973049081 7380742509026460729786811)
        ·
          refine ⟨11071113763539691094680217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380742509026460729786811 11071113763539691094680217)
          ·
            refine ⟨8303335322654768321010163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11071113763539691094680217 8303335322654768321010163)
            ·
              refine ⟨12455002983982152481515245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303335322654768321010163 12455002983982152481515245)
              ·
                refine ⟨4670626118993307180568217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12455002983982152481515245 4670626118993307180568217)
                ·
                  refine ⟨3502969589244980385426163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670626118993307180568217 3502969589244980385426163)
                  ·
                    refine ⟨5254454383867470578139245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502969589244980385426163 5254454383867470578139245)
                    ·
                      refine ⟨1970420393950301466802217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5254454383867470578139245 1970420393950301466802217)
                      ·
                        rfl

theorem cell23_3837380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3837380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837380 prefixEnd_3837380 := by exact prefixLift 3837380
  have htrace : WordTrace (prefixWord ++ tailWord_3837380) baseStart_3837380 baseEnd_3837380 := by
    simpa [prefixWord, tailWord_3837380, baseEnd_3837380] using wordTrace_append hprefix tailTrace_3837380
  have hstable : (prefixWord ++ tailWord_3837380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837380).length < 2 ^ (prefixWord ++ tailWord_3837380).sum := by decide
  have hdescent : baseEnd_3837380 < baseStart_3837380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837489 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3837489 : Nat := 118140960795 + 3837489 * 2 ^ 59
def prefixEnd_3837489 : Nat := 4983230072969 + 3 ^ 40 * 3837489 * 2
def baseEnd_3837489 : Nat := 1970476363341641540339215

theorem tailTrace_3837489 : CollatzResearch.WordTrace tailWord_3837489 prefixEnd_3837489 1970476363341641540339215 := by
  unfold tailWord_3837489
  simp only [CollatzResearch.WordTrace]
  refine ⟨139964722394440218787971521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93309814929626812525314347 139964722394440218787971521)
  ·
    refine ⟨104973541795830164090978641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139964722394440218787971521 104973541795830164090978641)
    ·
      refine ⟨78730156346872623068233981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104973541795830164090978641 78730156346872623068233981)
      ·
        refine ⟨29523808630077233650587743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78730156346872623068233981 29523808630077233650587743)
        ·
          refine ⟨44285712945115850475881615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29523808630077233650587743 44285712945115850475881615)
          ·
            refine ⟨66428569417673775713822423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44285712945115850475881615 66428569417673775713822423)
            ·
              refine ⟨99642854126510663570733635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66428569417673775713822423 99642854126510663570733635)
              ·
                refine ⟨149464281189765995356100453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99642854126510663570733635 149464281189765995356100453)
                ·
                  refine ⟨28024552723081124129268835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149464281189765995356100453 28024552723081124129268835)
                  ·
                    refine ⟨42036829084621686193903253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28024552723081124129268835 42036829084621686193903253)
                    ·
                      refine ⟨1970476363341641540339215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42036829084621686193903253 1970476363341641540339215)
                      ·
                        rfl

theorem cell23_3837489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3837489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837489 prefixEnd_3837489 := by exact prefixLift 3837489
  have htrace : WordTrace (prefixWord ++ tailWord_3837489) baseStart_3837489 baseEnd_3837489 := by
    simpa [prefixWord, tailWord_3837489, baseEnd_3837489] using wordTrace_append hprefix tailTrace_3837489
  have hstable : (prefixWord ++ tailWord_3837489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837489).length < 2 ^ (prefixWord ++ tailWord_3837489).sum := by decide
  have hdescent : baseEnd_3837489 < baseStart_3837489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837493 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_3837493 : Nat := 118140960795 + 3837493 * 2 ^ 59
def prefixEnd_3837493 : Nat := 4983230072969 + 3 ^ 40 * 3837493 * 2
def baseEnd_3837493 : Nat := 1970478417264259524689197

theorem tailTrace_3837493 : CollatzResearch.WordTrace tailWord_3837493 prefixEnd_3837493 1970478417264259524689197 := by
  unfold tailWord_3837493
  simp only [CollatzResearch.WordTrace]
  refine ⟨139964868286425727471117133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93309912190950484980744755 139964868286425727471117133)
  ·
    refine ⟨52486825607409647801668925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139964868286425727471117133 52486825607409647801668925)
    ·
      refine ⟨19682559602778617925625847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52486825607409647801668925 19682559602778617925625847)
      ·
        refine ⟨29523839404167926888438771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19682559602778617925625847 29523839404167926888438771)
        ·
          refine ⟨44285759106251890332658157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29523839404167926888438771 44285759106251890332658157)
          ·
            refine ⟨16607159664844458874746809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44285759106251890332658157 16607159664844458874746809)
            ·
              refine ⟨12455369748633344156060107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16607159664844458874746809 12455369748633344156060107)
              ·
                refine ⟨18683054622950016234090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12455369748633344156060107 18683054622950016234090161)
                ·
                  refine ⟨14012290967212512175567621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18683054622950016234090161 14012290967212512175567621)
                  ·
                    refine ⟨2627304556352346032918929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14012290967212512175567621 2627304556352346032918929)
                    ·
                      refine ⟨1970478417264259524689197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627304556352346032918929 1970478417264259524689197)
                      ·
                        rfl

theorem cell23_3837493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_3837493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837493 prefixEnd_3837493 := by exact prefixLift 3837493
  have htrace : WordTrace (prefixWord ++ tailWord_3837493) baseStart_3837493 baseEnd_3837493 := by
    simpa [prefixWord, tailWord_3837493, baseEnd_3837493] using wordTrace_append hprefix tailTrace_3837493
  have hstable : (prefixWord ++ tailWord_3837493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837493).length < 2 ^ (prefixWord ++ tailWord_3837493).sum := by decide
  have hdescent : baseEnd_3837493 < baseStart_3837493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837496 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_3837496 : Nat := 118140960795 + 3837496 * 2 ^ 59
def prefixEnd_3837496 : Nat := 4983230072969 + 3 ^ 40 * 3837496 * 2
def baseEnd_3837496 : Nat := 1970479957706223012951683

theorem tailTrace_3837496 : CollatzResearch.WordTrace tailWord_3837496 prefixEnd_3837496 1970479957706223012951683 := by
  unfold tailWord_3837496
  simp only [CollatzResearch.WordTrace]
  refine ⟨69982488852707429491738171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93309985136943239322317561 69982488852707429491738171)
  ·
    refine ⟨104973733279061144237607257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69982488852707429491738171 104973733279061144237607257)
    ·
      refine ⟨78730299959295858178205443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104973733279061144237607257 78730299959295858178205443)
      ·
        refine ⟨118095449938943787267308165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78730299959295858178205443 118095449938943787267308165)
        ·
          refine ⟨22142896863551960112620281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118095449938943787267308165 22142896863551960112620281)
          ·
            refine ⟨16607172647663970084465211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22142896863551960112620281 16607172647663970084465211)
            ·
              refine ⟨24910758971495955126697817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607172647663970084465211 24910758971495955126697817)
              ·
                refine ⟨18683069228621966345023363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24910758971495955126697817 18683069228621966345023363)
                ·
                  refine ⟨28024603842932949517535045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18683069228621966345023363 28024603842932949517535045)
                  ·
                    refine ⟨5254613220549928034537821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28024603842932949517535045 5254613220549928034537821)
                    ·
                      refine ⟨1970479957706223012951683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5254613220549928034537821 1970479957706223012951683)
                      ·
                        rfl

theorem cell23_3837496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_3837496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837496 prefixEnd_3837496 := by exact prefixLift 3837496
  have htrace : WordTrace (prefixWord ++ tailWord_3837496) baseStart_3837496 baseEnd_3837496 := by
    simpa [prefixWord, tailWord_3837496, baseEnd_3837496] using wordTrace_append hprefix tailTrace_3837496
  have hstable : (prefixWord ++ tailWord_3837496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837496).length < 2 ^ (prefixWord ++ tailWord_3837496).sum := by decide
  have hdescent : baseEnd_3837496 < baseStart_3837496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837623 : List Nat := [1, 1, 3, 1, 5, 2, 3, 7]
def baseStart_3837623 : Nat := 118140960795 + 3837623 * 2 ^ 59
def prefixEnd_3837623 : Nat := 4983230072969 + 3 ^ 40 * 3837623 * 2
def baseEnd_3837623 : Nat := 72983154435160889483837

theorem tailTrace_3837623 : CollatzResearch.WordTrace tailWord_3837623 prefixEnd_3837623 72983154435160889483837 := by
  unfold tailWord_3837623
  simp only [CollatzResearch.WordTrace]
  refine ⟨139969609775954759673349523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93313073183969839782233015 139969609775954759673349523)
  ·
    refine ⟨209954414663932139510024285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139969609775954759673349523 209954414663932139510024285)
    ·
      refine ⟨78732905498974552316259107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209954414663932139510024285 78732905498974552316259107)
      ·
        refine ⟨118099358248461828474388661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78732905498974552316259107 118099358248461828474388661)
        ·
          refine ⟨11071814835793296419473937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118099358248461828474388661 11071814835793296419473937)
          ·
            refine ⟨8303861126844972314605453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11071814835793296419473937 8303861126844972314605453)
            ·
              refine ⟨3113947922566864617977045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8303861126844972314605453 3113947922566864617977045)
              ·
                refine ⟨72983154435160889483837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3113947922566864617977045 72983154435160889483837)
                ·
                  rfl

theorem cell23_3837623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 7].length) (baseStart_3837623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837623 prefixEnd_3837623 := by exact prefixLift 3837623
  have htrace : WordTrace (prefixWord ++ tailWord_3837623) baseStart_3837623 baseEnd_3837623 := by
    simpa [prefixWord, tailWord_3837623, baseEnd_3837623] using wordTrace_append hprefix tailTrace_3837623
  have hstable : (prefixWord ++ tailWord_3837623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837623).length < 2 ^ (prefixWord ++ tailWord_3837623).sum := by decide
  have hdescent : baseEnd_3837623 < baseStart_3837623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837644 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_3837644 : Nat := 118140960795 + 3837644 * 2 ^ 59
def prefixEnd_3837644 : Nat := 4983230072969 + 3 ^ 40 * 3837644 * 2
def baseEnd_3837644 : Nat := 656851984281029477967001

theorem tailTrace_3837644 : CollatzResearch.WordTrace tailWord_3837644 prefixEnd_3837644 656851984281029477967001 := by
  unfold tailWord_3837644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69985187854439340129931993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93313583805919120173242657 69985187854439340129931993)
  ·
    refine ⟨52488890890829505097448995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69985187854439340129931993 52488890890829505097448995)
    ·
      refine ⟨78733336336244257646173493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52488890890829505097448995 78733336336244257646173493)
      ·
        refine ⟨7381250281522899154328765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78733336336244257646173493 7381250281522899154328765)
        ·
          refine ⟨2767968855571087182873287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7381250281522899154328765 2767968855571087182873287)
          ·
            refine ⟨4151953283356630774309931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767968855571087182873287 4151953283356630774309931)
            ·
              refine ⟨6227929925034946161464897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151953283356630774309931 6227929925034946161464897)
              ·
                refine ⟨4670947443776209621098673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227929925034946161464897 4670947443776209621098673)
                ·
                  refine ⟨3503210582832157215824005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670947443776209621098673 3503210582832157215824005)
                  ·
                    refine ⟨656851984281029477967001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503210582832157215824005 656851984281029477967001)
                    ·
                      rfl

theorem cell23_3837644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_3837644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837644 prefixEnd_3837644 := by exact prefixLift 3837644
  have htrace : WordTrace (prefixWord ++ tailWord_3837644) baseStart_3837644 baseEnd_3837644 := by
    simpa [prefixWord, tailWord_3837644, baseEnd_3837644] using wordTrace_append hprefix tailTrace_3837644
  have hstable : (prefixWord ++ tailWord_3837644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837644).length < 2 ^ (prefixWord ++ tailWord_3837644).sum := by decide
  have hdescent : baseEnd_3837644 < baseStart_3837644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837667 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3837667 : Nat := 118140960795 + 3837667 * 2 ^ 59
def prefixEnd_3837667 : Nat := 4983230072969 + 3 ^ 40 * 3837667 * 2
def baseEnd_3837667 : Nat := 1970567762898141843913397

theorem tailTrace_3837667 : CollatzResearch.WordTrace tailWord_3837667 prefixEnd_3837667 1970567762898141843913397 := by
  unfold tailWord_3837667
  simp only [CollatzResearch.WordTrace]
  refine ⟨139971214587795355187951255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93314143058530236791967503 139971214587795355187951255)
  ·
    refine ⟨209956821881693032781926883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139971214587795355187951255 209956821881693032781926883)
    ·
      refine ⟨314935232822539549172890325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209956821881693032781926883 314935232822539549172890325)
      ·
        refine ⟨7381294519278270683739617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 314935232822539549172890325 7381294519278270683739617)
        ·
          refine ⟨5535970889458703012804713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7381294519278270683739617 5535970889458703012804713)
          ·
            refine ⟨4151978167094027259603535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5535970889458703012804713 4151978167094027259603535)
            ·
              refine ⟨6227967250641040889405303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151978167094027259603535 6227967250641040889405303)
              ·
                refine ⟨9341950875961561334107955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227967250641040889405303 9341950875961561334107955)
                ·
                  refine ⟨14012926313942342001161933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9341950875961561334107955 14012926313942342001161933)
                  ·
                    refine ⟨5254847367728378250435725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14012926313942342001161933 5254847367728378250435725)
                    ·
                      refine ⟨1970567762898141843913397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5254847367728378250435725 1970567762898141843913397)
                      ·
                        rfl

theorem cell23_3837667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3837667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837667 prefixEnd_3837667 := by exact prefixLift 3837667
  have htrace : WordTrace (prefixWord ++ tailWord_3837667) baseStart_3837667 baseEnd_3837667 := by
    simpa [prefixWord, tailWord_3837667, baseEnd_3837667] using wordTrace_append hprefix tailTrace_3837667
  have hstable : (prefixWord ++ tailWord_3837667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837667).length < 2 ^ (prefixWord ++ tailWord_3837667).sum := by decide
  have hdescent : baseEnd_3837667 < baseStart_3837667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837677 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_3837677 : Nat := 118140960795 + 3837677 * 2 ^ 59
def prefixEnd_3837677 : Nat := 4983230072969 + 3 ^ 40 * 3837677 * 2
def baseEnd_3837677 : Nat := 1970572897704686804788351

theorem tailTrace_3837677 : CollatzResearch.WordTrace tailWord_3837677 prefixEnd_3837677 1970572897704686804788351 := by
  unfold tailWord_3837677
  simp only [CollatzResearch.WordTrace]
  refine ⟨139971579317759126895815285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93314386211839417930543523 139971579317759126895815285)
  ·
    refine ⟨13122335561039918146482683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139971579317759126895815285 13122335561039918146482683)
    ·
      refine ⟨19683503341559877219724025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122335561039918146482683 19683503341559877219724025)
      ·
        refine ⟨14762627506169907914793019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19683503341559877219724025 14762627506169907914793019)
        ·
          refine ⟨22143941259254861872189529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762627506169907914793019 22143941259254861872189529)
          ·
            refine ⟨16607955944441146404142147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22143941259254861872189529 16607955944441146404142147)
            ·
              refine ⟨24911933916661719606213221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607955944441146404142147 24911933916661719606213221)
              ·
                refine ⟨4670987609374072426164979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24911933916661719606213221 4670987609374072426164979)
                ·
                  refine ⟨7006481414061108639247469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670987609374072426164979 7006481414061108639247469)
                  ·
                    refine ⟨2627430530272915739717801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7006481414061108639247469 2627430530272915739717801)
                    ·
                      refine ⟨1970572897704686804788351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627430530272915739717801 1970572897704686804788351)
                      ·
                        rfl

theorem cell23_3837677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_3837677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837677 prefixEnd_3837677 := by exact prefixLift 3837677
  have htrace : WordTrace (prefixWord ++ tailWord_3837677) baseStart_3837677 baseEnd_3837677 := by
    simpa [prefixWord, tailWord_3837677, baseEnd_3837677] using wordTrace_append hprefix tailTrace_3837677
  have hstable : (prefixWord ++ tailWord_3837677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837677).length < 2 ^ (prefixWord ++ tailWord_3837677).sum := by decide
  have hdescent : baseEnd_3837677 < baseStart_3837677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837684 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3837684 : Nat := 118140960795 + 3837684 * 2 ^ 59
def prefixEnd_3837684 : Nat := 4983230072969 + 3 ^ 40 * 3837684 * 2
def baseEnd_3837684 : Nat := 1970576492069268277400819

theorem tailTrace_3837684 : CollatzResearch.WordTrace tailWord_3837684 prefixEnd_3837684 1970576492069268277400819 := by
  unfold tailWord_3837684
  simp only [CollatzResearch.WordTrace]
  refine ⟨69985917314366883545660053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93314556419155844727546737 69985917314366883545660053)
  ·
    refine ⟨3280589874110947666202815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69985917314366883545660053 3280589874110947666202815)
    ·
      refine ⟨4920884811166421499304223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280589874110947666202815 4920884811166421499304223)
      ·
        refine ⟨7381327216749632248956335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920884811166421499304223 7381327216749632248956335)
        ·
          refine ⟨11071990825124448373434503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381327216749632248956335 11071990825124448373434503)
          ·
            refine ⟨16607986237686672560151755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071990825124448373434503 16607986237686672560151755)
            ·
              refine ⟨24911979356530008840227633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607986237686672560151755 24911979356530008840227633)
              ·
                refine ⟨18683984517397506630170725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24911979356530008840227633 18683984517397506630170725)
                ·
                  refine ⟨3503247097012032493157011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18683984517397506630170725 3503247097012032493157011)
                  ·
                    refine ⟨5254870645518048739735517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3503247097012032493157011 5254870645518048739735517)
                    ·
                      refine ⟨1970576492069268277400819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5254870645518048739735517 1970576492069268277400819)
                      ·
                        rfl

theorem cell23_3837684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3837684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837684 prefixEnd_3837684 := by exact prefixLift 3837684
  have htrace : WordTrace (prefixWord ++ tailWord_3837684) baseStart_3837684 baseEnd_3837684 := by
    simpa [prefixWord, tailWord_3837684, baseEnd_3837684] using wordTrace_append hprefix tailTrace_3837684
  have hstable : (prefixWord ++ tailWord_3837684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837684).length < 2 ^ (prefixWord ++ tailWord_3837684).sum := by decide
  have hdescent : baseEnd_3837684 < baseStart_3837684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837702 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3837702 : Nat := 118140960795 + 3837702 * 2 ^ 59
def prefixEnd_3837702 : Nat := 4983230072969 + 3 ^ 40 * 3837702 * 2
def baseEnd_3837702 : Nat := 1970585734721049206975737

theorem tailTrace_3837702 : CollatzResearch.WordTrace tailWord_3837702 prefixEnd_3837702 1970585734721049206975737 := by
  unfold tailWord_3837702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374140348208392380171105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93314994095112370776983573 4374140348208392380171105)
  ·
    refine ⟨3280605261156294285128329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374140348208392380171105 3280605261156294285128329)
    ·
      refine ⟨2460453945867220713846247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280605261156294285128329 2460453945867220713846247)
      ·
        refine ⟨3690680918800831070769371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460453945867220713846247 3690680918800831070769371)
        ·
          refine ⟨5536021378201246606154057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690680918800831070769371 5536021378201246606154057)
          ·
            refine ⟨4152016033650934954615543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536021378201246606154057 4152016033650934954615543)
            ·
              refine ⟨6228024050476402431923315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152016033650934954615543 6228024050476402431923315)
              ·
                refine ⟨9342036075714603647884973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228024050476402431923315 9342036075714603647884973)
                ·
                  refine ⟨3503263528392976367956865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9342036075714603647884973 3503263528392976367956865)
                  ·
                    refine ⟨2627447646294732275967649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503263528392976367956865 2627447646294732275967649)
                    ·
                      refine ⟨1970585734721049206975737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627447646294732275967649 1970585734721049206975737)
                      ·
                        rfl

theorem cell23_3837702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3837702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837702 prefixEnd_3837702 := by exact prefixLift 3837702
  have htrace : WordTrace (prefixWord ++ tailWord_3837702) baseStart_3837702 baseEnd_3837702 := by
    simpa [prefixWord, tailWord_3837702, baseEnd_3837702] using wordTrace_append hprefix tailTrace_3837702
  have hstable : (prefixWord ++ tailWord_3837702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837702).length < 2 ^ (prefixWord ++ tailWord_3837702).sum := by decide
  have hdescent : baseEnd_3837702 < baseStart_3837702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837800 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3837800 : Nat := 118140960795 + 3837800 * 2 ^ 59
def prefixEnd_3837800 : Nat := 4983230072969 + 3 ^ 40 * 3837800 * 2
def baseEnd_3837800 : Nat := 1970636055825189823550285

theorem tailTrace_3837800 : CollatzResearch.WordTrace tailWord_3837800 prefixEnd_3837800 1970636055825189823550285 := by
  unfold tailWord_3837800
  simp only [CollatzResearch.WordTrace]
  refine ⟨69988032748156759451271427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93317376997542345935028569 69988032748156759451271427)
  ·
    refine ⟨104982049122235139176907141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69988032748156759451271427 104982049122235139176907141)
    ·
      refine ⟨19684134210419088595670089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104982049122235139176907141 19684134210419088595670089)
      ·
        refine ⟨14763100657814316446752567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19684134210419088595670089 14763100657814316446752567)
        ·
          refine ⟨22144650986721474670128851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14763100657814316446752567 22144650986721474670128851)
          ·
            refine ⟨33216976480082212005193277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22144650986721474670128851 33216976480082212005193277)
            ·
              refine ⟨12456366180030829501947479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33216976480082212005193277 12456366180030829501947479)
              ·
                refine ⟨18684549270046244252921219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456366180030829501947479 18684549270046244252921219)
                ·
                  refine ⟨28026823905069366379381829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18684549270046244252921219 28026823905069366379381829)
                  ·
                    refine ⟨5255029482200506196134093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28026823905069366379381829 5255029482200506196134093)
                    ·
                      refine ⟨1970636055825189823550285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255029482200506196134093 1970636055825189823550285)
                      ·
                        rfl

theorem cell23_3837800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3837800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837800 prefixEnd_3837800 := by exact prefixLift 3837800
  have htrace : WordTrace (prefixWord ++ tailWord_3837800) baseStart_3837800 baseEnd_3837800 := by
    simpa [prefixWord, tailWord_3837800, baseEnd_3837800] using wordTrace_append hprefix tailTrace_3837800
  have hstable : (prefixWord ++ tailWord_3837800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837800).length < 2 ^ (prefixWord ++ tailWord_3837800).sum := by decide
  have hdescent : baseEnd_3837800 < baseStart_3837800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837840 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2]
def baseStart_3837840 : Nat := 118140960795 + 3837840 * 2 ^ 59
def prefixEnd_3837840 : Nat := 4983230072969 + 3 ^ 40 * 3837840 * 2
def baseEnd_3837840 : Nat := 1970656595051369667050101

theorem tailTrace_3837840 : CollatzResearch.WordTrace tailWord_3837840 prefixEnd_3837840 1970656595051369667050101 := by
  unfold tailWord_3837840
  simp only [CollatzResearch.WordTrace]
  refine ⟨69988762208084302866999487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93318349610779070489332649 69988762208084302866999487)
  ·
    refine ⟨104983143312126454300499231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69988762208084302866999487 104983143312126454300499231)
    ·
      refine ⟨157474714968189681450748847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104983143312126454300499231 157474714968189681450748847)
      ·
        refine ⟨236212072452284522176123271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157474714968189681450748847 236212072452284522176123271)
        ·
          refine ⟨354318108678426783264184907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236212072452284522176123271 354318108678426783264184907)
          ·
            refine ⟨531477163017640174896277361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354318108678426783264184907 531477163017640174896277361)
            ·
              refine ⟨398607872263230131172208021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531477163017640174896277361 398607872263230131172208021)
              ·
                refine ⟨18684744012338912398697251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 398607872263230131172208021 18684744012338912398697251)
                ·
                  refine ⟨28027116018508368598045877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18684744012338912398697251 28027116018508368598045877)
                  ·
                    refine ⟨2627542126735159556066801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28027116018508368598045877 2627542126735159556066801)
                    ·
                      refine ⟨1970656595051369667050101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627542126735159556066801 1970656595051369667050101)
                      ·
                        rfl

theorem cell23_3837840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2].length) (baseStart_3837840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837840 prefixEnd_3837840 := by exact prefixLift 3837840
  have htrace : WordTrace (prefixWord ++ tailWord_3837840) baseStart_3837840 baseEnd_3837840 := by
    simpa [prefixWord, tailWord_3837840, baseEnd_3837840] using wordTrace_append hprefix tailTrace_3837840
  have hstable : (prefixWord ++ tailWord_3837840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837840).length < 2 ^ (prefixWord ++ tailWord_3837840).sum := by decide
  have hdescent : baseEnd_3837840 < baseStart_3837840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837847 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3837847 : Nat := 118140960795 + 3837847 * 2 ^ 59
def prefixEnd_3837847 : Nat := 4983230072969 + 3 ^ 40 * 3837847 * 2
def baseEnd_3837847 : Nat := 1970660189415951139662569

theorem tailTrace_3837847 : CollatzResearch.WordTrace tailWord_3837847 prefixEnd_3837847 1970660189415951139662569 := by
  unfold tailWord_3837847
  simp only [CollatzResearch.WordTrace]
  refine ⟨139977779727143245929503795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93318519818095497286335863 139977779727143245929503795)
  ·
    refine ⟨209966669590714868894255693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139977779727143245929503795 209966669590714868894255693)
    ·
      refine ⟨78737501096518075835345885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209966669590714868894255693 78737501096518075835345885)
      ·
        refine ⟨29526562911194278438254707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78737501096518075835345885 29526562911194278438254707)
        ·
          refine ⟨44289844366791417657382061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29526562911194278438254707 44289844366791417657382061)
          ·
            refine ⟨16608691637546781621518273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44289844366791417657382061 16608691637546781621518273)
            ·
              refine ⟨12456518728160086216138705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16608691637546781621518273 12456518728160086216138705)
              ·
                refine ⟨9342389046120064662104029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12456518728160086216138705 9342389046120064662104029)
                ·
                  refine ⟨3503395892295024248289011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9342389046120064662104029 3503395892295024248289011)
                  ·
                    refine ⟨5255093838442536372433517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3503395892295024248289011 5255093838442536372433517)
                    ·
                      refine ⟨1970660189415951139662569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255093838442536372433517 1970660189415951139662569)
                      ·
                        rfl

theorem cell23_3837847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3837847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837847 prefixEnd_3837847 := by exact prefixLift 3837847
  have htrace : WordTrace (prefixWord ++ tailWord_3837847) baseStart_3837847 baseEnd_3837847 := by
    simpa [prefixWord, tailWord_3837847, baseEnd_3837847] using wordTrace_append hprefix tailTrace_3837847
  have hstable : (prefixWord ++ tailWord_3837847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837847).length < 2 ^ (prefixWord ++ tailWord_3837847).sum := by decide
  have hdescent : baseEnd_3837847 < baseStart_3837847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837858 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3837858 : Nat := 118140960795 + 3837858 * 2 ^ 59
def prefixEnd_3837858 : Nat := 4983230072969 + 3 ^ 40 * 3837858 * 2
def baseEnd_3837858 : Nat := 656888612567716865541673

theorem tailTrace_3837858 : CollatzResearch.WordTrace tailWord_3837858 prefixEnd_3837858 656888612567716865541673 := by
  unfold tailWord_3837858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34994545232525848702038557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93318787286735596538769485 34994545232525848702038557)
  ·
    refine ⟨13122954462197193263264459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34994545232525848702038557 13122954462197193263264459)
    ·
      refine ⟨19684431693295789894896689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122954462197193263264459 19684431693295789894896689)
      ·
        refine ⟨14763323769971842421172517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19684431693295789894896689 14763323769971842421172517)
        ·
          refine ⟨2768123206869720453969847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14763323769971842421172517 2768123206869720453969847)
          ·
            refine ⟨4152184810304580680954771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768123206869720453969847 4152184810304580680954771)
            ·
              refine ⟨6228277215456871021432157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152184810304580680954771 6228277215456871021432157)
              ·
                refine ⟨2335603955796326633037059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228277215456871021432157 2335603955796326633037059)
                ·
                  refine ⟨3503405933694489949555589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335603955796326633037059 3503405933694489949555589)
                  ·
                    refine ⟨656888612567716865541673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503405933694489949555589 656888612567716865541673)
                    ·
                      rfl

theorem cell23_3837858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3837858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837858 prefixEnd_3837858 := by exact prefixLift 3837858
  have htrace : WordTrace (prefixWord ++ tailWord_3837858) baseStart_3837858 baseEnd_3837858 := by
    simpa [prefixWord, tailWord_3837858, baseEnd_3837858] using wordTrace_append hprefix tailTrace_3837858
  have hstable : (prefixWord ++ tailWord_3837858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837858).length < 2 ^ (prefixWord ++ tailWord_3837858).sum := by decide
  have hdescent : baseEnd_3837858 < baseStart_3837858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837880 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_3837880 : Nat := 118140960795 + 3837880 * 2 ^ 59
def prefixEnd_3837880 : Nat := 4983230072969 + 3 ^ 40 * 3837880 * 2
def baseEnd_3837880 : Nat := 656892378092516503516639

theorem tailTrace_3837880 : CollatzResearch.WordTrace tailWord_3837880 prefixEnd_3837880 656892378092516503516639 := by
  unfold tailWord_3837880
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989491668011846282727547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93319322224015795043636729 69989491668011846282727547)
  ·
    refine ⟨104984237502017769424091321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69989491668011846282727547 104984237502017769424091321)
    ·
      refine ⟨78738178126513327068068491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104984237502017769424091321 78738178126513327068068491)
      ·
        refine ⟨118107267189769990602102737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78738178126513327068068491 118107267189769990602102737)
        ·
          refine ⟨88580450392327492951577053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118107267189769990602102737 88580450392327492951577053)
          ·
            refine ⟨33217668897122809856841395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88580450392327492951577053 33217668897122809856841395)
            ·
              refine ⟨49826503345684214785262093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33217668897122809856841395 49826503345684214785262093)
              ·
                refine ⟨18684938754631580544473285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49826503345684214785262093 18684938754631580544473285)
                ·
                  refine ⟨3503426016493421352088741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18684938754631580544473285 3503426016493421352088741)
                  ·
                    refine ⟨656892378092516503516639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503426016493421352088741 656892378092516503516639)
                    ·
                      rfl

theorem cell23_3837880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_3837880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837880 prefixEnd_3837880 := by exact prefixLift 3837880
  have htrace : WordTrace (prefixWord ++ tailWord_3837880) baseStart_3837880 baseEnd_3837880 := by
    simpa [prefixWord, tailWord_3837880, baseEnd_3837880] using wordTrace_append hprefix tailTrace_3837880
  have hstable : (prefixWord ++ tailWord_3837880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837880).length < 2 ^ (prefixWord ++ tailWord_3837880).sum := by decide
  have hdescent : baseEnd_3837880 < baseStart_3837880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837881 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3837881 : Nat := 118140960795 + 3837881 * 2 ^ 59
def prefixEnd_3837881 : Nat := 4983230072969 + 3 ^ 40 * 3837881 * 2
def baseEnd_3837881 : Nat := 1970677647758204006637413

theorem tailTrace_3837881 : CollatzResearch.WordTrace tailWord_3837881 prefixEnd_3837881 1970677647758204006637413 := by
  unfold tailWord_3837881
  simp only [CollatzResearch.WordTrace]
  refine ⟨139979019809020069736241497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93319346539346713157494331 139979019809020069736241497)
  ·
    refine ⟨104984264856765052302181123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139979019809020069736241497 104984264856765052302181123)
    ·
      refine ⟨157476397285147578453271685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104984264856765052302181123 157476397285147578453271685)
      ·
        refine ⟨29526824490965170959988441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157476397285147578453271685 29526824490965170959988441)
        ·
          refine ⟨22145118368223878219991331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29526824490965170959988441 22145118368223878219991331)
          ·
            refine ⟨33217677552335817329986997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22145118368223878219991331 33217677552335817329986997)
            ·
              refine ⟨3114157270531482874686281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33217677552335817329986997 3114157270531482874686281)
              ·
                refine ⟨2335617952898612156014711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3114157270531482874686281 2335617952898612156014711)
                ·
                  refine ⟨3503426929347918234022067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335617952898612156014711 3503426929347918234022067)
                  ·
                    refine ⟨5255140394021877351033101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3503426929347918234022067 5255140394021877351033101)
                    ·
                      refine ⟨1970677647758204006637413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255140394021877351033101 1970677647758204006637413)
                      ·
                        rfl

theorem cell23_3837881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3837881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837881 prefixEnd_3837881 := by exact prefixLift 3837881
  have htrace : WordTrace (prefixWord ++ tailWord_3837881) baseStart_3837881 baseEnd_3837881 := by
    simpa [prefixWord, tailWord_3837881, baseEnd_3837881] using wordTrace_append hprefix tailTrace_3837881
  have hstable : (prefixWord ++ tailWord_3837881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837881).length < 2 ^ (prefixWord ++ tailWord_3837881).sum := by decide
  have hdescent : baseEnd_3837881 < baseStart_3837881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837883 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_3837883 : Nat := 118140960795 + 3837883 * 2 ^ 59
def prefixEnd_3837883 : Nat := 4983230072969 + 3 ^ 40 * 3837883 * 2
def baseEnd_3837883 : Nat := 1970678674719512998812403

theorem tailTrace_3837883 : CollatzResearch.WordTrace tailWord_3837883 prefixEnd_3837883 1970678674719512998812403 := by
  unfold tailWord_3837883
  simp only [CollatzResearch.WordTrace]
  refine ⟨139979092755012824077814303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93319395170008549385209535 139979092755012824077814303)
  ·
    refine ⟨209968639132519236116721455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139979092755012824077814303 209968639132519236116721455)
    ·
      refine ⟨314952958698778854175082183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209968639132519236116721455 314952958698778854175082183)
      ·
        refine ⟨472429438048168281262623275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314952958698778854175082183 472429438048168281262623275)
        ·
          refine ⟨708644157072252421893934913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472429438048168281262623275 708644157072252421893934913)
          ·
            refine ⟨531483117804189316420451185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708644157072252421893934913 531483117804189316420451185)
            ·
              refine ⟨398612338353141987315338389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531483117804189316420451185 398612338353141987315338389)
              ·
                refine ⟨18684953360303530655406487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 398612338353141987315338389 18684953360303530655406487)
                ·
                  refine ⟨28027430040455295983109731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18684953360303530655406487 28027430040455295983109731)
                  ·
                    refine ⟨42041145060682943974664597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28027430040455295983109731 42041145060682943974664597)
                    ·
                      refine ⟨1970678674719512998812403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42041145060682943974664597 1970678674719512998812403)
                      ·
                        rfl

theorem cell23_3837883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_3837883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837883 prefixEnd_3837883 := by exact prefixLift 3837883
  have htrace : WordTrace (prefixWord ++ tailWord_3837883) baseStart_3837883 baseEnd_3837883 := by
    simpa [prefixWord, tailWord_3837883, baseEnd_3837883] using wordTrace_append hprefix tailTrace_3837883
  have hstable : (prefixWord ++ tailWord_3837883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837883).length < 2 ^ (prefixWord ++ tailWord_3837883).sum := by decide
  have hdescent : baseEnd_3837883 < baseStart_3837883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837900 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3837900 : Nat := 118140960795 + 3837900 * 2 ^ 59
def prefixEnd_3837900 : Nat := 4983230072969 + 3 ^ 40 * 3837900 * 2
def baseEnd_3837900 : Nat := 1970687403890639432299825

theorem tailTrace_3837900 : CollatzResearch.WordTrace tailWord_3837900 prefixEnd_3837900 1970687403890639432299825 := by
  unfold tailWord_3837900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989856397975617990591577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93319808530634157320788769 69989856397975617990591577)
  ·
    refine ⟨52492392298481713492943683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69989856397975617990591577 52492392298481713492943683)
    ·
      refine ⟨78738588447722570239415525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52492392298481713492943683 78738588447722570239415525)
      ·
        refine ⟨14763485333947981919890411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78738588447722570239415525 14763485333947981919890411)
        ·
          refine ⟨22145228000921972879835617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14763485333947981919890411 22145228000921972879835617)
          ·
            refine ⟨16608921000691479659876713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22145228000921972879835617 16608921000691479659876713)
            ·
              refine ⟨12456690750518609744907535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16608921000691479659876713 12456690750518609744907535)
              ·
                refine ⟨18685036125777914617361303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456690750518609744907535 18685036125777914617361303)
                ·
                  refine ⟨28027554188666871926041955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18685036125777914617361303 28027554188666871926041955)
                  ·
                    refine ⟨42041331283000307889062933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28027554188666871926041955 42041331283000307889062933)
                    ·
                      refine ⟨1970687403890639432299825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42041331283000307889062933 1970687403890639432299825)
                      ·
                        rfl

theorem cell23_3837900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3837900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837900 prefixEnd_3837900 := by exact prefixLift 3837900
  have htrace : WordTrace (prefixWord ++ tailWord_3837900) baseStart_3837900 baseEnd_3837900 := by
    simpa [prefixWord, tailWord_3837900, baseEnd_3837900] using wordTrace_append hprefix tailTrace_3837900
  have hstable : (prefixWord ++ tailWord_3837900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837900).length < 2 ^ (prefixWord ++ tailWord_3837900).sum := by decide
  have hdescent : baseEnd_3837900 < baseStart_3837900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837924 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_3837924 : Nat := 118140960795 + 3837924 * 2 ^ 59
def prefixEnd_3837924 : Nat := 4983230072969 + 3 ^ 40 * 3837924 * 2
def baseEnd_3837924 : Nat := 1970699727426347338399715

theorem tailTrace_3837924 : CollatzResearch.WordTrace tailWord_3837924 prefixEnd_3837924 1970699727426347338399715 := by
  unfold tailWord_3837924
  simp only [CollatzResearch.WordTrace]
  refine ⟨69990294073932144040028413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93320392098576192053371217 69990294073932144040028413)
  ·
    refine ⟨26246360277724554015010655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69990294073932144040028413 26246360277724554015010655)
    ·
      refine ⟨39369540416586831022515983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26246360277724554015010655 39369540416586831022515983)
      ·
        refine ⟨59054310624880246533773975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39369540416586831022515983 59054310624880246533773975)
        ·
          refine ⟨88581465937320369800660963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59054310624880246533773975 88581465937320369800660963)
          ·
            refine ⟨132872198905980554700991445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88581465937320369800660963 132872198905980554700991445)
            ·
              refine ⟨3114192161858919250804487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132872198905980554700991445 3114192161858919250804487)
              ·
                refine ⟨4671288242788378876206731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114192161858919250804487 4671288242788378876206731)
                ·
                  refine ⟨7006932364182568314310097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671288242788378876206731 7006932364182568314310097)
                  ·
                    refine ⟨5255199273136926235732573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006932364182568314310097 5255199273136926235732573)
                    ·
                      refine ⟨1970699727426347338399715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255199273136926235732573 1970699727426347338399715)
                      ·
                        rfl

theorem cell23_3837924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_3837924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837924 prefixEnd_3837924 := by exact prefixLift 3837924
  have htrace : WordTrace (prefixWord ++ tailWord_3837924) baseStart_3837924 baseEnd_3837924 := by
    simpa [prefixWord, tailWord_3837924, baseEnd_3837924] using wordTrace_append hprefix tailTrace_3837924
  have hstable : (prefixWord ++ tailWord_3837924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837924).length < 2 ^ (prefixWord ++ tailWord_3837924).sum := by decide
  have hdescent : baseEnd_3837924 < baseStart_3837924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837947 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 3, 3, 2]
def baseStart_3837947 : Nat := 118140960795 + 3837947 * 2 ^ 59
def prefixEnd_3837947 : Nat := 4983230072969 + 3 ^ 40 * 3837947 * 2
def baseEnd_3837947 : Nat := 1970711537481400748412109

theorem tailTrace_3837947 : CollatzResearch.WordTrace tailWord_3837947 prefixEnd_3837947 1970711537481400748412109 := by
  unfold tailWord_3837947
  simp only [CollatzResearch.WordTrace]
  refine ⟨139981427026780963008144095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93320951351187308672096063 139981427026780963008144095)
  ·
    refine ⟨209972140540171444512216143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139981427026780963008144095 209972140540171444512216143)
    ·
      refine ⟨314958210810257166768324215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209972140540171444512216143 314958210810257166768324215)
      ·
        refine ⟨472437316215385750152486323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314958210810257166768324215 472437316215385750152486323)
        ·
          refine ⟨708655974323078625228729485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472437316215385750152486323 708655974323078625228729485)
          ·
            refine ⟨265745990371154484460773557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708655974323078625228729485 265745990371154484460773557)
            ·
              refine ⟨24913686597295732918197521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265745990371154484460773557 24913686597295732918197521)
              ·
                refine ⟨18685264947971799688648141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24913686597295732918197521 18685264947971799688648141)
                ·
                  refine ⟨7006974355489424883243053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18685264947971799688648141 7006974355489424883243053)
                  ·
                    refine ⟨2627615383308534331216145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7006974355489424883243053 2627615383308534331216145)
                    ·
                      refine ⟨1970711537481400748412109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627615383308534331216145 1970711537481400748412109)
                      ·
                        rfl

theorem cell23_3837947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3, 2].length) (baseStart_3837947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837947 prefixEnd_3837947 := by exact prefixLift 3837947
  have htrace : WordTrace (prefixWord ++ tailWord_3837947) baseStart_3837947 baseEnd_3837947 := by
    simpa [prefixWord, tailWord_3837947, baseEnd_3837947] using wordTrace_append hprefix tailTrace_3837947
  have hstable : (prefixWord ++ tailWord_3837947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837947).length < 2 ^ (prefixWord ++ tailWord_3837947).sum := by decide
  have hdescent : baseEnd_3837947 < baseStart_3837947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837960 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3837960 : Nat := 118140960795 + 3837960 * 2 ^ 59
def prefixEnd_3837960 : Nat := 4983230072969 + 3 ^ 40 * 3837960 * 2
def baseEnd_3837960 : Nat := 1970718212729909197549549

theorem tailTrace_3837960 : CollatzResearch.WordTrace tailWord_3837960 prefixEnd_3837960 1970718212729909197549549 := by
  unfold tailWord_3837960
  simp only [CollatzResearch.WordTrace]
  refine ⟨69990950587866933114183667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93321267450489244152244889 69990950587866933114183667)
  ·
    refine ⟨104986425881800399671275501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69990950587866933114183667 104986425881800399671275501)
    ·
      refine ⟨39369909705675149876728313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104986425881800399671275501 39369909705675149876728313)
      ·
        refine ⟨29527432279256362407546235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39369909705675149876728313 29527432279256362407546235)
        ·
          refine ⟨44291148418884543611319353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29527432279256362407546235 44291148418884543611319353)
          ·
            refine ⟨33218361314163407708489515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44291148418884543611319353 33218361314163407708489515)
            ·
              refine ⟨49827541971245111562734273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33218361314163407708489515 49827541971245111562734273)
              ·
                refine ⟨37370656478433833672050705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49827541971245111562734273 37370656478433833672050705)
                ·
                  refine ⟨28027992358825375254038029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37370656478433833672050705 28027992358825375254038029)
                  ·
                    refine ⟨10510497134559515720264261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28027992358825375254038029 10510497134559515720264261)
                    ·
                      refine ⟨1970718212729909197549549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10510497134559515720264261 1970718212729909197549549)
                      ·
                        rfl

theorem cell23_3837960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3837960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837960 prefixEnd_3837960 := by exact prefixLift 3837960
  have htrace : WordTrace (prefixWord ++ tailWord_3837960) baseStart_3837960 baseEnd_3837960 := by
    simpa [prefixWord, tailWord_3837960, baseEnd_3837960] using wordTrace_append hprefix tailTrace_3837960
  have hstable : (prefixWord ++ tailWord_3837960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837960).length < 2 ^ (prefixWord ++ tailWord_3837960).sum := by decide
  have hdescent : baseEnd_3837960 < baseStart_3837960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837964 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_3837964 : Nat := 118140960795 + 3837964 * 2 ^ 59
def prefixEnd_3837964 : Nat := 4983230072969 + 3 ^ 40 * 3837964 * 2
def baseEnd_3837964 : Nat := 1970720266652527181899531

theorem tailTrace_3837964 : CollatzResearch.WordTrace tailWord_3837964 prefixEnd_3837964 1970720266652527181899531 := by
  unfold tailWord_3837964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991023533859687455756473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93321364711812916607675297 69991023533859687455756473)
  ·
    refine ⟨52493267650394765591817355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69991023533859687455756473 52493267650394765591817355)
    ·
      refine ⟨78739901475592148387726033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52493267650394765591817355 78739901475592148387726033)
      ·
        refine ⟨59054926106694111290794525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78739901475592148387726033 59054926106694111290794525)
        ·
          refine ⟨22145597290010291734047947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59054926106694111290794525 22145597290010291734047947)
          ·
            refine ⟨33218395935015437601071921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22145597290010291734047947 33218395935015437601071921)
            ·
              refine ⟨24913796951261578200803941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33218395935015437601071921 24913796951261578200803941)
              ·
                refine ⟨4671336928361545912650739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24913796951261578200803941 4671336928361545912650739)
                ·
                  refine ⟨7007005392542318868976109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671336928361545912650739 7007005392542318868976109)
                  ·
                    refine ⟨2627627022203369575866041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7007005392542318868976109 2627627022203369575866041)
                    ·
                      refine ⟨1970720266652527181899531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627627022203369575866041 1970720266652527181899531)
                      ·
                        rfl

theorem cell23_3837964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_3837964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837964 prefixEnd_3837964 := by exact prefixLift 3837964
  have htrace : WordTrace (prefixWord ++ tailWord_3837964) baseStart_3837964 baseEnd_3837964 := by
    simpa [prefixWord, tailWord_3837964, baseEnd_3837964] using wordTrace_append hprefix tailTrace_3837964
  have hstable : (prefixWord ++ tailWord_3837964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837964).length < 2 ^ (prefixWord ++ tailWord_3837964).sum := by decide
  have hdescent : baseEnd_3837964 < baseStart_3837964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837972 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3837972 : Nat := 118140960795 + 3837972 * 2 ^ 59
def prefixEnd_3837972 : Nat := 4983230072969 + 3 ^ 40 * 3837972 * 2
def baseEnd_3837972 : Nat := 1970724374497763150599495

theorem tailTrace_3837972 : CollatzResearch.WordTrace tailWord_3837972 prefixEnd_3837972 1970724374497763150599495 := by
  unfold tailWord_3837972
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991169425845196138902085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93321559234460261518536113 69991169425845196138902085)
  ·
    refine ⟨13123344267345974276044141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69991169425845196138902085 13123344267345974276044141)
    ·
      refine ⟨4921254100254740353516553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13123344267345974276044141 4921254100254740353516553)
      ·
        refine ⟨3690940575191055265137415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4921254100254740353516553 3690940575191055265137415)
        ·
          refine ⟨5536410862786582897706123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690940575191055265137415 5536410862786582897706123)
          ·
            refine ⟨8304616294179874346559185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536410862786582897706123 8304616294179874346559185)
            ·
              refine ⟨6228462220634905759919389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304616294179874346559185 6228462220634905759919389)
              ·
                refine ⟨2335673332738089659969771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228462220634905759919389 2335673332738089659969771)
                ·
                  refine ⟨3503509999107134489954657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335673332738089659969771 3503509999107134489954657)
                  ·
                    refine ⟨2627632499330350867465993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503509999107134489954657 2627632499330350867465993)
                    ·
                      refine ⟨1970724374497763150599495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627632499330350867465993 1970724374497763150599495)
                      ·
                        rfl

theorem cell23_3837972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3837972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837972 prefixEnd_3837972 := by exact prefixLift 3837972
  have htrace : WordTrace (prefixWord ++ tailWord_3837972) baseStart_3837972 baseEnd_3837972 := by
    simpa [prefixWord, tailWord_3837972, baseEnd_3837972] using wordTrace_append hprefix tailTrace_3837972
  have hstable : (prefixWord ++ tailWord_3837972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837972).length < 2 ^ (prefixWord ++ tailWord_3837972).sum := by decide
  have hdescent : baseEnd_3837972 < baseStart_3837972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837981 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_3837981 : Nat := 118140960795 + 3837981 * 2 ^ 59
def prefixEnd_3837981 : Nat := 4983230072969 + 3 ^ 40 * 3837981 * 2
def baseEnd_3837981 : Nat := 1970728995823653615386953

theorem tailTrace_3837981 : CollatzResearch.WordTrace tailWord_3837981 prefixEnd_3837981 1970728995823653615386953 := by
  unfold tailWord_3837981
  simp only [CollatzResearch.WordTrace]
  refine ⟨139982667108657786814881797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93321778072438524543254531 139982667108657786814881797)
  ·
    refine ⟨26246750082873335027790337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139982667108657786814881797 26246750082873335027790337)
    ·
      refine ⟨19685062562155001270842753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26246750082873335027790337 19685062562155001270842753)
      ·
        refine ⟨14763796921616250953132065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19685062562155001270842753 14763796921616250953132065)
        ·
          refine ⟨11072847691212188214849049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14763796921616250953132065 11072847691212188214849049)
          ·
            refine ⟨8304635768409141161136787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11072847691212188214849049 8304635768409141161136787)
            ·
              refine ⟨12456953652613711741705181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304635768409141161136787 12456953652613711741705181)
              ·
                refine ⟨4671357619730141903139443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12456953652613711741705181 4671357619730141903139443)
                ·
                  refine ⟨7007036429595212854709165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671357619730141903139443 7007036429595212854709165)
                  ·
                    refine ⟨2627638661098204820515937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7007036429595212854709165 2627638661098204820515937)
                    ·
                      refine ⟨1970728995823653615386953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627638661098204820515937 1970728995823653615386953)
                      ·
                        rfl

theorem cell23_3837981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_3837981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837981 prefixEnd_3837981 := by exact prefixLift 3837981
  have htrace : WordTrace (prefixWord ++ tailWord_3837981) baseStart_3837981 baseEnd_3837981 := by
    simpa [prefixWord, tailWord_3837981, baseEnd_3837981] using wordTrace_append hprefix tailTrace_3837981
  have hstable : (prefixWord ++ tailWord_3837981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837981).length < 2 ^ (prefixWord ++ tailWord_3837981).sum := by decide
  have hdescent : baseEnd_3837981 < baseStart_3837981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3837988 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3837988 : Nat := 118140960795 + 3837988 * 2 ^ 59
def prefixEnd_3837988 : Nat := 4983230072969 + 3 ^ 40 * 3837988 * 2
def baseEnd_3837988 : Nat := 1970732590188235087999421

theorem tailTrace_3837988 : CollatzResearch.WordTrace tailWord_3837988 prefixEnd_3837988 1970732590188235087999421 := by
  unfold tailWord_3837988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991461209816213505193309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93321948279754951340257745 69991461209816213505193309)
  ·
    refine ⟨26246797953681080064447491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69991461209816213505193309 26246797953681080064447491)
    ·
      refine ⟨39370196930521620096671237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26246797953681080064447491 39370196930521620096671237)
      ·
        refine ⟨7381911924472803768125857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39370196930521620096671237 7381911924472803768125857)
        ·
          refine ⟨5536433943354602826094393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7381911924472803768125857 5536433943354602826094393)
          ·
            refine ⟨4152325457515952119570795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536433943354602826094393 4152325457515952119570795)
            ·
              refine ⟨6228488186273928179356193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152325457515952119570795 6228488186273928179356193)
              ·
                refine ⟨4671366139705446134517145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228488186273928179356193 4671366139705446134517145)
                ·
                  refine ⟨3503524604779084600887859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671366139705446134517145 3503524604779084600887859)
                  ·
                    refine ⟨5255286907168626901331789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3503524604779084600887859 5255286907168626901331789)
                    ·
                      refine ⟨1970732590188235087999421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255286907168626901331789 1970732590188235087999421)
                      ·
                        rfl

theorem cell23_3837988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3837988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3837988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3837988 prefixEnd_3837988 := by exact prefixLift 3837988
  have htrace : WordTrace (prefixWord ++ tailWord_3837988) baseStart_3837988 baseEnd_3837988 := by
    simpa [prefixWord, tailWord_3837988, baseEnd_3837988] using wordTrace_append hprefix tailTrace_3837988
  have hstable : (prefixWord ++ tailWord_3837988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3837988).length < 2 ^ (prefixWord ++ tailWord_3837988).sum := by decide
  have hdescent : baseEnd_3837988 < baseStart_3837988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3837988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838000 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 7]
def baseStart_3838000 : Nat := 118140960795 + 3838000 * 2 ^ 59
def prefixEnd_3838000 : Nat := 4983230072969 + 3 ^ 40 * 3838000 * 2
def baseEnd_3838000 : Nat := 218970972439565449005485

theorem tailTrace_3838000 : CollatzResearch.WordTrace tailWord_3838000 prefixEnd_3838000 218970972439565449005485 := by
  unfold tailWord_3838000
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991680047794476529911727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93322240063725968706548969 69991680047794476529911727)
  ·
    refine ⟨104987520071691714794867591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69991680047794476529911727 104987520071691714794867591)
    ·
      refine ⟨157481280107537572192301387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104987520071691714794867591 157481280107537572192301387)
      ·
        refine ⟨236221920161306358288452081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157481280107537572192301387 236221920161306358288452081)
        ·
          refine ⟨177166440120979768716339061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236221920161306358288452081 177166440120979768716339061)
          ·
            refine ⟨16609353761341853317156787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177166440120979768716339061 16609353761341853317156787)
            ·
              refine ⟨24914030642012779975735181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16609353761341853317156787 24914030642012779975735181)
              ·
                refine ⟨9342761490754792490900693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24914030642012779975735181 9342761490754792490900693)
                ·
                  refine ⟨218970972439565449005485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9342761490754792490900693 218970972439565449005485)
                  ·
                    rfl

theorem cell23_3838000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_3838000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838000 prefixEnd_3838000 := by exact prefixLift 3838000
  have htrace : WordTrace (prefixWord ++ tailWord_3838000) baseStart_3838000 baseEnd_3838000 := by
    simpa [prefixWord, tailWord_3838000, baseEnd_3838000] using wordTrace_append hprefix tailTrace_3838000
  have hstable : (prefixWord ++ tailWord_3838000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838000).length < 2 ^ (prefixWord ++ tailWord_3838000).sum := by decide
  have hdescent : baseEnd_3838000 < baseStart_3838000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838017 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 7]
def baseStart_3838017 : Nat := 118140960795 + 3838017 * 2 ^ 59
def prefixEnd_3838017 : Nat := 4983230072969 + 3 ^ 40 * 3838017 * 2
def baseEnd_3838017 : Nat := 218971942347468386059643

theorem tailTrace_3838017 : CollatzResearch.WordTrace tailWord_3838017 prefixEnd_3838017 218971942347468386059643 := by
  unfold tailWord_3838017
  simp only [CollatzResearch.WordTrace]
  refine ⟨139983980136527364963192305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93322653424351576642128203 139983980136527364963192305)
  ·
    refine ⟨104987985102395523722394229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139983980136527364963192305 104987985102395523722394229)
    ·
      refine ⟨9842623603349580348974459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104987985102395523722394229 9842623603349580348974459)
      ·
        refine ⟨14763935405024370523461689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9842623603349580348974459 14763935405024370523461689)
        ·
          refine ⟨11072951553768277892596267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14763935405024370523461689 11072951553768277892596267)
          ·
            refine ⟨16609427330652416838894401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072951553768277892596267 16609427330652416838894401)
            ·
              refine ⟨12457070497989312629170801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16609427330652416838894401 12457070497989312629170801)
              ·
                refine ⟨9342802873491984471878101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12457070497989312629170801 9342802873491984471878101)
                ·
                  refine ⟨218971942347468386059643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9342802873491984471878101 218971942347468386059643)
                  ·
                    rfl

theorem cell23_3838017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_3838017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838017 prefixEnd_3838017 := by exact prefixLift 3838017
  have htrace : WordTrace (prefixWord ++ tailWord_3838017) baseStart_3838017 baseEnd_3838017 := by
    simpa [prefixWord, tailWord_3838017, baseEnd_3838017] using wordTrace_append hprefix tailTrace_3838017
  have hstable : (prefixWord ++ tailWord_3838017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838017).length < 2 ^ (prefixWord ++ tailWord_3838017).sum := by decide
  have hdescent : baseEnd_3838017 < baseStart_3838017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838080 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_3838080 : Nat := 118140960795 + 3838080 * 2 ^ 59
def prefixEnd_3838080 : Nat := 4983230072969 + 3 ^ 40 * 3838080 * 2
def baseEnd_3838080 : Nat := 1970779830408448728048997

theorem tailTrace_3838080 : CollatzResearch.WordTrace tailWord_3838080 prefixEnd_3838080 1970779830408448728048997 := by
  unfold tailWord_3838080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69993138967649563361367847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93324185290199417815157129 69993138967649563361367847)
  ·
    refine ⟨104989708451474345042051771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69993138967649563361367847 104989708451474345042051771)
    ·
      refine ⟨157484562677211517563077657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104989708451474345042051771 157484562677211517563077657)
      ·
        refine ⟨118113422007908638172308243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157484562677211517563077657 118113422007908638172308243)
        ·
          refine ⟨177170133011862957258462365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118113422007908638172308243 177170133011862957258462365)
          ·
            refine ⟨66438799879448608971923387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177170133011862957258462365 66438799879448608971923387)
            ·
              refine ⟨99658199819172913457885081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66438799879448608971923387 99658199819172913457885081)
              ·
                refine ⟨74743649864379685093413811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99658199819172913457885081 74743649864379685093413811)
                ·
                  refine ⟨112115474796569527640120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74743649864379685093413811 112115474796569527640120717)
                  ·
                    refine ⟨42043303048713572865045269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112115474796569527640120717 42043303048713572865045269)
                    ·
                      refine ⟨1970779830408448728048997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42043303048713572865045269 1970779830408448728048997)
                      ·
                        rfl

theorem cell23_3838080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_3838080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838080 prefixEnd_3838080 := by exact prefixLift 3838080
  have htrace : WordTrace (prefixWord ++ tailWord_3838080) baseStart_3838080 baseEnd_3838080 := by
    simpa [prefixWord, tailWord_3838080, baseEnd_3838080] using wordTrace_append hprefix tailTrace_3838080
  have hstable : (prefixWord ++ tailWord_3838080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838080).length < 2 ^ (prefixWord ++ tailWord_3838080).sum := by decide
  have hdescent : baseEnd_3838080 < baseStart_3838080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838084 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3838084 : Nat := 118140960795 + 3838084 * 2 ^ 59
def prefixEnd_3838084 : Nat := 4983230072969 + 3 ^ 40 * 3838084 * 2
def baseEnd_3838084 : Nat := 1970781884331066712398979

theorem tailTrace_3838084 : CollatzResearch.WordTrace tailWord_3838084 prefixEnd_3838084 1970781884331066712398979 := by
  unfold tailWord_3838084
  simp only [CollatzResearch.WordTrace]
  refine ⟨69993211913642317702940653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93324282551523090270587537 69993211913642317702940653)
  ·
    refine ⟨26247454467615869138602745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69993211913642317702940653 26247454467615869138602745)
    ·
      refine ⟨19685590850711901853952059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26247454467615869138602745 19685590850711901853952059)
      ·
        refine ⟨29528386276067852780928089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19685590850711901853952059 29528386276067852780928089)
        ·
          refine ⟨22146289707050889585696067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29528386276067852780928089 22146289707050889585696067)
          ·
            refine ⟨33219434560576334378544101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22146289707050889585696067 33219434560576334378544101)
            ·
              refine ⟨6228643980108062695977019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33219434560576334378544101 6228643980108062695977019)
              ·
                refine ⟨9342965970162094043965529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228643980108062695977019 9342965970162094043965529)
                ·
                  refine ⟨7007224477621570532974147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342965970162094043965529 7007224477621570532974147)
                  ·
                    refine ⟨10510836716432355799461221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007224477621570532974147 10510836716432355799461221)
                    ·
                      refine ⟨1970781884331066712398979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10510836716432355799461221 1970781884331066712398979)
                      ·
                        rfl

theorem cell23_3838084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3838084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838084 prefixEnd_3838084 := by exact prefixLift 3838084
  have htrace : WordTrace (prefixWord ++ tailWord_3838084) baseStart_3838084 baseEnd_3838084 := by
    simpa [prefixWord, tailWord_3838084, baseEnd_3838084] using wordTrace_append hprefix tailTrace_3838084
  have hstable : (prefixWord ++ tailWord_3838084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838084).length < 2 ^ (prefixWord ++ tailWord_3838084).sum := by decide
  have hdescent : baseEnd_3838084 < baseStart_3838084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838087 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_3838087 : Nat := 118140960795 + 3838087 * 2 ^ 59
def prefixEnd_3838087 : Nat := 4983230072969 + 3 ^ 40 * 3838087 * 2
def baseEnd_3838087 : Nat := 1970783424773030200661465

theorem tailTrace_3838087 : CollatzResearch.WordTrace tailWord_3838087 prefixEnd_3838087 1970783424773030200661465 := by
  unfold tailWord_3838087
  simp only [CollatzResearch.WordTrace]
  refine ⟨139986533246273766918240515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93324355497515844612160343 139986533246273766918240515)
  ·
    refine ⟨209979799869410650377360773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139986533246273766918240515 209979799869410650377360773)
    ·
      refine ⟨39371212475514496945755145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209979799869410650377360773 39371212475514496945755145)
      ·
        refine ⟨29528409356635872709316359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39371212475514496945755145 29528409356635872709316359)
        ·
          refine ⟨44292614034953809063974539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29528409356635872709316359 44292614034953809063974539)
          ·
            refine ⟨66438921052430713595961809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44292614034953809063974539 66438921052430713595961809)
            ·
              refine ⟨49829190789323035196971357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66438921052430713595961809 49829190789323035196971357)
              ·
                refine ⟨18685946545996138198864259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49829190789323035196971357 18685946545996138198864259)
                ·
                  refine ⟨28028919818994207298296389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18685946545996138198864259 28028919818994207298296389)
                  ·
                    refine ⟨5255422466061413868430573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28028919818994207298296389 5255422466061413868430573)
                    ·
                      refine ⟨1970783424773030200661465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255422466061413868430573 1970783424773030200661465)
                      ·
                        rfl

theorem cell23_3838087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_3838087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838087 prefixEnd_3838087 := by exact prefixLift 3838087
  have htrace : WordTrace (prefixWord ++ tailWord_3838087) baseStart_3838087 baseEnd_3838087 := by
    simpa [prefixWord, tailWord_3838087, baseEnd_3838087] using wordTrace_append hprefix tailTrace_3838087
  have hstable : (prefixWord ++ tailWord_3838087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838087).length < 2 ^ (prefixWord ++ tailWord_3838087).sum := by decide
  have hdescent : baseEnd_3838087 < baseStart_3838087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838102 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3838102 : Nat := 118140960795 + 3838102 * 2 ^ 59
def prefixEnd_3838102 : Nat := 4983230072969 + 3 ^ 40 * 3838102 * 2
def baseEnd_3838102 : Nat := 218976791886983071330433

theorem tailTrace_3838102 : CollatzResearch.WordTrace tailWord_3838102 prefixEnd_3838102 218976791886983071330433 := by
  unfold tailWord_3838102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749192521326214030002285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93324720227479616320024373 8749192521326214030002285)
  ·
    refine ⟨3280947195497330261250857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8749192521326214030002285 3280947195497330261250857)
    ·
      refine ⟨2460710396622997695938143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280947195497330261250857 2460710396622997695938143)
      ·
        refine ⟨3691065594934496543907215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460710396622997695938143 3691065594934496543907215)
        ·
          refine ⟨5536598392401744815860823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691065594934496543907215 5536598392401744815860823)
          ·
            refine ⟨8304897588602617223791235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536598392401744815860823 8304897588602617223791235)
            ·
              refine ⟨12457346382903925835686853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304897588602617223791235 12457346382903925835686853)
              ·
                refine ⟨2335752446794486094191285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12457346382903925835686853 2335752446794486094191285)
                ·
                  refine ⟨218976791886983071330433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2335752446794486094191285 218976791886983071330433)
                  ·
                    rfl

theorem cell23_3838102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3838102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838102 prefixEnd_3838102 := by exact prefixLift 3838102
  have htrace : WordTrace (prefixWord ++ tailWord_3838102) baseStart_3838102 baseEnd_3838102 := by
    simpa [prefixWord, tailWord_3838102, baseEnd_3838102] using wordTrace_append hprefix tailTrace_3838102
  have hstable : (prefixWord ++ tailWord_3838102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838102).length < 2 ^ (prefixWord ++ tailWord_3838102).sum := by decide
  have hdescent : baseEnd_3838102 < baseStart_3838102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838132 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3838132 : Nat := 118140960795 + 3838132 * 2 ^ 59
def prefixEnd_3838132 : Nat := 4983230072969 + 3 ^ 40 * 3838132 * 2
def baseEnd_3838132 : Nat := 656935510467494174866253

theorem tailTrace_3838132 : CollatzResearch.WordTrace tailWord_3838132 prefixEnd_3838132 656935510467494174866253 := by
  unfold tailWord_3838132
  simp only [CollatzResearch.WordTrace]
  refine ⟨69994087265555369801814325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93325449687407159735752433 69994087265555369801814325)
  ·
    refine ⟨6561945681145815918920093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69994087265555369801814325 6561945681145815918920093)
    ·
      refine ⟨2460729630429680969595035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6561945681145815918920093 2460729630429680969595035)
      ·
        refine ⟨3691094445644521454392553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460729630429680969595035 3691094445644521454392553)
        ·
          refine ⟨2768320834233391090794415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3691094445644521454392553 2768320834233391090794415)
          ·
            refine ⟨4152481251350086636191623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768320834233391090794415 4152481251350086636191623)
            ·
              refine ⟨6228721877025129954287435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152481251350086636191623 6228721877025129954287435)
              ·
                refine ⟨9343082815537694931431153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228721877025129954287435 9343082815537694931431153)
                ·
                  refine ⟨7007312111653271198573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343082815537694931431153 7007312111653271198573365)
                  ·
                    refine ⟨656935510467494174866253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7007312111653271198573365 656935510467494174866253)
                    ·
                      rfl

theorem cell23_3838132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3838132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838132 prefixEnd_3838132 := by exact prefixLift 3838132
  have htrace : WordTrace (prefixWord ++ tailWord_3838132) baseStart_3838132 baseEnd_3838132 := by
    simpa [prefixWord, tailWord_3838132, baseEnd_3838132] using wordTrace_append hprefix tailTrace_3838132
  have hstable : (prefixWord ++ tailWord_3838132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838132).length < 2 ^ (prefixWord ++ tailWord_3838132).sum := by decide
  have hdescent : baseEnd_3838132 < baseStart_3838132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838137 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_3838137 : Nat := 118140960795 + 3838137 * 2 ^ 59
def prefixEnd_3838137 : Nat := 4983230072969 + 3 ^ 40 * 3838137 * 2
def baseEnd_3838137 : Nat := 656936366268585001678745

theorem tailTrace_3838137 : CollatzResearch.WordTrace tailWord_3838137 prefixEnd_3838137 656936366268585001678745 := by
  unfold tailWord_3838137
  simp only [CollatzResearch.WordTrace]
  refine ⟨139988356896092625457560665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93325571264061750305040443 139988356896092625457560665)
  ·
    refine ⟨104991267672069469093170499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139988356896092625457560665 104991267672069469093170499)
    ·
      refine ⟨157486901508104203639755749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104991267672069469093170499 157486901508104203639755749)
      ·
        refine ⟨29528794032769538182454203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157486901508104203639755749 29528794032769538182454203)
        ·
          refine ⟨44293191049154307273681305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29528794032769538182454203 44293191049154307273681305)
          ·
            refine ⟨33219893286865730455260979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44293191049154307273681305 33219893286865730455260979)
            ·
              refine ⟨49829839930298595682891469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33219893286865730455260979 49829839930298595682891469)
              ·
                refine ⟨18686189973861973381084301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49829839930298595682891469 18686189973861973381084301)
                ·
                  refine ⟨7007321240198240017906613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18686189973861973381084301 7007321240198240017906613)
                  ·
                    refine ⟨656936366268585001678745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7007321240198240017906613 656936366268585001678745)
                    ·
                      rfl

theorem cell23_3838137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_3838137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838137 prefixEnd_3838137 := by exact prefixLift 3838137
  have htrace : WordTrace (prefixWord ++ tailWord_3838137) baseStart_3838137 baseEnd_3838137 := by
    simpa [prefixWord, tailWord_3838137, baseEnd_3838137] using wordTrace_append hprefix tailTrace_3838137
  have hstable : (prefixWord ++ tailWord_3838137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838137).length < 2 ^ (prefixWord ++ tailWord_3838137).sum := by decide
  have hdescent : baseEnd_3838137 < baseStart_3838137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838145 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3838145 : Nat := 118140960795 + 3838145 * 2 ^ 59
def prefixEnd_3838145 : Nat := 4983230072969 + 3 ^ 40 * 3838145 * 2
def baseEnd_3838145 : Nat := 656937735550330324578733

theorem tailTrace_3838145 : CollatzResearch.WordTrace tailWord_3838145 prefixEnd_3838145 656937735550330324578733 := by
  unfold tailWord_3838145
  simp only [CollatzResearch.WordTrace]
  refine ⟨139988648680063642823851889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93325765786709095215901259 139988648680063642823851889)
  ·
    refine ⟨104991486510047732117888917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139988648680063642823851889 104991486510047732117888917)
    ·
      refine ⟨4921475930158487443026043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104991486510047732117888917 4921475930158487443026043)
      ·
        refine ⟨7382213895237731164539065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921475930158487443026043 7382213895237731164539065)
        ·
          refine ⟨5536660421428298373404299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7382213895237731164539065 5536660421428298373404299)
          ·
            refine ⟨8304990632142447560106449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536660421428298373404299 8304990632142447560106449)
            ·
              refine ⟨6228742974106835670079837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304990632142447560106449 6228742974106835670079837)
              ·
                refine ⟨2335778615290063376279939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228742974106835670079837 2335778615290063376279939)
                ·
                  refine ⟨3503667922935095064419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335778615290063376279939 3503667922935095064419909)
                  ·
                    refine ⟨656937735550330324578733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503667922935095064419909 656937735550330324578733)
                    ·
                      rfl

theorem cell23_3838145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3838145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838145 prefixEnd_3838145 := by exact prefixLift 3838145
  have htrace : WordTrace (prefixWord ++ tailWord_3838145) baseStart_3838145 baseEnd_3838145 := by
    simpa [prefixWord, tailWord_3838145, baseEnd_3838145] using wordTrace_append hprefix tailTrace_3838145
  have hstable : (prefixWord ++ tailWord_3838145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838145).length < 2 ^ (prefixWord ++ tailWord_3838145).sum := by decide
  have hdescent : baseEnd_3838145 < baseStart_3838145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838154 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_3838154 : Nat := 118140960795 + 3838154 * 2 ^ 59
def prefixEnd_3838154 : Nat := 4983230072969 + 3 ^ 40 * 3838154 * 2
def baseEnd_3838154 : Nat := 656939275992293812841219

theorem tailTrace_3838154 : CollatzResearch.WordTrace tailWord_3838154 prefixEnd_3838154 656939275992293812841219 := by
  unfold tailWord_3838154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997244234257759340232379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93325984624687358240619677 34997244234257759340232379)
  ·
    refine ⟨52495866351386639010348569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34997244234257759340232379 52495866351386639010348569)
    ·
      refine ⟨39371899763539979257761427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52495866351386639010348569 39371899763539979257761427)
      ·
        refine ⟨59057849645309968886642141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39371899763539979257761427 59057849645309968886642141)
        ·
          refine ⟨22146693616991238332490803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59057849645309968886642141 22146693616991238332490803)
          ·
            refine ⟨33220040425486857498736205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22146693616991238332490803 33220040425486857498736205)
            ·
              refine ⟨12457515159557571562026077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33220040425486857498736205 12457515159557571562026077)
              ·
                refine ⟨4671568184834089335759779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12457515159557571562026077 4671568184834089335759779)
                ·
                  refine ⟨7007352277251134003639669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671568184834089335759779 7007352277251134003639669)
                  ·
                    refine ⟨656939275992293812841219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7007352277251134003639669 656939275992293812841219)
                    ·
                      rfl

theorem cell23_3838154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_3838154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838154 prefixEnd_3838154 := by exact prefixLift 3838154
  have htrace : WordTrace (prefixWord ++ tailWord_3838154) baseStart_3838154 baseEnd_3838154 := by
    simpa [prefixWord, tailWord_3838154, baseEnd_3838154] using wordTrace_append hprefix tailTrace_3838154
  have hstable : (prefixWord ++ tailWord_3838154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838154).length < 2 ^ (prefixWord ++ tailWord_3838154).sum := by decide
  have hdescent : baseEnd_3838154 < baseStart_3838154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838168 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 1, 1, 3]
def baseStart_3838168 : Nat := 118140960795 + 3838168 * 2 ^ 59
def prefixEnd_3838168 : Nat := 4983230072969 + 3 ^ 40 * 3838168 * 2
def baseEnd_3838168 : Nat := 1970825016706044383748593

theorem tailTrace_3838168 : CollatzResearch.WordTrace tailWord_3838168 prefixEnd_3838168 1970825016706044383748593 := by
  unfold tailWord_3838168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69994743779490158875969579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93326325039320211834626105 69994743779490158875969579)
  ·
    refine ⟨104992115669235238313954369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69994743779490158875969579 104992115669235238313954369)
    ·
      refine ⟨78744086751926428735465777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104992115669235238313954369 78744086751926428735465777)
      ·
        refine ⟨59058065063944821551599333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78744086751926428735465777 59058065063944821551599333)
        ·
          refine ⟨11073387199489654040924875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59058065063944821551599333 11073387199489654040924875)
          ·
            refine ⟨16610080799234481061387313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11073387199489654040924875 16610080799234481061387313)
            ·
              refine ⟨12457560599425860796040485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16610080799234481061387313 12457560599425860796040485)
              ·
                refine ⟨2335792612392348899257591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12457560599425860796040485 2335792612392348899257591)
                ·
                  refine ⟨3503688918588523348886387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335792612392348899257591 3503688918588523348886387)
                  ·
                    refine ⟨5255533377882785023329581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3503688918588523348886387 5255533377882785023329581)
                    ·
                      refine ⟨1970825016706044383748593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255533377882785023329581 1970825016706044383748593)
                      ·
                        rfl

theorem cell23_3838168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_3838168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838168 prefixEnd_3838168 := by exact prefixLift 3838168
  have htrace : WordTrace (prefixWord ++ tailWord_3838168) baseStart_3838168 baseEnd_3838168 := by
    simpa [prefixWord, tailWord_3838168, baseEnd_3838168] using wordTrace_append hprefix tailTrace_3838168
  have hstable : (prefixWord ++ tailWord_3838168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838168).length < 2 ^ (prefixWord ++ tailWord_3838168).sum := by decide
  have hdescent : baseEnd_3838168 < baseStart_3838168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838184 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_3838184 : Nat := 118140960795 + 3838184 * 2 ^ 59
def prefixEnd_3838184 : Nat := 4983230072969 + 3 ^ 40 * 3838184 * 2
def baseEnd_3838184 : Nat := 656944410798838773716173

theorem tailTrace_3838184 : CollatzResearch.WordTrace tailWord_3838184 prefixEnd_3838184 656944410798838773716173 := by
  unfold tailWord_3838184
  simp only [CollatzResearch.WordTrace]
  refine ⟨69995035563461176242260803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93326714084614901656347737 69995035563461176242260803)
  ·
    refine ⟨104992553345191764363391205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69995035563461176242260803 104992553345191764363391205)
    ·
      refine ⟨19686103752223455818135851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104992553345191764363391205 19686103752223455818135851)
      ·
        refine ⟨29529155628335183727203777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19686103752223455818135851 29529155628335183727203777)
        ·
          refine ⟨22146866721251387795402833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29529155628335183727203777 22146866721251387795402833)
          ·
            refine ⟨16610150040938540846552125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22146866721251387795402833 16610150040938540846552125)
            ·
              refine ⟨6228806265351952817457047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16610150040938540846552125 6228806265351952817457047)
              ·
                refine ⟨9343209398027929226185571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228806265351952817457047 9343209398027929226185571)
                ·
                  refine ⟨14014814097041893839278357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343209398027929226185571 14014814097041893839278357)
                  ·
                    refine ⟨656944410798838773716173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14014814097041893839278357 656944410798838773716173)
                    ·
                      rfl

theorem cell23_3838184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_3838184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838184 prefixEnd_3838184 := by exact prefixLift 3838184
  have htrace : WordTrace (prefixWord ++ tailWord_3838184) baseStart_3838184 baseEnd_3838184 := by
    simpa [prefixWord, tailWord_3838184, baseEnd_3838184] using wordTrace_append hprefix tailTrace_3838184
  have hstable : (prefixWord ++ tailWord_3838184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838184).length < 2 ^ (prefixWord ++ tailWord_3838184).sum := by decide
  have hdescent : baseEnd_3838184 < baseStart_3838184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838187 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_3838187 : Nat := 118140960795 + 3838187 * 2 ^ 59
def prefixEnd_3838187 : Nat := 4983230072969 + 3 ^ 40 * 3838187 * 2
def baseEnd_3838187 : Nat := 1970834772838479809411005

theorem tailTrace_3838187 : CollatzResearch.WordTrace tailWord_3838187 prefixEnd_3838187 1970834772838479809411005 := by
  unfold tailWord_3838187
  simp only [CollatzResearch.WordTrace]
  refine ⟨139990180545911483996880815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93326787030607655997920543 139990180545911483996880815)
  ·
    refine ⟨209985270818867225995321223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139990180545911483996880815 209985270818867225995321223)
    ·
      refine ⟨314977906228300838992981835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209985270818867225995321223 314977906228300838992981835)
      ·
        refine ⟨472466859342451258489472753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314977906228300838992981835 472466859342451258489472753)
        ·
          refine ⟨354350144506838443867104565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472466859342451258489472753 354350144506838443867104565)
          ·
            refine ⟨33220326047516104112541053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354350144506838443867104565 33220326047516104112541053)
            ·
              refine ⟨12457622267818539042202895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33220326047516104112541053 12457622267818539042202895)
              ·
                refine ⟨18686433401727808563304343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12457622267818539042202895 18686433401727808563304343)
                ·
                  refine ⟨28029650102591712844956515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18686433401727808563304343 28029650102591712844956515)
                  ·
                    refine ⟨42044475153887569267434773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28029650102591712844956515 42044475153887569267434773)
                    ·
                      refine ⟨1970834772838479809411005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42044475153887569267434773 1970834772838479809411005)
                      ·
                        rfl

theorem cell23_3838187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_3838187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838187 prefixEnd_3838187 := by exact prefixLift 3838187
  have htrace : WordTrace (prefixWord ++ tailWord_3838187) baseStart_3838187 baseEnd_3838187 := by
    simpa [prefixWord, tailWord_3838187, baseEnd_3838187] using wordTrace_append hprefix tailTrace_3838187
  have hstable : (prefixWord ++ tailWord_3838187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838187).length < 2 ^ (prefixWord ++ tailWord_3838187).sum := by decide
  have hdescent : baseEnd_3838187 < baseStart_3838187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838191 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_3838191 : Nat := 118140960795 + 3838191 * 2 ^ 59
def prefixEnd_3838191 : Nat := 4983230072969 + 3 ^ 40 * 3838191 * 2
def baseEnd_3838191 : Nat := 1970836826761097793760987

theorem tailTrace_3838191 : CollatzResearch.WordTrace tailWord_3838191 prefixEnd_3838191 1970836826761097793760987 := by
  unfold tailWord_3838191
  simp only [CollatzResearch.WordTrace]
  refine ⟨139990326437896992680026427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93326884291931328453350951 139990326437896992680026427)
  ·
    refine ⟨209985489656845489020039641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139990326437896992680026427 209985489656845489020039641)
    ·
      refine ⟨157489117242634116765029731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209985489656845489020039641 157489117242634116765029731)
      ·
        refine ⟨236233675863951175147544597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157489117242634116765029731 236233675863951175147544597)
        ·
          refine ⟨11073453556122711335041153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236233675863951175147544597 11073453556122711335041153)
          ·
            refine ⟨8305090167092033501280865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11073453556122711335041153 8305090167092033501280865)
            ·
              refine ⟨6228817625319025125960649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305090167092033501280865 6228817625319025125960649)
              ·
                refine ⟨4671613218989268844470487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228817625319025125960649 4671613218989268844470487)
                ·
                  refine ⟨7007419828483903266705731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671613218989268844470487 7007419828483903266705731)
                  ·
                    refine ⟨10511129742725854900058597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007419828483903266705731 10511129742725854900058597)
                    ·
                      refine ⟨1970836826761097793760987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10511129742725854900058597 1970836826761097793760987)
                      ·
                        rfl

theorem cell23_3838191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_3838191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838191 prefixEnd_3838191 := by exact prefixLift 3838191
  have htrace : WordTrace (prefixWord ++ tailWord_3838191) baseStart_3838191 baseEnd_3838191 := by
    simpa [prefixWord, tailWord_3838191, baseEnd_3838191] using wordTrace_append hprefix tailTrace_3838191
  have hstable : (prefixWord ++ tailWord_3838191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838191).length < 2 ^ (prefixWord ++ tailWord_3838191).sum := by decide
  have hdescent : baseEnd_3838191 < baseStart_3838191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838245 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_3838245 : Nat := 118140960795 + 3838245 * 2 ^ 59
def prefixEnd_3838245 : Nat := 4983230072969 + 3 ^ 40 * 3838245 * 2
def baseEnd_3838245 : Nat := 1970864554716440582485739

theorem tailTrace_3838245 : CollatzResearch.WordTrace tailWord_3838245 prefixEnd_3838245 1970864554716440582485739 := by
  unfold tailWord_3838245
  simp only [CollatzResearch.WordTrace]
  refine ⟨139992295979701359902492189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93328197319800906601661459 139992295979701359902492189)
  ·
    refine ⟨52497110992388009963434571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139992295979701359902492189 52497110992388009963434571)
    ·
      refine ⟨78745666488582014945151857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52497110992388009963434571 78745666488582014945151857)
      ·
        refine ⟨59059249866436511208863893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78745666488582014945151857 59059249866436511208863893)
        ·
          refine ⟨2768402337489211462915495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59059249866436511208863893 2768402337489211462915495)
          ·
            refine ⟨4152603506233817194373243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768402337489211462915495 4152603506233817194373243)
            ·
              refine ⟨6228905259350725791559865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152603506233817194373243 6228905259350725791559865)
              ·
                refine ⟨4671678944513044343669899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228905259350725791559865 4671678944513044343669899)
                ·
                  refine ⟨7007518416769566515504849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671678944513044343669899 7007518416769566515504849)
                  ·
                    refine ⟨5255638812577174886628637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007518416769566515504849 5255638812577174886628637)
                    ·
                      refine ⟨1970864554716440582485739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255638812577174886628637 1970864554716440582485739)
                      ·
                        rfl

theorem cell23_3838245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_3838245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838245 prefixEnd_3838245 := by exact prefixLift 3838245
  have htrace : WordTrace (prefixWord ++ tailWord_3838245) baseStart_3838245 baseEnd_3838245 := by
    simpa [prefixWord, tailWord_3838245, baseEnd_3838245] using wordTrace_append hprefix tailTrace_3838245
  have hstable : (prefixWord ++ tailWord_3838245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838245).length < 2 ^ (prefixWord ++ tailWord_3838245).sum := by decide
  have hdescent : baseEnd_3838245 < baseStart_3838245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838276 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3838276 : Nat := 118140960795 + 3838276 * 2 ^ 59
def prefixEnd_3838276 : Nat := 4983230072969 + 3 ^ 40 * 3838276 * 2
def baseEnd_3838276 : Nat := 1970880472616729961198097

theorem tailTrace_3838276 : CollatzResearch.WordTrace tailWord_3838276 prefixEnd_3838276 1970880472616729961198097 := by
  unfold tailWord_3838276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69996713321294526098435341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93328951095059368131247121 69996713321294526098435341)
  ·
    refine ⟨26248767495485447286913253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69996713321294526098435341 26248767495485447286913253)
    ·
      refine ⟨4921643905403521366296235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26248767495485447286913253 4921643905403521366296235)
      ·
        refine ⟨7382465858105282049444353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921643905403521366296235 7382465858105282049444353)
        ·
          refine ⟨5536849393578961537083265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7382465858105282049444353 5536849393578961537083265)
          ·
            refine ⟨4152637045184221152812449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536849393578961537083265 4152637045184221152812449)
            ·
              refine ⟨3114477783888165864609337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152637045184221152812449 3114477783888165864609337)
              ·
                refine ⟨2335858337916124398457003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3114477783888165864609337 2335858337916124398457003)
                ·
                  refine ⟨3503787506874186597685505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335858337916124398457003 3503787506874186597685505)
                  ·
                    refine ⟨2627840630155639948264129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503787506874186597685505 2627840630155639948264129)
                    ·
                      refine ⟨1970880472616729961198097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627840630155639948264129 1970880472616729961198097)
                      ·
                        rfl

theorem cell23_3838276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3838276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838276 prefixEnd_3838276 := by exact prefixLift 3838276
  have htrace : WordTrace (prefixWord ++ tailWord_3838276) baseStart_3838276 baseEnd_3838276 := by
    simpa [prefixWord, tailWord_3838276, baseEnd_3838276] using wordTrace_append hprefix tailTrace_3838276
  have hstable : (prefixWord ++ tailWord_3838276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838276).length < 2 ^ (prefixWord ++ tailWord_3838276).sum := by decide
  have hdescent : baseEnd_3838276 < baseStart_3838276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838277 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3838277 : Nat := 118140960795 + 3838277 * 2 ^ 59
def prefixEnd_3838277 : Nat := 4983230072969 + 3 ^ 40 * 3838277 * 2
def baseEnd_3838277 : Nat := 1970880986097384457285591

theorem tailTrace_3838277 : CollatzResearch.WordTrace tailWord_3838277 prefixEnd_3838277 1970880986097384457285591 := by
  unfold tailWord_3838277
  simp only [CollatzResearch.WordTrace]
  refine ⟨139993463115585429367657085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93328975410390286245104723 139993463115585429367657085)
  ·
    refine ⟨52497548668344536012871407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139993463115585429367657085 52497548668344536012871407)
    ·
      refine ⟨78746323002516804019307111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52497548668344536012871407 78746323002516804019307111)
      ·
        refine ⟨118119484503775206028960667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78746323002516804019307111 118119484503775206028960667)
        ·
          refine ⟨177179226755662809043441001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118119484503775206028960667 177179226755662809043441001)
          ·
            refine ⟨132884420066747106782580751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177179226755662809043441001 132884420066747106782580751)
            ·
              refine ⟨199326630100120660173871127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132884420066747106782580751 199326630100120660173871127)
              ·
                refine ⟨298989945150180990260806691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199326630100120660173871127 298989945150180990260806691)
                ·
                  refine ⟨448484917725271485391210037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298989945150180990260806691 448484917725271485391210037)
                  ·
                    refine ⟨42045461036744201755425941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 448484917725271485391210037 42045461036744201755425941)
                    ·
                      refine ⟨1970880986097384457285591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42045461036744201755425941 1970880986097384457285591)
                      ·
                        rfl

theorem cell23_3838277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3838277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838277 prefixEnd_3838277 := by exact prefixLift 3838277
  have htrace : WordTrace (prefixWord ++ tailWord_3838277) baseStart_3838277 baseEnd_3838277 := by
    simpa [prefixWord, tailWord_3838277, baseEnd_3838277] using wordTrace_append hprefix tailTrace_3838277
  have hstable : (prefixWord ++ tailWord_3838277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838277).length < 2 ^ (prefixWord ++ tailWord_3838277).sum := by decide
  have hdescent : baseEnd_3838277 < baseStart_3838277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838284 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3838284 : Nat := 118140960795 + 3838284 * 2 ^ 59
def prefixEnd_3838284 : Nat := 4983230072969 + 3 ^ 40 * 3838284 * 2
def baseEnd_3838284 : Nat := 1970884580461965929898059

theorem tailTrace_3838284 : CollatzResearch.WordTrace tailWord_3838284 prefixEnd_3838284 1970884580461965929898059 := by
  unfold tailWord_3838284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69996859213280034781580953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93329145617706713042107937 69996859213280034781580953)
  ·
    refine ⟨52497644409960026086185715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69996859213280034781580953 52497644409960026086185715)
    ·
      refine ⟨78746466614940039129278573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52497644409960026086185715 78746466614940039129278573)
      ·
        refine ⟨29529924980602514673479465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78746466614940039129278573 29529924980602514673479465)
        ·
          refine ⟨22147443735451886005109599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29529924980602514673479465 22147443735451886005109599)
          ·
            refine ⟨33221165603177829007664399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22147443735451886005109599 33221165603177829007664399)
            ·
              refine ⟨49831748404766743511496599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33221165603177829007664399 49831748404766743511496599)
              ·
                refine ⟨74747622607150115267244899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49831748404766743511496599 74747622607150115267244899)
                ·
                  refine ⟨112121433910725172900867349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74747622607150115267244899 112121433910725172900867349)
                  ·
                    refine ⟨5255692214565242479728157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112121433910725172900867349 5255692214565242479728157)
                    ·
                      refine ⟨1970884580461965929898059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255692214565242479728157 1970884580461965929898059)
                      ·
                        rfl

theorem cell23_3838284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3838284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838284 prefixEnd_3838284 := by exact prefixLift 3838284
  have htrace : WordTrace (prefixWord ++ tailWord_3838284) baseStart_3838284 baseEnd_3838284 := by
    simpa [prefixWord, tailWord_3838284, baseEnd_3838284] using wordTrace_append hprefix tailTrace_3838284
  have hstable : (prefixWord ++ tailWord_3838284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838284).length < 2 ^ (prefixWord ++ tailWord_3838284).sum := by decide
  have hdescent : baseEnd_3838284 < baseStart_3838284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838344 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3838344 : Nat := 118140960795 + 3838344 * 2 ^ 59
def prefixEnd_3838344 : Nat := 4983230072969 + 3 ^ 40 * 3838344 * 2
def baseEnd_3838344 : Nat := 1970915389301235695147783

theorem tailTrace_3838344 : CollatzResearch.WordTrace tailWord_3838344 prefixEnd_3838344 1970915389301235695147783 := by
  unfold tailWord_3838344
  simp only [CollatzResearch.WordTrace]
  refine ⟨69997953403171349905173043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93330604537561799873564057 69997953403171349905173043)
  ·
    refine ⟨104996930104757024857759565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69997953403171349905173043 104996930104757024857759565)
    ·
      refine ⟨39373848789283884321659837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104996930104757024857759565 39373848789283884321659837)
      ·
        refine ⟨14765193295981456620622439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39373848789283884321659837 14765193295981456620622439)
        ·
          refine ⟨22147789943972184930933659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14765193295981456620622439 22147789943972184930933659)
          ·
            refine ⟨33221684915958277396400489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22147789943972184930933659 33221684915958277396400489)
            ·
              refine ⟨24916263686968708047300367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33221684915958277396400489 24916263686968708047300367)
              ·
                refine ⟨37374395530453062070950551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916263686968708047300367 37374395530453062070950551)
                ·
                  refine ⟨56061593295679593106425827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37374395530453062070950551 56061593295679593106425827)
                  ·
                    refine ⟨84092389943519389659638741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56061593295679593106425827 84092389943519389659638741)
                    ·
                      refine ⟨1970915389301235695147783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84092389943519389659638741 1970915389301235695147783)
                      ·
                        rfl

theorem cell23_3838344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3838344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838344 prefixEnd_3838344 := by exact prefixLift 3838344
  have htrace : WordTrace (prefixWord ++ tailWord_3838344) baseStart_3838344 baseEnd_3838344 := by
    simpa [prefixWord, tailWord_3838344, baseEnd_3838344] using wordTrace_append hprefix tailTrace_3838344
  have hstable : (prefixWord ++ tailWord_3838344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838344).length < 2 ^ (prefixWord ++ tailWord_3838344).sum := by decide
  have hdescent : baseEnd_3838344 < baseStart_3838344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838391 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_3838391 : Nat := 118140960795 + 3838391 * 2 ^ 59
def prefixEnd_3838391 : Nat := 4983230072969 + 3 ^ 40 * 3838391 * 2
def baseEnd_3838391 : Nat := 1970939522891997011260067

theorem tailTrace_3838391 : CollatzResearch.WordTrace tailWord_3838391 prefixEnd_3838391 1970939522891997011260067 := by
  unfold tailWord_3838391
  simp only [CollatzResearch.WordTrace]
  refine ⟨139997621037172426837307027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93331747358114951224871351 139997621037172426837307027)
  ·
    refine ⟨209996431555758640255960541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139997621037172426837307027 209996431555758640255960541)
    ·
      refine ⟨78748661833409490095985203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209996431555758640255960541 78748661833409490095985203)
      ·
        refine ⟨118122992750114235143977805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78748661833409490095985203 118122992750114235143977805)
        ·
          refine ⟨44296122281292838178991677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118122992750114235143977805 44296122281292838178991677)
          ·
            refine ⟨16611045855484814317121879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44296122281292838178991677 16611045855484814317121879)
            ·
              refine ⟨24916568783227221475682819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16611045855484814317121879 24916568783227221475682819)
              ·
                refine ⟨37374853174840832213524229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916568783227221475682819 37374853174840832213524229)
                ·
                  refine ⟨7007784970282656040035793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37374853174840832213524229 7007784970282656040035793)
                  ·
                    refine ⟨5255838727711992030026845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007784970282656040035793 5255838727711992030026845)
                    ·
                      refine ⟨1970939522891997011260067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5255838727711992030026845 1970939522891997011260067)
                      ·
                        rfl

theorem cell23_3838391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_3838391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838391 prefixEnd_3838391 := by exact prefixLift 3838391
  have htrace : WordTrace (prefixWord ++ tailWord_3838391) baseStart_3838391 baseEnd_3838391 := by
    simpa [prefixWord, tailWord_3838391, baseEnd_3838391] using wordTrace_append hprefix tailTrace_3838391
  have hstable : (prefixWord ++ tailWord_3838391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838391).length < 2 ^ (prefixWord ++ tailWord_3838391).sum := by decide
  have hdescent : baseEnd_3838391 < baseStart_3838391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838398 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3838398 : Nat := 118140960795 + 3838398 * 2 ^ 59
def prefixEnd_3838398 : Nat := 4983230072969 + 3 ^ 40 * 3838398 * 2
def baseEnd_3838398 : Nat := 656981039085526161290845

theorem tailTrace_3838398 : CollatzResearch.WordTrace tailWord_3838398 prefixEnd_3838398 656981039085526161290845 := by
  unfold tailWord_3838398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499734543518383379101481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93331917565431378021874565 17499734543518383379101481)
  ·
    refine ⟨13124800907638787534326111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17499734543518383379101481 13124800907638787534326111)
    ·
      refine ⟨19687201361458181301489167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124800907638787534326111 19687201361458181301489167)
      ·
        refine ⟨29530802042187271952233751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687201361458181301489167 29530802042187271952233751)
        ·
          refine ⟨44296203063280907928350627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29530802042187271952233751 44296203063280907928350627)
          ·
            refine ⟨66444304594921361892525941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44296203063280907928350627 66444304594921361892525941)
            ·
              refine ⟨6229153555773877677424307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66444304594921361892525941 6229153555773877677424307)
              ·
                refine ⟨9343730333660816516136461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229153555773877677424307 9343730333660816516136461)
                ·
                  refine ⟨3503898875122806193551173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9343730333660816516136461 3503898875122806193551173)
                  ·
                    refine ⟨656981039085526161290845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503898875122806193551173 656981039085526161290845)
                    ·
                      rfl

theorem cell23_3838398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3838398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838398 prefixEnd_3838398 := by exact prefixLift 3838398
  have htrace : WordTrace (prefixWord ++ tailWord_3838398) baseStart_3838398 baseEnd_3838398 := by
    simpa [prefixWord, tailWord_3838398, baseEnd_3838398] using wordTrace_append hprefix tailTrace_3838398
  have hstable : (prefixWord ++ tailWord_3838398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838398).length < 2 ^ (prefixWord ++ tailWord_3838398).sum := by decide
  have hdescent : baseEnd_3838398 < baseStart_3838398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838448 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2]
def baseStart_3838448 : Nat := 118140960795 + 3838448 * 2 ^ 59
def prefixEnd_3838448 : Nat := 4983230072969 + 3 ^ 40 * 3838448 * 2
def baseEnd_3838448 : Nat := 1970968791289303288247305

theorem tailTrace_3838448 : CollatzResearch.WordTrace tailWord_3838448 prefixEnd_3838448 1970968791289303288247305 := by
  unfold tailWord_3838448
  simp only [CollatzResearch.WordTrace]
  refine ⟨69999849998982962786065999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93333133331977283714754665 69999849998982962786065999)
  ·
    refine ⟨104999774998474444179098999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69999849998982962786065999 104999774998474444179098999)
    ·
      refine ⟨157499662497711666268648499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104999774998474444179098999 157499662497711666268648499)
      ·
        refine ⟨236249493746567499402972749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157499662497711666268648499 236249493746567499402972749)
        ·
          refine ⟨88593560154962812276114781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236249493746567499402972749 88593560154962812276114781)
          ·
            refine ⟨33222585058111054603543043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88593560154962812276114781 33222585058111054603543043)
            ·
              refine ⟨49833877587166581905314565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222585058111054603543043 49833877587166581905314565)
              ·
                refine ⟨9343852047593734107246481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49833877587166581905314565 9343852047593734107246481)
                ·
                  refine ⟨7007889035695300580434861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343852047593734107246481 7007889035695300580434861)
                  ·
                    refine ⟨2627958388385737717663073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7007889035695300580434861 2627958388385737717663073)
                    ·
                      refine ⟨1970968791289303288247305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2627958388385737717663073 1970968791289303288247305)
                      ·
                        rfl

theorem cell23_3838448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2].length) (baseStart_3838448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838448 prefixEnd_3838448 := by exact prefixLift 3838448
  have htrace : WordTrace (prefixWord ++ tailWord_3838448) baseStart_3838448 baseEnd_3838448 := by
    simpa [prefixWord, tailWord_3838448, baseEnd_3838448] using wordTrace_append hprefix tailTrace_3838448
  have hstable : (prefixWord ++ tailWord_3838448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838448).length < 2 ^ (prefixWord ++ tailWord_3838448).sum := by decide
  have hdescent : baseEnd_3838448 < baseStart_3838448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838461 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3838461 : Nat := 118140960795 + 3838461 * 2 ^ 59
def prefixEnd_3838461 : Nat := 4983230072969 + 3 ^ 40 * 3838461 * 2
def baseEnd_3838461 : Nat := 1970975466537811737384745

theorem tailTrace_3838461 : CollatzResearch.WordTrace tailWord_3838461 prefixEnd_3838461 1970975466537811737384745 := by
  unfold tailWord_3838461
  simp only [CollatzResearch.WordTrace]
  refine ⟨140000174146918828792355237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93333449431279219194903491 140000174146918828792355237)
  ·
    refine ⟨26250032652547280398566607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140000174146918828792355237 26250032652547280398566607)
    ·
      refine ⟨39375048978820920597849911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26250032652547280398566607 39375048978820920597849911)
      ·
        refine ⟨59062573468231380896774867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39375048978820920597849911 59062573468231380896774867)
        ·
          refine ⟨88593860202347071345162301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59062573468231380896774867 88593860202347071345162301)
          ·
            refine ⟨33222697575880151754435863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88593860202347071345162301 33222697575880151754435863)
            ·
              refine ⟨49834046363820227631653795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222697575880151754435863 49834046363820227631653795)
              ·
                refine ⟨74751069545730341447480693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49834046363820227631653795 74751069545730341447480693)
                ·
                  refine ⟨7007912769912219510701315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74751069545730341447480693 7007912769912219510701315)
                  ·
                    refine ⟨10511869154868329266051973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007912769912219510701315 10511869154868329266051973)
                    ·
                      refine ⟨1970975466537811737384745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10511869154868329266051973 1970975466537811737384745)
                      ·
                        rfl

theorem cell23_3838461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3838461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838461 prefixEnd_3838461 := by exact prefixLift 3838461
  have htrace : WordTrace (prefixWord ++ tailWord_3838461) baseStart_3838461 baseEnd_3838461 := by
    simpa [prefixWord, tailWord_3838461, baseEnd_3838461] using wordTrace_append hprefix tailTrace_3838461
  have hstable : (prefixWord ++ tailWord_3838461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838461).length < 2 ^ (prefixWord ++ tailWord_3838461).sum := by decide
  have hdescent : baseEnd_3838461 < baseStart_3838461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838478 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3838478 : Nat := 118140960795 + 3838478 * 2 ^ 59
def prefixEnd_3838478 : Nat := 4983230072969 + 3 ^ 40 * 3838478 * 2
def baseEnd_3838478 : Nat := 1970984195708938170872167

theorem tailTrace_3838478 : CollatzResearch.WordTrace tailWord_3838478 prefixEnd_3838478 1970984195708938170872167 := by
  unfold tailWord_3838478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17500099273482155086965511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93333862791904827130482725 17500099273482155086965511)
  ·
    refine ⟨26250148910223232630448267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17500099273482155086965511 26250148910223232630448267)
    ·
      refine ⟨39375223365334848945672401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26250148910223232630448267 39375223365334848945672401)
      ·
        refine ⟨29531417524001136709254301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39375223365334848945672401 29531417524001136709254301)
        ·
          refine ⟨11074281571500426265970363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29531417524001136709254301 11074281571500426265970363)
          ·
            refine ⟨16611422357250639398955545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074281571500426265970363 16611422357250639398955545)
            ·
              refine ⟨12458566767937979549216659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16611422357250639398955545 12458566767937979549216659)
              ·
                refine ⟨18687850151906969323824989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12458566767937979549216659 18687850151906969323824989)
                ·
                  refine ⟨7007943806965113496434371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18687850151906969323824989 7007943806965113496434371)
                  ·
                    refine ⟨10511915710447670244651557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007943806965113496434371 10511915710447670244651557)
                    ·
                      refine ⟨1970984195708938170872167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10511915710447670244651557 1970984195708938170872167)
                      ·
                        rfl

theorem cell23_3838478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3838478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838478 prefixEnd_3838478 := by exact prefixLift 3838478
  have htrace : WordTrace (prefixWord ++ tailWord_3838478) baseStart_3838478 baseEnd_3838478 := by
    simpa [prefixWord, tailWord_3838478, baseEnd_3838478] using wordTrace_append hprefix tailTrace_3838478
  have hstable : (prefixWord ++ tailWord_3838478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838478).length < 2 ^ (prefixWord ++ tailWord_3838478).sum := by decide
  have hdescent : baseEnd_3838478 < baseStart_3838478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838512 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 1, 2, 2]
def baseStart_3838512 : Nat := 118140960795 + 3838512 * 2 ^ 59
def prefixEnd_3838512 : Nat := 4983230072969 + 3 ^ 40 * 3838512 * 2
def baseEnd_3838512 : Nat := 1971001654051191037847011

theorem tailTrace_3838512 : CollatzResearch.WordTrace tailWord_3838512 prefixEnd_3838512 1971001654051191037847011 := by
  unfold tailWord_3838512
  simp only [CollatzResearch.WordTrace]
  refine ⟨70001017134867032251230895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93334689513156043001641193 70001017134867032251230895)
  ·
    refine ⟨105001525702300548376846343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70001017134867032251230895 105001525702300548376846343)
    ·
      refine ⟨157502288553450822565269515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105001525702300548376846343 157502288553450822565269515)
      ·
        refine ⟨236253432830176233847904273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157502288553450822565269515 236253432830176233847904273)
        ·
          refine ⟨177190074622632175385928205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236253432830176233847904273 177190074622632175385928205)
          ·
            refine ⟨66446277983487065769723077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177190074622632175385928205 66446277983487065769723077)
            ·
              refine ⟨12458677121903824831823077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66446277983487065769723077 12458677121903824831823077)
              ·
                refine ⟨2336001960356967155966827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12458677121903824831823077 2336001960356967155966827)
                ·
                  refine ⟨3504002940535450733950241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336001960356967155966827 3504002940535450733950241)
                  ·
                    refine ⟨2628002205401588050462681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3504002940535450733950241 2628002205401588050462681)
                    ·
                      refine ⟨1971001654051191037847011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628002205401588050462681 1971001654051191037847011)
                      ·
                        rfl

theorem cell23_3838512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 2, 2].length) (baseStart_3838512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838512 prefixEnd_3838512 := by exact prefixLift 3838512
  have htrace : WordTrace (prefixWord ++ tailWord_3838512) baseStart_3838512 baseEnd_3838512 := by
    simpa [prefixWord, tailWord_3838512, baseEnd_3838512] using wordTrace_append hprefix tailTrace_3838512
  have hstable : (prefixWord ++ tailWord_3838512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838512).length < 2 ^ (prefixWord ++ tailWord_3838512).sum := by decide
  have hdescent : baseEnd_3838512 < baseStart_3838512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838525 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3838525 : Nat := 118140960795 + 3838525 * 2 ^ 59
def prefixEnd_3838525 : Nat := 4983230072969 + 3 ^ 40 * 3838525 * 2
def baseEnd_3838525 : Nat := 1971008329299699486984451

theorem tailTrace_3838525 : CollatzResearch.WordTrace tailWord_3838525 prefixEnd_3838525 1971008329299699486984451 := by
  unfold tailWord_3838525
  simp only [CollatzResearch.WordTrace]
  refine ⟨140002508418686967722685029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93335005612457978481790019 140002508418686967722685029)
  ·
    refine ⟨26250470328503806448003443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140002508418686967722685029 26250470328503806448003443)
    ·
      refine ⟨39375705492755709672005165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26250470328503806448003443 39375705492755709672005165)
      ·
        refine ⟨14765889559783391127001937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39375705492755709672005165 14765889559783391127001937)
        ·
          refine ⟨11074417169837543345251453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14765889559783391127001937 11074417169837543345251453)
          ·
            refine ⟨4152906438689078754469295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11074417169837543345251453 4152906438689078754469295)
            ·
              refine ⟨6229359658033618131703943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152906438689078754469295 6229359658033618131703943)
              ·
                refine ⟨9344039487050427197555915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229359658033618131703943 9344039487050427197555915)
                ·
                  refine ⟨14016059230575640796333873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344039487050427197555915 14016059230575640796333873)
                  ·
                    refine ⟨10512044422931730597250405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14016059230575640796333873 10512044422931730597250405)
                    ·
                      refine ⟨1971008329299699486984451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10512044422931730597250405 1971008329299699486984451)
                      ·
                        rfl

theorem cell23_3838525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3838525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838525 prefixEnd_3838525 := by exact prefixLift 3838525
  have htrace : WordTrace (prefixWord ++ tailWord_3838525) baseStart_3838525 baseEnd_3838525 := by
    simpa [prefixWord, tailWord_3838525, baseEnd_3838525] using wordTrace_append hprefix tailTrace_3838525
  have hstable : (prefixWord ++ tailWord_3838525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838525).length < 2 ^ (prefixWord ++ tailWord_3838525).sum := by decide
  have hdescent : baseEnd_3838525 < baseStart_3838525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838528 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_3838528 : Nat := 118140960795 + 3838528 * 2 ^ 59
def prefixEnd_3838528 : Nat := 4983230072969 + 3 ^ 40 * 3838528 * 2
def baseEnd_3838528 : Nat := 1971009869741662975246937

theorem tailTrace_3838528 : CollatzResearch.WordTrace tailWord_3838528 prefixEnd_3838528 1971009869741662975246937 := by
  unfold tailWord_3838528
  simp only [CollatzResearch.WordTrace]
  refine ⟨70001308918838049617522119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93335078558450732823362825 70001308918838049617522119)
  ·
    refine ⟨105001963378257074426283179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70001308918838049617522119 105001963378257074426283179)
    ·
      refine ⟨157502945067385611639424769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105001963378257074426283179 157502945067385611639424769)
      ·
        refine ⟨118127208800539208729568577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157502945067385611639424769 118127208800539208729568577)
        ·
          refine ⟨88595406600404406547176433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118127208800539208729568577 88595406600404406547176433)
          ·
            refine ⟨66446554950303304910382325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88595406600404406547176433 66446554950303304910382325)
            ·
              refine ⟨6229364526590934835348343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66446554950303304910382325 6229364526590934835348343)
              ·
                refine ⟨9344046789886402253022515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229364526590934835348343 9344046789886402253022515)
                ·
                  refine ⟨14016070184829603379533773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344046789886402253022515 14016070184829603379533773)
                  ·
                    refine ⟨5256026319311101267325165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14016070184829603379533773 5256026319311101267325165)
                    ·
                      refine ⟨1971009869741662975246937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5256026319311101267325165 1971009869741662975246937)
                      ·
                        rfl

theorem cell23_3838528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_3838528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838528 prefixEnd_3838528 := by exact prefixLift 3838528
  have htrace : WordTrace (prefixWord ++ tailWord_3838528) baseStart_3838528 baseEnd_3838528 := by
    simpa [prefixWord, tailWord_3838528, baseEnd_3838528] using wordTrace_append hprefix tailTrace_3838528
  have hstable : (prefixWord ++ tailWord_3838528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838528).length < 2 ^ (prefixWord ++ tailWord_3838528).sum := by decide
  have hdescent : baseEnd_3838528 < baseStart_3838528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838589 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_3838589 : Nat := 118140960795 + 3838589 * 2 ^ 59
def prefixEnd_3838589 : Nat := 4983230072969 + 3 ^ 40 * 3838589 * 2
def baseEnd_3838589 : Nat := 1971041192061587236584157

theorem tailTrace_3838589 : CollatzResearch.WordTrace tailWord_3838589 prefixEnd_3838589 1971041192061587236584157 := by
  unfold tailWord_3838589
  simp only [CollatzResearch.WordTrace]
  refine ⟨140004842690455106653014821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93336561793636737768676547 140004842690455106653014821)
  ·
    refine ⟨26250908004460332497440279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140004842690455106653014821 26250908004460332497440279)
    ·
      refine ⟨39376362006690498746160419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26250908004460332497440279 39376362006690498746160419)
      ·
        refine ⟨59064543010035748119240629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39376362006690498746160419 59064543010035748119240629)
        ·
          refine ⟨5537300907190851386178809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59064543010035748119240629 5537300907190851386178809)
          ·
            refine ⟨4152975680393138539634107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537300907190851386178809 4152975680393138539634107)
            ·
              refine ⟨6229463520589707809451161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152975680393138539634107 6229463520589707809451161)
              ·
                refine ⟨4672097640442280857088371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229463520589707809451161 4672097640442280857088371)
                ·
                  refine ⟨7008146460663421285632557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672097640442280857088371 7008146460663421285632557)
                  ·
                    refine ⟨2628054922748782982112209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7008146460663421285632557 2628054922748782982112209)
                    ·
                      refine ⟨1971041192061587236584157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628054922748782982112209 1971041192061587236584157)
                      ·
                        rfl

theorem cell23_3838589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_3838589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838589 prefixEnd_3838589 := by exact prefixLift 3838589
  have htrace : WordTrace (prefixWord ++ tailWord_3838589) baseStart_3838589 baseEnd_3838589 := by
    simpa [prefixWord, tailWord_3838589, baseEnd_3838589] using wordTrace_append hprefix tailTrace_3838589
  have hstable : (prefixWord ++ tailWord_3838589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838589).length < 2 ^ (prefixWord ++ tailWord_3838589).sum := by decide
  have hdescent : baseEnd_3838589 < baseStart_3838589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838602 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_3838602 : Nat := 118140960795 + 3838602 * 2 ^ 59
def prefixEnd_3838602 : Nat := 4983230072969 + 3 ^ 40 * 3838602 * 2
def baseEnd_3838602 : Nat := 1971047867310095685721597

theorem tailTrace_3838602 : CollatzResearch.WordTrace tailWord_3838602 prefixEnd_3838602 1971047867310095685721597 := by
  unfold tailWord_3838602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001329209852002468309515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93336877892938673248825373 35001329209852002468309515)
  ·
    refine ⟨52501993814778003702464273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35001329209852002468309515 52501993814778003702464273)
    ·
      refine ⟨39376495361083502776848205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52501993814778003702464273 39376495361083502776848205)
      ·
        refine ⟨14766185760406313541318077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39376495361083502776848205 14766185760406313541318077)
        ·
          refine ⟨5537319660152367577994279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14766185760406313541318077 5537319660152367577994279)
          ·
            refine ⟨8305979490228551366991419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537319660152367577994279 8305979490228551366991419)
            ·
              refine ⟨12458969235342827050487129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8305979490228551366991419 12458969235342827050487129)
              ·
                refine ⟨9344226926507120287865347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12458969235342827050487129 9344226926507120287865347)
                ·
                  refine ⟨14016340389760680431798021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344226926507120287865347 14016340389760680431798021)
                  ·
                    refine ⟨2628063823080127580962129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14016340389760680431798021 2628063823080127580962129)
                    ·
                      refine ⟨1971047867310095685721597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628063823080127580962129 1971047867310095685721597)
                      ·
                        rfl

theorem cell23_3838602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_3838602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838602 prefixEnd_3838602 := by exact prefixLift 3838602
  have htrace : WordTrace (prefixWord ++ tailWord_3838602) baseStart_3838602 baseEnd_3838602 := by
    simpa [prefixWord, tailWord_3838602, baseEnd_3838602] using wordTrace_append hprefix tailTrace_3838602
  have hstable : (prefixWord ++ tailWord_3838602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838602).length < 2 ^ (prefixWord ++ tailWord_3838602).sum := by decide
  have hdescent : baseEnd_3838602 < baseStart_3838602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838655 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 2, 5]
def baseStart_3838655 : Nat := 118140960795 + 3838655 * 2 ^ 59
def prefixEnd_3838655 : Nat := 4983230072969 + 3 ^ 40 * 3838655 * 2
def baseEnd_3838655 : Nat := 657025027261594659452951

theorem tailTrace_3838655 : CollatzResearch.WordTrace tailWord_3838655 prefixEnd_3838655 657025027261594659452951 := by
  unfold tailWord_3838655
  simp only [CollatzResearch.WordTrace]
  refine ⟨140007249908215999924917419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93338166605477333283278279 140007249908215999924917419)
  ·
    refine ⟨210010874862323999887376129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140007249908215999924917419 210010874862323999887376129)
    ·
      refine ⟨157508156146742999915532097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210010874862323999887376129 157508156146742999915532097)
      ·
        refine ⟨118131117110057249936649073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157508156146742999915532097 118131117110057249936649073)
        ·
          refine ⟨88598337832542937452486805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118131117110057249936649073 88598337832542937452486805)
          ·
            refine ⟨4153047085900450193085319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88598337832542937452486805 4153047085900450193085319)
            ·
              refine ⟨6229570628850675289627979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153047085900450193085319 6229570628850675289627979)
              ·
                refine ⟨9344355943276012934441969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229570628850675289627979 9344355943276012934441969)
                ·
                  refine ⟨7008266957457009700831477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9344355943276012934441969 7008266957457009700831477)
                  ·
                    refine ⟨657025027261594659452951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7008266957457009700831477 657025027261594659452951)
                    ·
                      rfl

theorem cell23_3838655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_3838655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838655 prefixEnd_3838655 := by exact prefixLift 3838655
  have htrace : WordTrace (prefixWord ++ tailWord_3838655) baseStart_3838655 baseEnd_3838655 := by
    simpa [prefixWord, tailWord_3838655, baseEnd_3838655] using wordTrace_append hprefix tailTrace_3838655
  have hstable : (prefixWord ++ tailWord_3838655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838655).length < 2 ^ (prefixWord ++ tailWord_3838655).sum := by decide
  have hdescent : baseEnd_3838655 < baseStart_3838655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838661 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3838661 : Nat := 118140960795 + 3838661 * 2 ^ 59
def prefixEnd_3838661 : Nat := 4983230072969 + 3 ^ 40 * 3838661 * 2
def baseEnd_3838661 : Nat := 1971078162668710954883825

theorem tailTrace_3838661 : CollatzResearch.WordTrace tailWord_3838661 prefixEnd_3838661 1971078162668710954883825 := by
  unfold tailWord_3838661
  simp only [CollatzResearch.WordTrace]
  refine ⟨140007468746194262949635837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93338312497462841966423891 140007468746194262949635837)
  ·
    refine ⟨52502800779822848606113439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140007468746194262949635837 52502800779822848606113439)
    ·
      refine ⟨78754201169734272909170159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52502800779822848606113439 78754201169734272909170159)
      ·
        refine ⟨118131301754601409363755239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78754201169734272909170159 118131301754601409363755239)
        ·
          refine ⟨177196952631902114045632859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118131301754601409363755239 177196952631902114045632859)
          ·
            refine ⟨265795428947853171068449289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177196952631902114045632859 265795428947853171068449289)
            ·
              refine ⟨199346571710889878301336967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265795428947853171068449289 199346571710889878301336967)
              ·
                refine ⟨299019857566334817452005451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199346571710889878301336967 299019857566334817452005451)
                ·
                  refine ⟨448529786349502226178008177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299019857566334817452005451 448529786349502226178008177)
                  ·
                    refine ⟨336397339762126669633506133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 448529786349502226178008177 336397339762126669633506133)
                    ·
                      refine ⟨1971078162668710954883825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 336397339762126669633506133 1971078162668710954883825)
                      ·
                        rfl

theorem cell23_3838661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3838661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838661 prefixEnd_3838661 := by exact prefixLift 3838661
  have htrace : WordTrace (prefixWord ++ tailWord_3838661) baseStart_3838661 baseEnd_3838661 := by
    simpa [prefixWord, tailWord_3838661, baseEnd_3838661] using wordTrace_append hprefix tailTrace_3838661
  have hstable : (prefixWord ++ tailWord_3838661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838661).length < 2 ^ (prefixWord ++ tailWord_3838661).sum := by decide
  have hdescent : baseEnd_3838661 < baseStart_3838661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838725 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_3838725 : Nat := 118140960795 + 3838725 * 2 ^ 59
def prefixEnd_3838725 : Nat := 4983230072969 + 3 ^ 40 * 3838725 * 2
def baseEnd_3838725 : Nat := 1971111025430598704483531

theorem tailTrace_3838725 : CollatzResearch.WordTrace tailWord_3838725 prefixEnd_3838725 1971111025430598704483531 := by
  unfold tailWord_3838725
  simp only [CollatzResearch.WordTrace]
  refine ⟨140009803017962401879965629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93339868678641601253310419 140009803017962401879965629)
  ·
    refine ⟨52503676131735900704987111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140009803017962401879965629 52503676131735900704987111)
    ·
      refine ⟨78755514197603851057480667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52503676131735900704987111 78755514197603851057480667)
      ·
        refine ⟨118133271296405776586221001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78755514197603851057480667 118133271296405776586221001)
        ·
          refine ⟨88599953472304332439665751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118133271296405776586221001 88599953472304332439665751)
          ·
            refine ⟨132899930208456498659498627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88599953472304332439665751 132899930208456498659498627)
            ·
              refine ⟨199349895312684747989247941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132899930208456498659498627 199349895312684747989247941)
              ·
                refine ⟨37378105371128390247983989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199349895312684747989247941 37378105371128390247983989)
                ·
                  refine ⟨3504197378543286585748499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37378105371128390247983989 3504197378543286585748499)
                  ·
                    refine ⟨5256296067814929878622749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3504197378543286585748499 5256296067814929878622749)
                    ·
                      refine ⟨1971111025430598704483531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5256296067814929878622749 1971111025430598704483531)
                      ·
                        rfl

theorem cell23_3838725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_3838725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838725 prefixEnd_3838725 := by exact prefixLift 3838725
  have htrace : WordTrace (prefixWord ++ tailWord_3838725) baseStart_3838725 baseEnd_3838725 := by
    simpa [prefixWord, tailWord_3838725, baseEnd_3838725] using wordTrace_append hprefix tailTrace_3838725
  have hstable : (prefixWord ++ tailWord_3838725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838725).length < 2 ^ (prefixWord ++ tailWord_3838725).sum := by decide
  have hdescent : baseEnd_3838725 < baseStart_3838725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838768 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_3838768 : Nat := 118140960795 + 3838768 * 2 ^ 59
def prefixEnd_3838768 : Nat := 4983230072969 + 3 ^ 40 * 3838768 * 2
def baseEnd_3838768 : Nat := 1971133105098742036245833

theorem tailTrace_3838768 : CollatzResearch.WordTrace tailWord_3838768 prefixEnd_3838768 1971133105098742036245833 := by
  unfold tailWord_3838768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70005685678403310111890479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93340914237871080149187305 70005685678403310111890479)
  ·
    refine ⟨105008528517604965167835719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70005685678403310111890479 105008528517604965167835719)
    ·
      refine ⟨157512792776407447751753579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105008528517604965167835719 157512792776407447751753579)
      ·
        refine ⟨236269189164611171627630369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157512792776407447751753579 236269189164611171627630369)
        ·
          refine ⟨177201891873458378720722777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236269189164611171627630369 177201891873458378720722777)
          ·
            refine ⟨132901418905093784040542083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177201891873458378720722777 132901418905093784040542083)
            ·
              refine ⟨199352128357640676060813125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132901418905093784040542083 199352128357640676060813125)
              ·
                refine ⟨37378524067057626761402461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199352128357640676060813125 37378524067057626761402461)
                ·
                  refine ⟨14016946525146610035525923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37378524067057626761402461 14016946525146610035525923)
                  ·
                    refine ⟨21025419787719915053288885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14016946525146610035525923 21025419787719915053288885)
                    ·
                      refine ⟨1971133105098742036245833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21025419787719915053288885 1971133105098742036245833)
                      ·
                        rfl

theorem cell23_3838768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_3838768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838768 prefixEnd_3838768 := by exact prefixLift 3838768
  have htrace : WordTrace (prefixWord ++ tailWord_3838768) baseStart_3838768 baseEnd_3838768 := by
    simpa [prefixWord, tailWord_3838768, baseEnd_3838768] using wordTrace_append hprefix tailTrace_3838768
  have hstable : (prefixWord ++ tailWord_3838768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838768).length < 2 ^ (prefixWord ++ tailWord_3838768).sum := by decide
  have hdescent : baseEnd_3838768 < baseStart_3838768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838792 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_3838792 : Nat := 118140960795 + 3838792 * 2 ^ 59
def prefixEnd_3838792 : Nat := 4983230072969 + 3 ^ 40 * 3838792 * 2
def baseEnd_3838792 : Nat := 657048476211483314115241

theorem tailTrace_3838792 : CollatzResearch.WordTrace tailWord_3838792 prefixEnd_3838792 657048476211483314115241 := by
  unfold tailWord_3838792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70006123354359836161327315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93341497805813114881769753 70006123354359836161327315)
  ·
    refine ⟨105009185031539754241990973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70006123354359836161327315 105009185031539754241990973)
    ·
      refine ⟨39378444386827407840746615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105009185031539754241990973 39378444386827407840746615)
      ·
        refine ⟨59067666580241111761119923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39378444386827407840746615 59067666580241111761119923)
        ·
          refine ⟨88601499870361667641679885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59067666580241111761119923 88601499870361667641679885)
          ·
            refine ⟨33225562451385625365629957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88601499870361667641679885 33225562451385625365629957)
            ·
              refine ⟨6229792959634804756055617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33225562451385625365629957 6229792959634804756055617)
              ·
                refine ⟨4672344719726103567041713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229792959634804756055617 4672344719726103567041713)
                ·
                  refine ⟨3504258539794577675281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672344719726103567041713 3504258539794577675281285)
                  ·
                    refine ⟨657048476211483314115241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3504258539794577675281285 657048476211483314115241)
                    ·
                      rfl

theorem cell23_3838792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_3838792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838792 prefixEnd_3838792 := by exact prefixLift 3838792
  have htrace : WordTrace (prefixWord ++ tailWord_3838792) baseStart_3838792 baseEnd_3838792 := by
    simpa [prefixWord, tailWord_3838792, baseEnd_3838792] using wordTrace_append hprefix tailTrace_3838792
  have hstable : (prefixWord ++ tailWord_3838792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838792).length < 2 ^ (prefixWord ++ tailWord_3838792).sum := by decide
  have hdescent : baseEnd_3838792 < baseStart_3838792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838808 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3838808 : Nat := 118140960795 + 3838808 * 2 ^ 59
def prefixEnd_3838808 : Nat := 4983230072969 + 3 ^ 40 * 3838808 * 2
def baseEnd_3838808 : Nat := 1971153644324921879745649

theorem tailTrace_3838808 : CollatzResearch.WordTrace tailWord_3838808 prefixEnd_3838808 1971153644324921879745649 := by
  unfold tailWord_3838808
  simp only [CollatzResearch.WordTrace]
  refine ⟨70006415138330853527618539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93341886851107804703491385 70006415138330853527618539)
  ·
    refine ⟨105009622707496280291427809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70006415138330853527618539 105009622707496280291427809)
    ·
      refine ⟨78757217030622210218570857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105009622707496280291427809 78757217030622210218570857)
      ·
        refine ⟨59067912772966657663928143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78757217030622210218570857 59067912772966657663928143)
        ·
          refine ⟨88601869159449986495892215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59067912772966657663928143 88601869159449986495892215)
          ·
            refine ⟨132902803739174979743838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88601869159449986495892215 132902803739174979743838323)
            ·
              refine ⟨199354205608762469615757485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132902803739174979743838323 199354205608762469615757485)
              ·
                refine ⟨74757827103285926105909057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199354205608762469615757485 74757827103285926105909057)
                ·
                  refine ⟨56068370327464444579431793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74757827103285926105909057 56068370327464444579431793)
                  ·
                    refine ⟨42051277745598333434573845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56068370327464444579431793 42051277745598333434573845)
                    ·
                      refine ⟨1971153644324921879745649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42051277745598333434573845 1971153644324921879745649)
                      ·
                        rfl

theorem cell23_3838808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3838808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838808 prefixEnd_3838808 := by exact prefixLift 3838808
  have htrace : WordTrace (prefixWord ++ tailWord_3838808) baseStart_3838808 baseEnd_3838808 := by
    simpa [prefixWord, tailWord_3838808, baseEnd_3838808] using wordTrace_append hprefix tailTrace_3838808
  have hstable : (prefixWord ++ tailWord_3838808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838808).length < 2 ^ (prefixWord ++ tailWord_3838808).sum := by decide
  have hdescent : baseEnd_3838808 < baseStart_3838808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838812 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3838812 : Nat := 118140960795 + 3838812 * 2 ^ 59
def prefixEnd_3838812 : Nat := 4983230072969 + 3 ^ 40 * 3838812 * 2
def baseEnd_3838812 : Nat := 1971155698247539864095631

theorem tailTrace_3838812 : CollatzResearch.WordTrace tailWord_3838812 prefixEnd_3838812 1971155698247539864095631 := by
  unfold tailWord_3838812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70006488084323607869191345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93341984112431477158921793 70006488084323607869191345)
  ·
    refine ⟨52504866063242705901893509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70006488084323607869191345 52504866063242705901893509)
    ·
      refine ⟨9844662386858007356605033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52504866063242705901893509 9844662386858007356605033)
      ·
        refine ⟨7383496790143505517453775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9844662386858007356605033 7383496790143505517453775)
        ·
          refine ⟨11075245185215258276180663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383496790143505517453775 11075245185215258276180663)
          ·
            refine ⟨16612867777822887414270995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075245185215258276180663 16612867777822887414270995)
            ·
              refine ⟨24919301666734331121406493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16612867777822887414270995 24919301666734331121406493)
              ·
                refine ⟨9344738125025374170527435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24919301666734331121406493 9344738125025374170527435)
                ·
                  refine ⟨14017107187538061255791153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344738125025374170527435 14017107187538061255791153)
                  ·
                    refine ⟨10512830390653545941843365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14017107187538061255791153 10512830390653545941843365)
                    ·
                      refine ⟨1971155698247539864095631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10512830390653545941843365 1971155698247539864095631)
                      ·
                        rfl

theorem cell23_3838812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3838812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838812 prefixEnd_3838812 := by exact prefixLift 3838812
  have htrace : WordTrace (prefixWord ++ tailWord_3838812) baseStart_3838812 baseEnd_3838812 := by
    simpa [prefixWord, tailWord_3838812, baseEnd_3838812] using wordTrace_append hprefix tailTrace_3838812
  have hstable : (prefixWord ++ tailWord_3838812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838812).length < 2 ^ (prefixWord ++ tailWord_3838812).sum := by decide
  have hdescent : baseEnd_3838812 < baseStart_3838812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838850 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3838850 : Nat := 118140960795 + 3838850 * 2 ^ 59
def prefixEnd_3838850 : Nat := 4983230072969 + 3 ^ 40 * 3838850 * 2
def baseEnd_3838850 : Nat := 1971175210512410715420457

theorem tailTrace_3838850 : CollatzResearch.WordTrace tailWord_3838850 prefixEnd_3838850 1971175210512410715420457 := by
  unfold tailWord_3838850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35003590535627387057066501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93342908095006365485510669 35003590535627387057066501)
  ·
    refine ⟨6563173225430135073199969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35003590535627387057066501 6563173225430135073199969)
    ·
      refine ⟨4922379919072601304899977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6563173225430135073199969 4922379919072601304899977)
      ·
        refine ⟨3691784939304450978674983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922379919072601304899977 3691784939304450978674983)
        ·
          refine ⟨5537677408956676468012475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691784939304450978674983 5537677408956676468012475)
          ·
            refine ⟨8306516113435014702018713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537677408956676468012475 8306516113435014702018713)
            ·
              refine ⟨6229887085076261026514035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8306516113435014702018713 6229887085076261026514035)
              ·
                refine ⟨9344830627614391539771053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229887085076261026514035 9344830627614391539771053)
                ·
                  refine ⟨3504311485355396827414145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9344830627614391539771053 3504311485355396827414145)
                  ·
                    refine ⟨2628233614016547620560609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3504311485355396827414145 2628233614016547620560609)
                    ·
                      refine ⟨1971175210512410715420457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628233614016547620560609 1971175210512410715420457)
                      ·
                        rfl

theorem cell23_3838850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3838850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838850 prefixEnd_3838850 := by exact prefixLift 3838850
  have htrace : WordTrace (prefixWord ++ tailWord_3838850) baseStart_3838850 baseEnd_3838850 := by
    simpa [prefixWord, tailWord_3838850, baseEnd_3838850] using wordTrace_append hprefix tailTrace_3838850
  have hstable : (prefixWord ++ tailWord_3838850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838850).length < 2 ^ (prefixWord ++ tailWord_3838850).sum := by decide
  have hdescent : baseEnd_3838850 < baseStart_3838850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838866 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3838866 : Nat := 118140960795 + 3838866 * 2 ^ 59
def prefixEnd_3838866 : Nat := 4983230072969 + 3 ^ 40 * 3838866 * 2
def baseEnd_3838866 : Nat := 1971183426202882652820383

theorem tailTrace_3838866 : CollatzResearch.WordTrace tailWord_3838866 prefixEnd_3838866 1971183426202882652820383 := by
  unfold tailWord_3838866
  simp only [CollatzResearch.WordTrace]
  refine ⟨35003736427612895740212113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93343297140301055307232301 35003736427612895740212113)
  ·
    refine ⟨26252802320709671805159085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35003736427612895740212113 26252802320709671805159085)
    ·
      refine ⟨9844800870266126926934657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26252802320709671805159085 9844800870266126926934657)
      ·
        refine ⟨7383600652699595195200993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9844800870266126926934657 7383600652699595195200993)
        ·
          refine ⟨5537700489524696396400745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7383600652699595195200993 5537700489524696396400745)
          ·
            refine ⟨4153275367143522297300559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537700489524696396400745 4153275367143522297300559)
            ·
              refine ⟨6229913050715283445950839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153275367143522297300559 6229913050715283445950839)
              ·
                refine ⟨9344869576072925168926259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229913050715283445950839 9344869576072925168926259)
                ·
                  refine ⟨14017304364109387753389389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344869576072925168926259 14017304364109387753389389)
                  ·
                    refine ⟨5256489136541020407521021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14017304364109387753389389 5256489136541020407521021)
                    ·
                      refine ⟨1971183426202882652820383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5256489136541020407521021 1971183426202882652820383)
                      ·
                        rfl

theorem cell23_3838866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3838866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838866 prefixEnd_3838866 := by exact prefixLift 3838866
  have htrace : WordTrace (prefixWord ++ tailWord_3838866) baseStart_3838866 baseEnd_3838866 := by
    simpa [prefixWord, tailWord_3838866, baseEnd_3838866] using wordTrace_append hprefix tailTrace_3838866
  have hstable : (prefixWord ++ tailWord_3838866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838866).length < 2 ^ (prefixWord ++ tailWord_3838866).sum := by decide
  have hdescent : baseEnd_3838866 < baseStart_3838866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838912 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 7]
def baseStart_3838912 : Nat := 118140960795 + 3838912 * 2 ^ 59
def prefixEnd_3838912 : Nat := 4983230072969 + 3 ^ 40 * 3838912 * 2
def baseEnd_3838912 : Nat := 219023005145887719205019

theorem tailTrace_3838912 : CollatzResearch.WordTrace tailWord_3838912 prefixEnd_3838912 219023005145887719205019 := by
  unfold tailWord_3838912
  simp only [CollatzResearch.WordTrace]
  refine ⟨70008311734142466408511495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93344415645523288544681993 70008311734142466408511495)
  ·
    refine ⟨105012467601213699612767243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70008311734142466408511495 105012467601213699612767243)
    ·
      refine ⟨157518701401820549419150865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105012467601213699612767243 157518701401820549419150865)
      ·
        refine ⟨118139026051365412064363149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157518701401820549419150865 118139026051365412064363149)
        ·
          refine ⟨44302134769262029524136181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118139026051365412064363149 44302134769262029524136181)
          ·
            refine ⟨4153325134618315267887767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44302134769262029524136181 4153325134618315267887767)
            ·
              refine ⟨6229987701927472901831651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153325134618315267887767 6229987701927472901831651)
              ·
                refine ⟨9344981552891209352747477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229987701927472901831651 9344981552891209352747477)
                ·
                  refine ⟨219023005145887719205019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9344981552891209352747477 219023005145887719205019)
                  ·
                    rfl

theorem cell23_3838912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_3838912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838912 prefixEnd_3838912 := by exact prefixLift 3838912
  have htrace : WordTrace (prefixWord ++ tailWord_3838912) baseStart_3838912 baseEnd_3838912 := by
    simpa [prefixWord, tailWord_3838912, baseEnd_3838912] using wordTrace_append hprefix tailTrace_3838912
  have hstable : (prefixWord ++ tailWord_3838912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838912).length < 2 ^ (prefixWord ++ tailWord_3838912).sum := by decide
  have hdescent : baseEnd_3838912 < baseStart_3838912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838923 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 2, 2, 2]
def baseStart_3838923 : Nat := 118140960795 + 3838923 * 2 ^ 59
def prefixEnd_3838923 : Nat := 4983230072969 + 3 ^ 40 * 3838923 * 2
def baseEnd_3838923 : Nat := 1971212694600188929807621

theorem tailTrace_3838923 : CollatzResearch.WordTrace tailWord_3838923 prefixEnd_3838923 1971212694600188929807621 := by
  unfold tailWord_3838923
  simp only [CollatzResearch.WordTrace]
  refine ⟨140017024671245081695673423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93344683114163387797115615 140017024671245081695673423)
  ·
    refine ⟨210025537006867622543510135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140017024671245081695673423 210025537006867622543510135)
    ·
      refine ⟨315038305510301433815265203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210025537006867622543510135 315038305510301433815265203)
      ·
        refine ⟨472557458265452150722897805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315038305510301433815265203 472557458265452150722897805)
        ·
          refine ⟨177209046849544556521086677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472557458265452150722897805 177209046849544556521086677)
          ·
            refine ⟨4153337035536200543462969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177209046849544556521086677 4153337035536200543462969)
            ·
              refine ⟨3115002776652150407597227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153337035536200543462969 3115002776652150407597227)
              ·
                refine ⟨4672504164978225611395841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115002776652150407597227 4672504164978225611395841)
                ·
                  refine ⟨3504378123733669208546881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672504164978225611395841 3504378123733669208546881)
                  ·
                    refine ⟨2628283592800251906410161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3504378123733669208546881 2628283592800251906410161)
                    ·
                      refine ⟨1971212694600188929807621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628283592800251906410161 1971212694600188929807621)
                      ·
                        rfl

theorem cell23_3838923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 2, 2].length) (baseStart_3838923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838923 prefixEnd_3838923 := by exact prefixLift 3838923
  have htrace : WordTrace (prefixWord ++ tailWord_3838923) baseStart_3838923 baseEnd_3838923 := by
    simpa [prefixWord, tailWord_3838923, baseEnd_3838923] using wordTrace_append hprefix tailTrace_3838923
  have hstable : (prefixWord ++ tailWord_3838923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838923).length < 2 ^ (prefixWord ++ tailWord_3838923).sum := by decide
  have hdescent : baseEnd_3838923 < baseStart_3838923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838975 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_3838975 : Nat := 118140960795 + 3838975 * 2 ^ 59
def prefixEnd_3838975 : Nat := 4983230072969 + 3 ^ 40 * 3838975 * 2
def baseEnd_3838975 : Nat := 1971239395594222726357381

theorem tailTrace_3838975 : CollatzResearch.WordTrace tailWord_3838975 prefixEnd_3838975 1971239395594222726357381 := by
  unfold tailWord_3838975
  simp only [CollatzResearch.WordTrace]
  refine ⟨140018921267056694576566379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93345947511371129717710919 140018921267056694576566379)
  ·
    refine ⟨210028381900585041864849569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140018921267056694576566379 210028381900585041864849569)
    ·
      refine ⟨157521286425438781398637177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210028381900585041864849569 157521286425438781398637177)
      ·
        refine ⟨118140964819079086048977883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157521286425438781398637177 118140964819079086048977883)
        ·
          refine ⟨177211447228618629073466825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118140964819079086048977883 177211447228618629073466825)
          ·
            refine ⟨132908585421463971805100119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177211447228618629073466825 132908585421463971805100119)
            ·
              refine ⟨199362878132195957707650179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132908585421463971805100119 199362878132195957707650179)
              ·
                refine ⟨299044317198293936561475269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199362878132195957707650179 299044317198293936561475269)
                ·
                  refine ⟨56070809474680113105276613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299044317198293936561475269 56070809474680113105276613)
                  ·
                    refine ⟨10513276776502521207239365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56070809474680113105276613 10513276776502521207239365)
                    ·
                      refine ⟨1971239395594222726357381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10513276776502521207239365 1971239395594222726357381)
                      ·
                        rfl

theorem cell23_3838975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_3838975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838975 prefixEnd_3838975 := by exact prefixLift 3838975
  have htrace : WordTrace (prefixWord ++ tailWord_3838975) baseStart_3838975 baseEnd_3838975 := by
    simpa [prefixWord, tailWord_3838975, baseEnd_3838975] using wordTrace_append hprefix tailTrace_3838975
  have hstable : (prefixWord ++ tailWord_3838975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838975).length < 2 ^ (prefixWord ++ tailWord_3838975).sum := by decide
  have hdescent : baseEnd_3838975 < baseStart_3838975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3838999 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3838999 : Nat := 118140960795 + 3838999 * 2 ^ 59
def prefixEnd_3838999 : Nat := 4983230072969 + 3 ^ 40 * 3838999 * 2
def baseEnd_3838999 : Nat := 1971251719129930632457271

theorem tailTrace_3838999 : CollatzResearch.WordTrace tailWord_3838999 prefixEnd_3838999 1971251719129930632457271 := by
  unfold tailWord_3838999
  simp only [CollatzResearch.WordTrace]
  refine ⟨140019796618969746675440051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93346531079313164450293367 140019796618969746675440051)
  ·
    refine ⟨210029694928454620013160077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140019796618969746675440051 210029694928454620013160077)
    ·
      refine ⟨78761135598170482504935029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210029694928454620013160077 78761135598170482504935029)
      ·
        refine ⟨7383856462328482734837659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78761135598170482504935029 7383856462328482734837659)
        ·
          refine ⟨11075784693492724102256489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383856462328482734837659 11075784693492724102256489)
          ·
            refine ⟨8306838520119543076692367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11075784693492724102256489 8306838520119543076692367)
            ·
              refine ⟨12460257780179314615038551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306838520119543076692367 12460257780179314615038551)
              ·
                refine ⟨18690386670268971922557827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12460257780179314615038551 18690386670268971922557827)
                ·
                  refine ⟨28035580005403457883836741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18690386670268971922557827 28035580005403457883836741)
                  ·
                    refine ⟨5256671251013148353219389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28035580005403457883836741 5256671251013148353219389)
                    ·
                      refine ⟨1971251719129930632457271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5256671251013148353219389 1971251719129930632457271)
                      ·
                        rfl

theorem cell23_3838999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3838999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3838999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3838999 prefixEnd_3838999 := by exact prefixLift 3838999
  have htrace : WordTrace (prefixWord ++ tailWord_3838999) baseStart_3838999 baseEnd_3838999 := by
    simpa [prefixWord, tailWord_3838999, baseEnd_3838999] using wordTrace_append hprefix tailTrace_3838999
  have hstable : (prefixWord ++ tailWord_3838999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3838999).length < 2 ^ (prefixWord ++ tailWord_3838999).sum := by decide
  have hdescent : baseEnd_3838999 < baseStart_3838999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3838999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839022 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3839022 : Nat := 118140960795 + 3839022 * 2 ^ 59
def prefixEnd_3839022 : Nat := 4983230072969 + 3 ^ 40 * 3839022 * 2
def baseEnd_3839022 : Nat := 1971263529184984042469665

theorem tailTrace_3839022 : CollatzResearch.WordTrace tailWord_3839022 prefixEnd_3839022 1971263529184984042469665 := by
  unfold tailWord_3839022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17502579437235802700440915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93347090331924281069018213 17502579437235802700440915)
  ·
    refine ⟨26253869155853704050661373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17502579437235802700440915 26253869155853704050661373)
    ·
      refine ⟨9845200933445139018998015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26253869155853704050661373 9845200933445139018998015)
      ·
        refine ⟨14767801400167708528497023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9845200933445139018998015 14767801400167708528497023)
        ·
          refine ⟨22151702100251562792745535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14767801400167708528497023 22151702100251562792745535)
          ·
            refine ⟨33227553150377344189118303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22151702100251562792745535 33227553150377344189118303)
            ·
              refine ⟨49841329725566016283677455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33227553150377344189118303 49841329725566016283677455)
              ·
                refine ⟨74761994588349024425516183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49841329725566016283677455 74761994588349024425516183)
                ·
                  refine ⟨112142991882523536638274275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74761994588349024425516183 112142991882523536638274275)
                  ·
                    refine ⟨168214487823785304957411413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112142991882523536638274275 168214487823785304957411413)
                    ·
                      refine ⟨1971263529184984042469665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168214487823785304957411413 1971263529184984042469665)
                      ·
                        rfl

theorem cell23_3839022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3839022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839022 prefixEnd_3839022 := by exact prefixLift 3839022
  have htrace : WordTrace (prefixWord ++ tailWord_3839022) baseStart_3839022 baseEnd_3839022 := by
    simpa [prefixWord, tailWord_3839022, baseEnd_3839022] using wordTrace_append hprefix tailTrace_3839022
  have hstable : (prefixWord ++ tailWord_3839022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839022).length < 2 ^ (prefixWord ++ tailWord_3839022).sum := by decide
  have hdescent : baseEnd_3839022 < baseStart_3839022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839079 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3839079 : Nat := 118140960795 + 3839079 * 2 ^ 59
def prefixEnd_3839079 : Nat := 4983230072969 + 3 ^ 40 * 3839079 * 2
def baseEnd_3839079 : Nat := 657097599194096773152301

theorem tailTrace_3839079 : CollatzResearch.WordTrace tailWord_3839079 prefixEnd_3839079 657097599194096773152301 := by
  unfold tailWord_3839079
  simp only [CollatzResearch.WordTrace]
  refine ⟨140022714458679920338352291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93348476305786613558901527 140022714458679920338352291)
  ·
    refine ⟨210034071688019880507528437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140022714458679920338352291 210034071688019880507528437)
    ·
      refine ⟨19690694220751863797580791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210034071688019880507528437 19690694220751863797580791)
      ·
        refine ⟨29536041331127795696371187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19690694220751863797580791 29536041331127795696371187)
        ·
          refine ⟨44304061996691693544556781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29536041331127795696371187 44304061996691693544556781)
          ·
            refine ⟨16614023248759385079208793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44304061996691693544556781 16614023248759385079208793)
            ·
              refine ⟨12460517436569538809406595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16614023248759385079208793 12460517436569538809406595)
              ·
                refine ⟨18690776154854308214109893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12460517436569538809406595 18690776154854308214109893)
                ·
                  refine ⟨3504520529035182790145605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18690776154854308214109893 3504520529035182790145605)
                  ·
                    refine ⟨657097599194096773152301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3504520529035182790145605 657097599194096773152301)
                    ·
                      rfl

theorem cell23_3839079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3839079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839079 prefixEnd_3839079 := by exact prefixLift 3839079
  have htrace : WordTrace (prefixWord ++ tailWord_3839079) baseStart_3839079 baseEnd_3839079 := by
    simpa [prefixWord, tailWord_3839079, baseEnd_3839079] using wordTrace_append hprefix tailTrace_3839079
  have hstable : (prefixWord ++ tailWord_3839079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839079).length < 2 ^ (prefixWord ++ tailWord_3839079).sum := by decide
  have hdescent : baseEnd_3839079 < baseStart_3839079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839080 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3839080 : Nat := 118140960795 + 3839080 * 2 ^ 59
def prefixEnd_3839080 : Nat := 4983230072969 + 3 ^ 40 * 3839080 * 2
def baseEnd_3839080 : Nat := 1971293311062944815544399

theorem tailTrace_3839080 : CollatzResearch.WordTrace tailWord_3839080 prefixEnd_3839080 1971293311062944815544399 := by
  unfold tailWord_3839080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70011375465838148754569347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93348500621117531672759129 70011375465838148754569347)
  ·
    refine ⟨105017063198757223131854021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70011375465838148754569347 105017063198757223131854021)
    ·
      refine ⟨19690699349766979337222629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105017063198757223131854021 19690699349766979337222629)
      ·
        refine ⟨3692006128081308625729243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19690699349766979337222629 3692006128081308625729243)
        ·
          refine ⟨5538009192121962938593865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692006128081308625729243 5538009192121962938593865)
          ·
            refine ⟨4153506894091472203945399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538009192121962938593865 4153506894091472203945399)
            ·
              refine ⟨6230260341137208305918099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153506894091472203945399 6230260341137208305918099)
              ·
                refine ⟨9345390511705812458877149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230260341137208305918099 9345390511705812458877149)
                ·
                  refine ⟨3504521441889679672078931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9345390511705812458877149 3504521441889679672078931)
                  ·
                    refine ⟨5256782162834519508118397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3504521441889679672078931 5256782162834519508118397)
                    ·
                      refine ⟨1971293311062944815544399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5256782162834519508118397 1971293311062944815544399)
                      ·
                        rfl

theorem cell23_3839080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3839080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839080 prefixEnd_3839080 := by exact prefixLift 3839080
  have htrace : WordTrace (prefixWord ++ tailWord_3839080) baseStart_3839080 baseEnd_3839080 := by
    simpa [prefixWord, tailWord_3839080, baseEnd_3839080] using wordTrace_append hprefix tailTrace_3839080
  have hstable : (prefixWord ++ tailWord_3839080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839080).length < 2 ^ (prefixWord ++ tailWord_3839080).sum := by decide
  have hdescent : baseEnd_3839080 < baseStart_3839080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839096 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 2, 4]
def baseStart_3839096 : Nat := 118140960795 + 3839096 * 2 ^ 59
def prefixEnd_3839096 : Nat := 4983230072969 + 3 ^ 40 * 3839096 * 2
def baseEnd_3839096 : Nat := 657100508917805584314775

theorem tailTrace_3839096 : CollatzResearch.WordTrace tailWord_3839096 prefixEnd_3839096 657100508917805584314775 := by
  unfold tailWord_3839096
  simp only [CollatzResearch.WordTrace]
  refine ⟨70011667249809166120860571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93348889666412221494480761 70011667249809166120860571)
  ·
    refine ⟨105017500874713749181290857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70011667249809166120860571 105017500874713749181290857)
    ·
      refine ⟨78763125656035311885968143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105017500874713749181290857 78763125656035311885968143)
      ·
        refine ⟨118144688484052967828952215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78763125656035311885968143 118144688484052967828952215)
        ·
          refine ⟨177217032726079451743428323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118144688484052967828952215 177217032726079451743428323)
          ·
            refine ⟨265825549089119177615142485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177217032726079451743428323 265825549089119177615142485)
            ·
              refine ⟨3115143153388115362677451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 265825549089119177615142485 3115143153388115362677451)
              ·
                refine ⟨4672714730082173044016177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115143153388115362677451 4672714730082173044016177)
                ·
                  refine ⟨3504536047561629783012133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672714730082173044016177 3504536047561629783012133)
                  ·
                    refine ⟨657100508917805584314775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3504536047561629783012133 657100508917805584314775)
                    ·
                      rfl

theorem cell23_3839096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_3839096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839096 prefixEnd_3839096 := by exact prefixLift 3839096
  have htrace : WordTrace (prefixWord ++ tailWord_3839096) baseStart_3839096 baseEnd_3839096 := by
    simpa [prefixWord, tailWord_3839096, baseEnd_3839096] using wordTrace_append hprefix tailTrace_3839096
  have hstable : (prefixWord ++ tailWord_3839096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839096).length < 2 ^ (prefixWord ++ tailWord_3839096).sum := by decide
  have hdescent : baseEnd_3839096 < baseStart_3839096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839126 : List Nat := [5, 3, 2, 13]
def baseStart_3839126 : Nat := 118140960795 + 3839126 * 2 ^ 59
def prefixEnd_3839126 : Nat := 4983230072969 + 3 ^ 40 * 3839126 * 2
def baseEnd_3839126 : Nat := 901379483846845741001

theorem tailTrace_3839126 : CollatzResearch.WordTrace tailWord_3839126 prefixEnd_3839126 901379483846845741001 := by
  unfold tailWord_3839126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751526793094352960332077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93349619126339764910208821 8751526793094352960332077)
  ·
    refine ⟨3281822547410382360124529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8751526793094352960332077 3281822547410382360124529)
    ·
      refine ⟨2461366910557786770093397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3281822547410382360124529 2461366910557786770093397)
      ·
        refine ⟨901379483846845741001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2461366910557786770093397 901379483846845741001)
        ·
          rfl

theorem cell23_3839126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 13].length) (baseStart_3839126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839126 prefixEnd_3839126 := by exact prefixLift 3839126
  have htrace : WordTrace (prefixWord ++ tailWord_3839126) baseStart_3839126 baseEnd_3839126 := by
    simpa [prefixWord, tailWord_3839126, baseEnd_3839126] using wordTrace_append hprefix tailTrace_3839126
  have hstable : (prefixWord ++ tailWord_3839126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839126).length < 2 ^ (prefixWord ++ tailWord_3839126).sum := by decide
  have hdescent : baseEnd_3839126 < baseStart_3839126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839152 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_3839152 : Nat := 118140960795 + 3839152 * 2 ^ 59
def prefixEnd_3839152 : Nat := 4983230072969 + 3 ^ 40 * 3839152 * 2
def baseEnd_3839152 : Nat := 657110093890022844614689

theorem tailTrace_3839152 : CollatzResearch.WordTrace tailWord_3839152 prefixEnd_3839152 657110093890022844614689 := by
  unfold tailWord_3839152
  simp only [CollatzResearch.WordTrace]
  refine ⟨70012688493707726902879855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93350251324943635870506473 70012688493707726902879855)
  ·
    refine ⟨105019032740561590354319783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70012688493707726902879855 105019032740561590354319783)
    ·
      refine ⟨157528549110842385531479675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105019032740561590354319783 157528549110842385531479675)
      ·
        refine ⟨236292823666263578297219513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157528549110842385531479675 236292823666263578297219513)
        ·
          refine ⟨177219617749697683722914635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236292823666263578297219513 177219617749697683722914635)
          ·
            refine ⟨265829426624546525584371953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177219617749697683722914635 265829426624546525584371953)
            ·
              refine ⟨199372069968409894188278965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265829426624546525584371953 199372069968409894188278965)
              ·
                refine ⟨18691131559538427580151153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199372069968409894188278965 18691131559538427580151153)
                ·
                  refine ⟨14018348669653820685113365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18691131559538427580151153 14018348669653820685113365)
                  ·
                    refine ⟨657110093890022844614689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14018348669653820685113365 657110093890022844614689)
                    ·
                      rfl

theorem cell23_3839152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_3839152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839152 prefixEnd_3839152 := by exact prefixLift 3839152
  have htrace : WordTrace (prefixWord ++ tailWord_3839152) baseStart_3839152 baseEnd_3839152 := by
    simpa [prefixWord, tailWord_3839152, baseEnd_3839152] using wordTrace_append hprefix tailTrace_3839152
  have hstable : (prefixWord ++ tailWord_3839152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839152).length < 2 ^ (prefixWord ++ tailWord_3839152).sum := by decide
  have hdescent : baseEnd_3839152 < baseStart_3839152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839153 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3839153 : Nat := 118140960795 + 3839153 * 2 ^ 59
def prefixEnd_3839153 : Nat := 4983230072969 + 3 ^ 40 * 3839153 * 2
def baseEnd_3839153 : Nat := 1971330795150723029931563

theorem tailTrace_3839153 : CollatzResearch.WordTrace tailWord_3839153 prefixEnd_3839153 1971330795150723029931563 := by
  unfold tailWord_3839153
  simp only [CollatzResearch.WordTrace]
  refine ⟨140025413460411830976546113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93350275640274553984364075 140025413460411830976546113)
  ·
    refine ⟨105019060095308873232409585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140025413460411830976546113 105019060095308873232409585)
    ·
      refine ⟨78764295071481654924307189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105019060095308873232409585 78764295071481654924307189)
      ·
        refine ⟨7384152662951405149153799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78764295071481654924307189 7384152662951405149153799)
        ·
          refine ⟨11076228994427107723730699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384152662951405149153799 11076228994427107723730699)
          ·
            refine ⟨16614343491640661585596049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11076228994427107723730699 16614343491640661585596049)
            ·
              refine ⟨12460757618730496189197037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16614343491640661585596049 12460757618730496189197037)
              ·
                refine ⟨4672784107023936070948889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12460757618730496189197037 4672784107023936070948889)
                ·
                  refine ⟨3504588080267952053211667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672784107023936070948889 3504588080267952053211667)
                  ·
                    refine ⟨5256882120401928079817501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3504588080267952053211667 5256882120401928079817501)
                    ·
                      refine ⟨1971330795150723029931563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5256882120401928079817501 1971330795150723029931563)
                      ·
                        rfl

theorem cell23_3839153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3839153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839153 prefixEnd_3839153 := by exact prefixLift 3839153
  have htrace : WordTrace (prefixWord ++ tailWord_3839153) baseStart_3839153 baseEnd_3839153 := by
    simpa [prefixWord, tailWord_3839153, baseEnd_3839153] using wordTrace_append hprefix tailTrace_3839153
  have hstable : (prefixWord ++ tailWord_3839153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839153).length < 2 ^ (prefixWord ++ tailWord_3839153).sum := by decide
  have hdescent : baseEnd_3839153 < baseStart_3839153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839176 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_3839176 : Nat := 118140960795 + 3839176 * 2 ^ 59
def prefixEnd_3839176 : Nat := 4983230072969 + 3 ^ 40 * 3839176 * 2
def baseEnd_3839176 : Nat := 1971342605205776439943957

theorem tailTrace_3839176 : CollatzResearch.WordTrace tailWord_3839176 prefixEnd_3839176 1971342605205776439943957 := by
  unfold tailWord_3839176
  simp only [CollatzResearch.WordTrace]
  refine ⟨70013126169664252952316691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93350834892885670603088921 70013126169664252952316691)
  ·
    refine ⟨105019689254496379428475037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70013126169664252952316691 105019689254496379428475037)
    ·
      refine ⟨39382383470436142285678139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105019689254496379428475037 39382383470436142285678139)
      ·
        refine ⟨59073575205654213428517209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39382383470436142285678139 59073575205654213428517209)
        ·
          refine ⟨44305181404240660071387907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59073575205654213428517209 44305181404240660071387907)
          ·
            refine ⟨66457772106360990107081861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44305181404240660071387907 66457772106360990107081861)
            ·
              refine ⟨12460832269942685645077849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66457772106360990107081861 12460832269942685645077849)
              ·
                refine ⟨9345624202457014233808387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12460832269942685645077849 9345624202457014233808387)
                ·
                  refine ⟨14018436303685521350712581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345624202457014233808387 14018436303685521350712581)
                  ·
                    refine ⟨2628456806941035253258609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14018436303685521350712581 2628456806941035253258609)
                    ·
                      refine ⟨1971342605205776439943957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628456806941035253258609 1971342605205776439943957)
                      ·
                        rfl

theorem cell23_3839176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_3839176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839176 prefixEnd_3839176 := by exact prefixLift 3839176
  have htrace : WordTrace (prefixWord ++ tailWord_3839176) baseStart_3839176 baseEnd_3839176 := by
    simpa [prefixWord, tailWord_3839176, baseEnd_3839176] using wordTrace_append hprefix tailTrace_3839176
  have hstable : (prefixWord ++ tailWord_3839176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839176).length < 2 ^ (prefixWord ++ tailWord_3839176).sum := by decide
  have hdescent : baseEnd_3839176 < baseStart_3839176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839233 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 5]
def baseStart_3839233 : Nat := 118140960795 + 3839233 * 2 ^ 59
def prefixEnd_3839233 : Nat := 4983230072969 + 3 ^ 40 * 3839233 * 2
def baseEnd_3839233 : Nat := 219041319289231412992355

theorem tailTrace_3839233 : CollatzResearch.WordTrace tailWord_3839233 prefixEnd_3839233 219041319289231412992355 := by
  unfold tailWord_3839233
  simp only [CollatzResearch.WordTrace]
  refine ⟨140028331300122004639458353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93352220866748003092972235 140028331300122004639458353)
  ·
    refine ⟨105021248475091503479593765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140028331300122004639458353 105021248475091503479593765)
    ·
      refine ⟨19691484089079656902423831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105021248475091503479593765 19691484089079656902423831)
      ·
        refine ⟨29537226133619485353635747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19691484089079656902423831 29537226133619485353635747)
        ·
          refine ⟨44305839200429228030453621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29537226133619485353635747 44305839200429228030453621)
          ·
            refine ⟨4153672425040240127855027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44305839200429228030453621 4153672425040240127855027)
            ·
              refine ⟨6230508637560360191782541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153672425040240127855027 6230508637560360191782541)
              ·
                refine ⟨2336440739085135071918453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6230508637560360191782541 2336440739085135071918453)
                ·
                  refine ⟨219041319289231412992355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2336440739085135071918453 219041319289231412992355)
                  ·
                    rfl

theorem cell23_3839233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 5].length) (baseStart_3839233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839233 prefixEnd_3839233 := by exact prefixLift 3839233
  have htrace : WordTrace (prefixWord ++ tailWord_3839233) baseStart_3839233 baseEnd_3839233 := by
    simpa [prefixWord, tailWord_3839233, baseEnd_3839233] using wordTrace_append hprefix tailTrace_3839233
  have hstable : (prefixWord ++ tailWord_3839233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839233).length < 2 ^ (prefixWord ++ tailWord_3839233).sum := by decide
  have hdescent : baseEnd_3839233 < baseStart_3839233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839246 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_3839246 : Nat := 118140960795 + 3839246 * 2 ^ 59
def prefixEnd_3839246 : Nat := 4983230072969 + 3 ^ 40 * 3839246 * 2
def baseEnd_3839246 : Nat := 657126182950530388689545

theorem tailTrace_3839246 : CollatzResearch.WordTrace tailWord_3839246 prefixEnd_3839246 657126182950530388689545 := by
  unfold tailWord_3839246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503600681134363482460199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93352536966049938573121061 17503600681134363482460199)
  ·
    refine ⟨26255401021701545223690299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17503600681134363482460199 26255401021701545223690299)
    ·
      refine ⟨39383101532552317835535449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26255401021701545223690299 39383101532552317835535449)
      ·
        refine ⟨29537326149414238376651587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39383101532552317835535449 29537326149414238376651587)
        ·
          refine ⟨44305989224121357564977381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29537326149414238376651587 44305989224121357564977381)
          ·
            refine ⟨8307372979522754543433259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44305989224121357564977381 8307372979522754543433259)
            ·
              refine ⟨12461059469284131815149889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307372979522754543433259 12461059469284131815149889)
              ·
                refine ⟨9345794601963098861362417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12461059469284131815149889 9345794601963098861362417)
                ·
                  refine ⟨7009345951472324146021813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9345794601963098861362417 7009345951472324146021813)
                  ·
                    refine ⟨657126182950530388689545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7009345951472324146021813 657126182950530388689545)
                    ·
                      rfl

theorem cell23_3839246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_3839246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839246 prefixEnd_3839246 := by exact prefixLift 3839246
  have htrace : WordTrace (prefixWord ++ tailWord_3839246) baseStart_3839246 baseEnd_3839246 := by
    simpa [prefixWord, tailWord_3839246, baseEnd_3839246] using wordTrace_append hprefix tailTrace_3839246
  have hstable : (prefixWord ++ tailWord_3839246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839246).length < 2 ^ (prefixWord ++ tailWord_3839246).sum := by decide
  have hdescent : baseEnd_3839246 < baseStart_3839246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839250 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_3839250 : Nat := 118140960795 + 3839250 * 2 ^ 59
def prefixEnd_3839250 : Nat := 4983230072969 + 3 ^ 40 * 3839250 * 2
def baseEnd_3839250 : Nat := 219042289197134350046513

theorem tailTrace_3839250 : CollatzResearch.WordTrace tailWord_3839250 prefixEnd_3839250 219042289197134350046513 := by
  unfold tailWord_3839250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35007237835265104135706801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93352634227373611028551469 35007237835265104135706801)
  ·
    refine ⟨26255428376448828101780101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35007237835265104135706801 26255428376448828101780101)
    ·
      refine ⟨4922892820584155269083769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26255428376448828101780101 4922892820584155269083769)
      ·
        refine ⟨3692169615438116451812827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922892820584155269083769 3692169615438116451812827)
        ·
          refine ⟨5538254423157174677719241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692169615438116451812827 5538254423157174677719241)
          ·
            refine ⟨4153690817367881008289431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538254423157174677719241 4153690817367881008289431)
            ·
              refine ⟨6230536226051821512434147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153690817367881008289431 6230536226051821512434147)
              ·
                refine ⟨9345804339077732268651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230536226051821512434147 9345804339077732268651221)
                ·
                  refine ⟨219042289197134350046513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9345804339077732268651221 219042289197134350046513)
                  ·
                    rfl

theorem cell23_3839250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_3839250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839250 prefixEnd_3839250 := by exact prefixLift 3839250
  have htrace : WordTrace (prefixWord ++ tailWord_3839250) baseStart_3839250 baseEnd_3839250 := by
    simpa [prefixWord, tailWord_3839250, baseEnd_3839250] using wordTrace_append hprefix tailTrace_3839250
  have hstable : (prefixWord ++ tailWord_3839250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839250).length < 2 ^ (prefixWord ++ tailWord_3839250).sum := by decide
  have hdescent : baseEnd_3839250 < baseStart_3839250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839333 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3839333 : Nat := 118140960795 + 3839333 * 2 ^ 59
def prefixEnd_3839333 : Nat := 4983230072969 + 3 ^ 40 * 3839333 * 2
def baseEnd_3839333 : Nat := 1971423221668532325680735

theorem tailTrace_3839333 : CollatzResearch.WordTrace tailWord_3839333 prefixEnd_3839333 1971423221668532325680735 := by
  unfold tailWord_3839333
  simp only [CollatzResearch.WordTrace]
  refine ⟨140031978599759721718098653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93354652399839814478732435 140031978599759721718098653)
  ·
    refine ⟨52511991974909895644286995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140031978599759721718098653 52511991974909895644286995)
    ·
      refine ⟨78767987962364843466430493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52511991974909895644286995 78767987962364843466430493)
      ·
        refine ⟨29537995485886816299911435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78767987962364843466430493 29537995485886816299911435)
        ·
          refine ⟨44306993228830224449867153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29537995485886816299911435 44306993228830224449867153)
          ·
            refine ⟨33230244921622668337400365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44306993228830224449867153 33230244921622668337400365)
            ·
              refine ⟨12461341845608500626525137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33230244921622668337400365 12461341845608500626525137)
              ·
                refine ⟨9346006384206375469893853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12461341845608500626525137 9346006384206375469893853)
                ·
                  refine ⟨3504752394077390801210195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9346006384206375469893853 3504752394077390801210195)
                  ·
                    refine ⟨5257128591116086201815293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3504752394077390801210195 5257128591116086201815293)
                    ·
                      refine ⟨1971423221668532325680735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5257128591116086201815293 1971423221668532325680735)
                      ·
                        rfl

theorem cell23_3839333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3839333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839333 prefixEnd_3839333 := by exact prefixLift 3839333
  have htrace : WordTrace (prefixWord ++ tailWord_3839333) baseStart_3839333 baseEnd_3839333 := by
    simpa [prefixWord, tailWord_3839333, baseEnd_3839333] using wordTrace_append hprefix tailTrace_3839333
  have hstable : (prefixWord ++ tailWord_3839333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839333).length < 2 ^ (prefixWord ++ tailWord_3839333).sum := by decide
  have hdescent : baseEnd_3839333 < baseStart_3839333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839353 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 1, 5]
def baseStart_3839353 : Nat := 118140960795 + 3839353 * 2 ^ 59
def prefixEnd_3839353 : Nat := 4983230072969 + 3 ^ 40 * 3839353 * 2
def baseEnd_3839353 : Nat := 657144497093874082476881

theorem tailTrace_3839353 : CollatzResearch.WordTrace tailWord_3839353 prefixEnd_3839353 657144497093874082476881 := by
  unfold tailWord_3839353
  simp only [CollatzResearch.WordTrace]
  refine ⟨140032708059687265133826713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93355138706458176755884475 140032708059687265133826713)
  ·
    refine ⟨105024531044765448850370035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140032708059687265133826713 105024531044765448850370035)
    ·
      refine ⟨157536796567148173275555053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105024531044765448850370035 157536796567148173275555053)
      ·
        refine ⟨59076298712680564978333145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157536796567148173275555053 59076298712680564978333145)
        ·
          refine ⟨44307224034510423733749859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59076298712680564978333145 44307224034510423733749859)
          ·
            refine ⟨66460836051765635600624789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44307224034510423733749859 66460836051765635600624789)
            ·
              refine ⟨3115351689926514168779287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66460836051765635600624789 3115351689926514168779287)
              ·
                refine ⟨4673027534889771253168931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115351689926514168779287 4673027534889771253168931)
                ·
                  refine ⟨7009541302334656879753397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673027534889771253168931 7009541302334656879753397)
                  ·
                    refine ⟨657144497093874082476881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7009541302334656879753397 657144497093874082476881)
                    ·
                      rfl

theorem cell23_3839353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_3839353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839353 prefixEnd_3839353 := by exact prefixLift 3839353
  have htrace : WordTrace (prefixWord ++ tailWord_3839353) baseStart_3839353 baseEnd_3839353 := by
    simpa [prefixWord, tailWord_3839353, baseEnd_3839353] using wordTrace_append hprefix tailTrace_3839353
  have hstable : (prefixWord ++ tailWord_3839353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839353).length < 2 ^ (prefixWord ++ tailWord_3839353).sum := by decide
  have hdescent : baseEnd_3839353 < baseStart_3839353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839386 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3839386 : Nat := 118140960795 + 3839386 * 2 ^ 59
def prefixEnd_3839386 : Nat := 4983230072969 + 3 ^ 40 * 3839386 * 2
def baseEnd_3839386 : Nat := 1971450436143220618317991

theorem tailTrace_3839386 : CollatzResearch.WordTrace tailWord_3839386 prefixEnd_3839386 1971450436143220618317991 := by
  unfold tailWord_3839386
  simp only [CollatzResearch.WordTrace]
  refine ⟨35008477917141927942444503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93355941112378474513185341 35008477917141927942444503)
  ·
    refine ⟨52512716875712891913666755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35008477917141927942444503 52512716875712891913666755)
    ·
      refine ⟨78769075313569337870500133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52512716875712891913666755 78769075313569337870500133)
      ·
        refine ⟨14769201621294250850718775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78769075313569337870500133 14769201621294250850718775)
        ·
          refine ⟨22153802431941376276078163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769201621294250850718775 22153802431941376276078163)
          ·
            refine ⟨33230703647912064414117245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22153802431941376276078163 33230703647912064414117245)
            ·
              refine ⟨12461513867967024155293967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33230703647912064414117245 12461513867967024155293967)
              ·
                refine ⟨18692270801950536232940951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12461513867967024155293967 18692270801950536232940951)
                ·
                  refine ⟨28038406202925804349411427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18692270801950536232940951 28038406202925804349411427)
                  ·
                    refine ⟨42057609304388706524117141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28038406202925804349411427 42057609304388706524117141)
                    ·
                      refine ⟨1971450436143220618317991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42057609304388706524117141 1971450436143220618317991)
                      ·
                        rfl

theorem cell23_3839386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3839386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839386 prefixEnd_3839386 := by exact prefixLift 3839386
  have htrace : WordTrace (prefixWord ++ tailWord_3839386) baseStart_3839386 baseEnd_3839386 := by
    simpa [prefixWord, tailWord_3839386, baseEnd_3839386] using wordTrace_append hprefix tailTrace_3839386
  have hstable : (prefixWord ++ tailWord_3839386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839386).length < 2 ^ (prefixWord ++ tailWord_3839386).sum := by decide
  have hdescent : baseEnd_3839386 < baseStart_3839386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839419 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_3839419 : Nat := 118140960795 + 3839419 * 2 ^ 59
def prefixEnd_3839419 : Nat := 4983230072969 + 3 ^ 40 * 3839419 * 2
def baseEnd_3839419 : Nat := 1971467381004818989205339

theorem tailTrace_3839419 : CollatzResearch.WordTrace tailWord_3839419 prefixEnd_3839419 1971467381004818989205339 := by
  unfold tailWord_3839419
  simp only [CollatzResearch.WordTrace]
  refine ⟨140035115277448158405729311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93356743518298772270486207 140035115277448158405729311)
  ·
    refine ⟨210052672916172237608593967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140035115277448158405729311 210052672916172237608593967)
    ·
      refine ⟨315079009374258356412890951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210052672916172237608593967 315079009374258356412890951)
      ·
        refine ⟨472618514061387534619336427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315079009374258356412890951 472618514061387534619336427)
        ·
          refine ⟨708927771092081301929004641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472618514061387534619336427 708927771092081301929004641)
          ·
            refine ⟨531695828319060976446753481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708927771092081301929004641 531695828319060976446753481)
            ·
              refine ⟨398771871239295732335065111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531695828319060976446753481 398771871239295732335065111)
              ·
                refine ⟨598157806858943598502597667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398771871239295732335065111 598157806858943598502597667)
                ·
                  refine ⟨897236710288415397753896501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598157806858943598502597667 897236710288415397753896501)
                  ·
                    refine ⟨84115941589538943539427797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 897236710288415397753896501 84115941589538943539427797)
                    ·
                      refine ⟨1971467381004818989205339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84115941589538943539427797 1971467381004818989205339)
                      ·
                        rfl

theorem cell23_3839419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_3839419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839419 prefixEnd_3839419 := by exact prefixLift 3839419
  have htrace : WordTrace (prefixWord ++ tailWord_3839419) baseStart_3839419 baseEnd_3839419 := by
    simpa [prefixWord, tailWord_3839419, baseEnd_3839419] using wordTrace_append hprefix tailTrace_3839419
  have hstable : (prefixWord ++ tailWord_3839419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839419).length < 2 ^ (prefixWord ++ tailWord_3839419).sum := by decide
  have hdescent : baseEnd_3839419 < baseStart_3839419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839433 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 3, 3, 2]
def baseStart_3839433 : Nat := 118140960795 + 3839433 * 2 ^ 59
def prefixEnd_3839433 : Nat := 4983230072969 + 3 ^ 40 * 3839433 * 2
def baseEnd_3839433 : Nat := 1971474569733981934430275

theorem tailTrace_3839433 : CollatzResearch.WordTrace tailWord_3839433 prefixEnd_3839433 1971474569733981934430275 := by
  unfold tailWord_3839433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140035625899397438796738953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93357083932931625864492635 140035625899397438796738953)
  ·
    refine ⟨105026719424548079097554215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140035625899397438796738953 105026719424548079097554215)
    ·
      refine ⟨157540079136822118646331323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105026719424548079097554215 157540079136822118646331323)
      ·
        refine ⟨236310118705233177969496985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157540079136822118646331323 236310118705233177969496985)
        ·
          refine ⟨177232589028924883477122739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236310118705233177969496985 177232589028924883477122739)
          ·
            refine ⟨265848883543387325215684109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177232589028924883477122739 265848883543387325215684109)
            ·
              refine ⟨99693331328770246955881541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265848883543387325215684109 99693331328770246955881541)
              ·
                refine ⟨18692499624144421304227789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99693331328770246955881541 18692499624144421304227789)
                ·
                  refine ⟨7009687359054157989085421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18692499624144421304227789 7009687359054157989085421)
                  ·
                    refine ⟨2628632759645309245907033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7009687359054157989085421 2628632759645309245907033)
                    ·
                      refine ⟨1971474569733981934430275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628632759645309245907033 1971474569733981934430275)
                      ·
                        rfl

theorem cell23_3839433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3, 2].length) (baseStart_3839433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839433 prefixEnd_3839433 := by exact prefixLift 3839433
  have htrace : WordTrace (prefixWord ++ tailWord_3839433) baseStart_3839433 baseEnd_3839433 := by
    simpa [prefixWord, tailWord_3839433, baseEnd_3839433] using wordTrace_append hprefix tailTrace_3839433
  have hstable : (prefixWord ++ tailWord_3839433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839433).length < 2 ^ (prefixWord ++ tailWord_3839433).sum := by decide
  have hdescent : baseEnd_3839433 < baseStart_3839433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839444 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_3839444 : Nat := 118140960795 + 3839444 * 2 ^ 59
def prefixEnd_3839444 : Nat := 4983230072969 + 3 ^ 40 * 3839444 * 2
def baseEnd_3839444 : Nat := 1971480218021181391392725

theorem tailTrace_3839444 : CollatzResearch.WordTrace tailWord_3839444 prefixEnd_3839444 1971480218021181391392725 := by
  unfold tailWord_3839444
  simp only [CollatzResearch.WordTrace]
  refine ⟨70018013551178793837694693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93357351401571725116926257 70018013551178793837694693)
  ·
    refine ⟨13128377540846023844567755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70018013551178793837694693 13128377540846023844567755)
    ·
      refine ⟨19692566311269035766851633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13128377540846023844567755 19692566311269035766851633)
      ·
        refine ⟨14769424733451776825138725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19692566311269035766851633 14769424733451776825138725)
        ·
          refine ⟨2769267137522208154713511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14769424733451776825138725 2769267137522208154713511)
          ·
            refine ⟨4153900706283312232070267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769267137522208154713511 4153900706283312232070267)
            ·
              refine ⟨6230851059424968348105401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153900706283312232070267 6230851059424968348105401)
              ·
                refine ⟨4673138294568726261079051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6230851059424968348105401 4673138294568726261079051)
                ·
                  refine ⟨7009707441853089391618577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673138294568726261079051 7009707441853089391618577)
                  ·
                    refine ⟨5257280581389817043713933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7009707441853089391618577 5257280581389817043713933)
                    ·
                      refine ⟨1971480218021181391392725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5257280581389817043713933 1971480218021181391392725)
                      ·
                        rfl

theorem cell23_3839444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_3839444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839444 prefixEnd_3839444 := by exact prefixLift 3839444
  have htrace : WordTrace (prefixWord ++ tailWord_3839444) baseStart_3839444 baseEnd_3839444 := by
    simpa [prefixWord, tailWord_3839444, baseEnd_3839444] using wordTrace_append hprefix tailTrace_3839444
  have hstable : (prefixWord ++ tailWord_3839444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839444).length < 2 ^ (prefixWord ++ tailWord_3839444).sum := by decide
  have hdescent : baseEnd_3839444 < baseStart_3839444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839450 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_3839450 : Nat := 118140960795 + 3839450 * 2 ^ 59
def prefixEnd_3839450 : Nat := 4983230072969 + 3 ^ 40 * 3839450 * 2
def baseEnd_3839450 : Nat := 1971483298905108367917697

theorem tailTrace_3839450 : CollatzResearch.WordTrace tailWord_3839450 prefixEnd_3839450 1971483298905108367917697 := by
  unfold tailWord_3839450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009061485083962675026951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93357497293557233800071869 35009061485083962675026951)
  ·
    refine ⟨52513592227625944012540427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35009061485083962675026951 52513592227625944012540427)
    ·
      refine ⟨78770388341438916018810641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52513592227625944012540427 78770388341438916018810641)
      ·
        refine ⟨59077791256079187014107981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78770388341438916018810641 59077791256079187014107981)
        ·
          refine ⟨22154171721029695130290493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59077791256079187014107981 22154171721029695130290493)
          ·
            refine ⟨8307814395386135673858935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22154171721029695130290493 8307814395386135673858935)
            ·
              refine ⟨12461721593079203510788403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307814395386135673858935 12461721593079203510788403)
              ·
                refine ⟨18692582389618805266182605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12461721593079203510788403 18692582389618805266182605)
                ·
                  refine ⟨7009718396107051974818477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18692582389618805266182605 7009718396107051974818477)
                  ·
                    refine ⟨2628644398540144490556929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7009718396107051974818477 2628644398540144490556929)
                    ·
                      refine ⟨1971483298905108367917697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628644398540144490556929 1971483298905108367917697)
                      ·
                        rfl

theorem cell23_3839450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_3839450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839450 prefixEnd_3839450 := by exact prefixLift 3839450
  have htrace : WordTrace (prefixWord ++ tailWord_3839450) baseStart_3839450 baseEnd_3839450 := by
    simpa [prefixWord, tailWord_3839450, baseEnd_3839450] using wordTrace_append hprefix tailTrace_3839450
  have hstable : (prefixWord ++ tailWord_3839450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839450).length < 2 ^ (prefixWord ++ tailWord_3839450).sum := by decide
  have hdescent : baseEnd_3839450 < baseStart_3839450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839490 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3839490 : Nat := 118140960795 + 3839490 * 2 ^ 59
def prefixEnd_3839490 : Nat := 4983230072969 + 3 ^ 40 * 3839490 * 2
def baseEnd_3839490 : Nat := 657167946043762737139171

theorem tailTrace_3839490 : CollatzResearch.WordTrace tailWord_3839490 prefixEnd_3839490 657167946043762737139171 := by
  unfold tailWord_3839490
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009426215047734382890981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93358469906793958354375949 35009426215047734382890981)
  ·
    refine ⟨6564267415321450196792059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35009426215047734382890981 6564267415321450196792059)
    ·
      refine ⟨9846401122982175295188089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564267415321450196792059 9846401122982175295188089)
      ·
        refine ⟨7384800842236631471391067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9846401122982175295188089 7384800842236631471391067)
        ·
          refine ⟨11077201263354947207086601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384800842236631471391067 11077201263354947207086601)
          ·
            refine ⟨8307900947516210405314951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11077201263354947207086601 8307900947516210405314951)
            ·
              refine ⟨12461851421274315607972427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307900947516210405314951 12461851421274315607972427)
              ·
                refine ⟨18692777131911473411958641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12461851421274315607972427 18692777131911473411958641)
                ·
                  refine ⟨14019582848933605058968981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18692777131911473411958641 14019582848933605058968981)
                  ·
                    refine ⟨657167946043762737139171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14019582848933605058968981 657167946043762737139171)
                    ·
                      rfl

theorem cell23_3839490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3839490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839490 prefixEnd_3839490 := by exact prefixLift 3839490
  have htrace : WordTrace (prefixWord ++ tailWord_3839490) baseStart_3839490 baseEnd_3839490 := by
    simpa [prefixWord, tailWord_3839490, baseEnd_3839490] using wordTrace_append hprefix tailTrace_3839490
  have hstable : (prefixWord ++ tailWord_3839490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839490).length < 2 ^ (prefixWord ++ tailWord_3839490).sum := by decide
  have hdescent : baseEnd_3839490 < baseStart_3839490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839518 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3839518 : Nat := 118140960795 + 3839518 * 2 ^ 59
def prefixEnd_3839518 : Nat := 4983230072969 + 3 ^ 40 * 3839518 * 2
def baseEnd_3839518 : Nat := 1971518215589614101867385

theorem tailTrace_3839518 : CollatzResearch.WordTrace tailWord_3839518 prefixEnd_3839518 1971518215589614101867385 := by
  unfold tailWord_3839518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504840763011187289197901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93359150736059665542388805 17504840763011187289197901)
  ·
    refine ⟨6564315286129195233449213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17504840763011187289197901 6564315286129195233449213)
    ·
      refine ⟨2461618232298448212543455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6564315286129195233449213 2461618232298448212543455)
      ·
        refine ⟨3692427348447672318815183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461618232298448212543455 3692427348447672318815183)
        ·
          refine ⟨5538641022671508478222775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692427348447672318815183 5538641022671508478222775)
          ·
            refine ⟨8307961534007262717334163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538641022671508478222775 8307961534007262717334163)
            ·
              refine ⟨12461942301010894076001245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307961534007262717334163 12461942301010894076001245)
              ·
                refine ⟨4673228362879085278500467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12461942301010894076001245 4673228362879085278500467)
                ·
                  refine ⟨7009842544318627917750701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673228362879085278500467 7009842544318627917750701)
                  ·
                    refine ⟨2628690954119485469156513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7009842544318627917750701 2628690954119485469156513)
                    ·
                      refine ⟨1971518215589614101867385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628690954119485469156513 1971518215589614101867385)
                      ·
                        rfl

theorem cell23_3839518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3839518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839518 prefixEnd_3839518 := by exact prefixLift 3839518
  have htrace : WordTrace (prefixWord ++ tailWord_3839518) baseStart_3839518 baseEnd_3839518 := by
    simpa [prefixWord, tailWord_3839518, baseEnd_3839518] using wordTrace_append hprefix tailTrace_3839518
  have hstable : (prefixWord ++ tailWord_3839518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839518).length < 2 ^ (prefixWord ++ tailWord_3839518).sum := by decide
  have hdescent : baseEnd_3839518 < baseStart_3839518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839520 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 5]
def baseStart_3839520 : Nat := 118140960795 + 3839520 * 2 ^ 59
def prefixEnd_3839520 : Nat := 4983230072969 + 3 ^ 40 * 3839520 * 2
def baseEnd_3839520 : Nat := 219057693616769232671375

theorem tailTrace_3839520 : CollatzResearch.WordTrace tailWord_3839520 prefixEnd_3839520 219057693616769232671375 := by
  unfold tailWord_3839520
  simp only [CollatzResearch.WordTrace]
  refine ⟨70019399525041126327578007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93359199366721501770104009 70019399525041126327578007)
  ·
    refine ⟨105029099287561689491367011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70019399525041126327578007 105029099287561689491367011)
    ·
      refine ⟨157543648931342534237050517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105029099287561689491367011 157543648931342534237050517)
      ·
        refine ⟨7384858543656681292361743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157543648931342534237050517 7384858543656681292361743)
        ·
          refine ⟨11077287815485021938542615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384858543656681292361743 11077287815485021938542615)
          ·
            refine ⟨16615931723227532907813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077287815485021938542615 16615931723227532907813923)
            ·
              refine ⟨24923897584841299361720885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16615931723227532907813923 24923897584841299361720885)
              ·
                refine ⟨2336615398578871815161333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24923897584841299361720885 2336615398578871815161333)
                ·
                  refine ⟨219057693616769232671375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2336615398578871815161333 219057693616769232671375)
                  ·
                    rfl

theorem cell23_3839520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 5].length) (baseStart_3839520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839520 prefixEnd_3839520 := by exact prefixLift 3839520
  have htrace : WordTrace (prefixWord ++ tailWord_3839520) baseStart_3839520 baseEnd_3839520 := by
    simpa [prefixWord, tailWord_3839520, baseEnd_3839520] using wordTrace_append hprefix tailTrace_3839520
  have hstable : (prefixWord ++ tailWord_3839520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839520).length < 2 ^ (prefixWord ++ tailWord_3839520).sum := by decide
  have hdescent : baseEnd_3839520 < baseStart_3839520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839553 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3839553 : Nat := 118140960795 + 3839553 * 2 ^ 59
def prefixEnd_3839553 : Nat := 4983230072969 + 3 ^ 40 * 3839553 * 2
def baseEnd_3839553 : Nat := 1971536187412521464929723

theorem tailTrace_3839553 : CollatzResearch.WordTrace tailWord_3839553 prefixEnd_3839553 1971536187412521464929723 := by
  unfold tailWord_3839553
  simp only [CollatzResearch.WordTrace]
  refine ⟨140040002658962699291107313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93360001772641799527404875 140040002658962699291107313)
  ·
    refine ⟨105030001994222024468330485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140040002658962699291107313 105030001994222024468330485)
    ·
      refine ⟨9846562686958314793905983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105030001994222024468330485 9846562686958314793905983)
      ·
        refine ⟨14769844030437472190858975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846562686958314793905983 14769844030437472190858975)
        ·
          refine ⟨22154766045656208286288463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769844030437472190858975 22154766045656208286288463)
          ·
            refine ⟨33232149068484312429432695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154766045656208286288463 33232149068484312429432695)
            ·
              refine ⟨49848223602726468644149043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33232149068484312429432695 49848223602726468644149043)
              ·
                refine ⟨74772335404089702966223565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49848223602726468644149043 74772335404089702966223565)
                ·
                  refine ⟨28039625776533638612333837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74772335404089702966223565 28039625776533638612333837)
                  ·
                    refine ⟨10514859666200114479625189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28039625776533638612333837 10514859666200114479625189)
                    ·
                      refine ⟨1971536187412521464929723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10514859666200114479625189 1971536187412521464929723)
                      ·
                        rfl

theorem cell23_3839553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3839553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839553 prefixEnd_3839553 := by exact prefixLift 3839553
  have htrace : WordTrace (prefixWord ++ tailWord_3839553) baseStart_3839553 baseEnd_3839553 := by
    simpa [prefixWord, tailWord_3839553, baseEnd_3839553] using wordTrace_append hprefix tailTrace_3839553
  have hstable : (prefixWord ++ tailWord_3839553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839553).length < 2 ^ (prefixWord ++ tailWord_3839553).sum := by decide
  have hdescent : baseEnd_3839553 < baseStart_3839553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839624 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3839624 : Nat := 118140960795 + 3839624 * 2 ^ 59
def prefixEnd_3839624 : Nat := 4983230072969 + 3 ^ 40 * 3839624 * 2
def baseEnd_3839624 : Nat := 1971572644538990687141897

theorem tailTrace_3839624 : CollatzResearch.WordTrace tailWord_3839624 prefixEnd_3839624 1971572644538990687141897 := by
  unfold tailWord_3839624
  simp only [CollatzResearch.WordTrace]
  refine ⟨70021296120852739208470963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93361728161136985611294617 70021296120852739208470963)
  ·
    refine ⟨105031944181279108812706445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70021296120852739208470963 105031944181279108812706445)
    ·
      refine ⟨39386979067979665804764917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105031944181279108812706445 39386979067979665804764917)
      ·
        refine ⟨3692529287623093669196711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39386979067979665804764917 3692529287623093669196711)
        ·
          refine ⟨5538793931434640503795067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692529287623093669196711 5538793931434640503795067)
          ·
            refine ⟨8308190897151960755692601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538793931434640503795067 8308190897151960755692601)
            ·
              refine ⟨6231143172863970566769451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8308190897151960755692601 6231143172863970566769451)
              ·
                refine ⟨9346714759295955850154177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231143172863970566769451 9346714759295955850154177)
                ·
                  refine ⟨7010036069471966887615633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346714759295955850154177 7010036069471966887615633)
                  ·
                    refine ⟨5257527052103975165711725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010036069471966887615633 5257527052103975165711725)
                    ·
                      refine ⟨1971572644538990687141897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5257527052103975165711725 1971572644538990687141897)
                      ·
                        rfl

theorem cell23_3839624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3839624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839624 prefixEnd_3839624 := by exact prefixLift 3839624
  have htrace : WordTrace (prefixWord ++ tailWord_3839624) baseStart_3839624 baseEnd_3839624 := by
    simpa [prefixWord, tailWord_3839624, baseEnd_3839624] using wordTrace_append hprefix tailTrace_3839624
  have hstable : (prefixWord ++ tailWord_3839624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839624).length < 2 ^ (prefixWord ++ tailWord_3839624).sum := by decide
  have hdescent : baseEnd_3839624 < baseStart_3839624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839663 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_3839663 : Nat := 118140960795 + 3839663 * 2 ^ 59
def prefixEnd_3839663 : Nat := 4983230072969 + 3 ^ 40 * 3839663 * 2
def baseEnd_3839663 : Nat := 1971592670284516034554217

theorem tailTrace_3839663 : CollatzResearch.WordTrace tailWord_3839663 prefixEnd_3839663 1971592670284516034554217 := by
  unfold tailWord_3839663
  simp only [CollatzResearch.WordTrace]
  refine ⟨140044014688564188077611643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93362676459042792051741095 140044014688564188077611643)
  ·
    refine ⟨210066022032846282116417465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140044014688564188077611643 210066022032846282116417465)
    ·
      refine ⟨157549516524634711587313099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210066022032846282116417465 157549516524634711587313099)
      ·
        refine ⟨236324274786952067380969649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157549516524634711587313099 236324274786952067380969649)
        ·
          refine ⟨177243206090214050535727237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236324274786952067380969649 177243206090214050535727237)
          ·
            refine ⟨33233101141915134475448857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177243206090214050535727237 33233101141915134475448857)
            ·
              refine ⟨24924825856436350856586643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33233101141915134475448857 24924825856436350856586643)
              ·
                refine ⟨37387238784654526284879965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24924825856436350856586643 37387238784654526284879965)
                ·
                  refine ⟨14020214544245447356829987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37387238784654526284879965 14020214544245447356829987)
                  ·
                    refine ⟨21030321816368171035244981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14020214544245447356829987 21030321816368171035244981)
                    ·
                      refine ⟨1971592670284516034554217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21030321816368171035244981 1971592670284516034554217)
                      ·
                        rfl

theorem cell23_3839663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_3839663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839663 prefixEnd_3839663 := by exact prefixLift 3839663
  have htrace : WordTrace (prefixWord ++ tailWord_3839663) baseStart_3839663 baseEnd_3839663 := by
    simpa [prefixWord, tailWord_3839663, baseEnd_3839663] using wordTrace_append hprefix tailTrace_3839663
  have hstable : (prefixWord ++ tailWord_3839663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839663).length < 2 ^ (prefixWord ++ tailWord_3839663).sum := by decide
  have hdescent : baseEnd_3839663 < baseStart_3839663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839673 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3839673 : Nat := 118140960795 + 3839673 * 2 ^ 59
def prefixEnd_3839673 : Nat := 4983230072969 + 3 ^ 40 * 3839673 * 2
def baseEnd_3839673 : Nat := 1971597805091060995429171

theorem tailTrace_3839673 : CollatzResearch.WordTrace tailWord_3839673 prefixEnd_3839673 1971597805091060995429171 := by
  unfold tailWord_3839673
  simp only [CollatzResearch.WordTrace]
  refine ⟨140044379418527959785475673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93362919612351973190317115 140044379418527959785475673)
  ·
    refine ⟨105033284563895969839106755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140044379418527959785475673 105033284563895969839106755)
    ·
      refine ⟨157549926845843954758660133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105033284563895969839106755 157549926845843954758660133)
      ·
        refine ⟨29540611283595741517248775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157549926845843954758660133 29540611283595741517248775)
        ·
          refine ⟨44310916925393612275873163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29540611283595741517248775 44310916925393612275873163)
          ·
            refine ⟨66466375388090418413809745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44310916925393612275873163 66466375388090418413809745)
            ·
              refine ⟨49849781541067813810357309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66466375388090418413809745 49849781541067813810357309)
              ·
                refine ⟨18693668077900430178883991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49849781541067813810357309 18693668077900430178883991)
                ·
                  refine ⟨28040502116850645268325987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18693668077900430178883991 28040502116850645268325987)
                  ·
                    refine ⟨42060753175275967902488981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28040502116850645268325987 42060753175275967902488981)
                    ·
                      refine ⟨1971597805091060995429171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42060753175275967902488981 1971597805091060995429171)
                      ·
                        rfl

theorem cell23_3839673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3839673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839673 prefixEnd_3839673 := by exact prefixLift 3839673
  have htrace : WordTrace (prefixWord ++ tailWord_3839673) baseStart_3839673 baseEnd_3839673 := by
    simpa [prefixWord, tailWord_3839673, baseEnd_3839673] using wordTrace_append hprefix tailTrace_3839673
  have hstable : (prefixWord ++ tailWord_3839673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839673).length < 2 ^ (prefixWord ++ tailWord_3839673).sum := by decide
  have hdescent : baseEnd_3839673 < baseStart_3839673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839680 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_3839680 : Nat := 118140960795 + 3839680 * 2 ^ 59
def prefixEnd_3839680 : Nat := 4983230072969 + 3 ^ 40 * 3839680 * 2
def baseEnd_3839680 : Nat := 1971601399455642468041639

theorem tailTrace_3839680 : CollatzResearch.WordTrace tailWord_3839680 prefixEnd_3839680 1971601399455642468041639 := by
  unfold tailWord_3839680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70022317364751299990490247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93363089819668399987320329 70022317364751299990490247)
  ·
    refine ⟨105033476047126949985735371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70022317364751299990490247 105033476047126949985735371)
    ·
      refine ⟨157550214070690424978603057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105033476047126949985735371 157550214070690424978603057)
      ·
        refine ⟨118162660553017818733952293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157550214070690424978603057 118162660553017818733952293)
        ·
          refine ⟨22155498853690841012616055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118162660553017818733952293 22155498853690841012616055)
          ·
            refine ⟨33233248280536261518924083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22155498853690841012616055 33233248280536261518924083)
            ·
              refine ⟨49849872420804392278386125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33233248280536261518924083 49849872420804392278386125)
              ·
                refine ⟨18693702157801647104394797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49849872420804392278386125 18693702157801647104394797)
                ·
                  refine ⟨7010138309175617664148049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18693702157801647104394797 7010138309175617664148049)
                  ·
                    refine ⟨5257603731881713248111037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010138309175617664148049 5257603731881713248111037)
                    ·
                      refine ⟨1971601399455642468041639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5257603731881713248111037 1971601399455642468041639)
                      ·
                        rfl

theorem cell23_3839680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_3839680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839680 prefixEnd_3839680 := by exact prefixLift 3839680
  have htrace : WordTrace (prefixWord ++ tailWord_3839680) baseStart_3839680 baseEnd_3839680 := by
    simpa [prefixWord, tailWord_3839680, baseEnd_3839680] using wordTrace_append hprefix tailTrace_3839680
  have hstable : (prefixWord ++ tailWord_3839680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839680).length < 2 ^ (prefixWord ++ tailWord_3839680).sum := by decide
  have hdescent : baseEnd_3839680 < baseStart_3839680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839697 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_3839697 : Nat := 118140960795 + 3839697 * 2 ^ 59
def prefixEnd_3839697 : Nat := 4983230072969 + 3 ^ 40 * 3839697 * 2
def baseEnd_3839697 : Nat := 1971610128626768901529061

theorem tailTrace_3839697 : CollatzResearch.WordTrace tailWord_3839697 prefixEnd_3839697 1971610128626768901529061 := by
  unfold tailWord_3839697
  simp only [CollatzResearch.WordTrace]
  refine ⟨140045254770441011884349345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93363503180294007922899563 140045254770441011884349345)
  ·
    refine ⟨105033941077830758913262009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140045254770441011884349345 105033941077830758913262009)
    ·
      refine ⟨78775455808373069184946507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105033941077830758913262009 78775455808373069184946507)
      ·
        refine ⟨118163183712559603777419761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78775455808373069184946507 118163183712559603777419761)
        ·
          refine ⟨88622387784419702833064821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118163183712559603777419761 88622387784419702833064821)
          ·
            refine ⟨8308348854789347140599827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88622387784419702833064821 8308348854789347140599827)
            ·
              refine ⟨12462523282184020710899741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308348854789347140599827 12462523282184020710899741)
              ·
                refine ⟨4673446230819007766587403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12462523282184020710899741 4673446230819007766587403)
                ·
                  refine ⟨7010169346228511649881105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673446230819007766587403 7010169346228511649881105)
                  ·
                    refine ⟨5257627009671383737410829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010169346228511649881105 5257627009671383737410829)
                    ·
                      refine ⟨1971610128626768901529061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5257627009671383737410829 1971610128626768901529061)
                      ·
                        rfl

theorem cell23_3839697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_3839697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839697 prefixEnd_3839697 := by exact prefixLift 3839697
  have htrace : WordTrace (prefixWord ++ tailWord_3839697) baseStart_3839697 baseEnd_3839697 := by
    simpa [prefixWord, tailWord_3839697, baseEnd_3839697] using wordTrace_append hprefix tailTrace_3839697
  have hstable : (prefixWord ++ tailWord_3839697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839697).length < 2 ^ (prefixWord ++ tailWord_3839697).sum := by decide
  have hdescent : baseEnd_3839697 < baseStart_3839697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839700 : List Nat := [2, 4, 1, 3, 1, 2, 10]
def baseStart_3839700 : Nat := 118140960795 + 3839700 * 2 ^ 59
def prefixEnd_3839700 : Nat := 4983230072969 + 3 ^ 40 * 3839700 * 2
def baseEnd_3839700 : Nat := 24340884803317683824587

theorem tailTrace_3839700 : CollatzResearch.WordTrace tailWord_3839700 prefixEnd_3839700 24340884803317683824587 := by
  unfold tailWord_3839700
  simp only [CollatzResearch.WordTrace]
  refine ⟨70022682094715071698354277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93363576126286762264472369 70022682094715071698354277)
  ·
    refine ⟨13129252892759075943441427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70022682094715071698354277 13129252892759075943441427)
    ·
      refine ⟨19693879339138613915162141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129252892759075943441427 19693879339138613915162141)
      ·
        refine ⟨7385204752176980218185803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19693879339138613915162141 7385204752176980218185803)
        ·
          refine ⟨11077807128265470327278705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385204752176980218185803 11077807128265470327278705)
          ·
            refine ⟨8308355346199102745459029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11077807128265470327278705 8308355346199102745459029)
            ·
              refine ⟨24340884803317683824587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8308355346199102745459029 24340884803317683824587)
              ·
                rfl

theorem cell23_3839700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 10].length) (baseStart_3839700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839700 prefixEnd_3839700 := by exact prefixLift 3839700
  have htrace : WordTrace (prefixWord ++ tailWord_3839700) baseStart_3839700 baseEnd_3839700 := by
    simpa [prefixWord, tailWord_3839700, baseEnd_3839700] using wordTrace_append hprefix tailTrace_3839700
  have hstable : (prefixWord ++ tailWord_3839700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839700).length < 2 ^ (prefixWord ++ tailWord_3839700).sum := by decide
  have hdescent : baseEnd_3839700 < baseStart_3839700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839743 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 8]
def baseStart_3839743 : Nat := 118140960795 + 3839743 * 2 ^ 59
def prefixEnd_3839743 : Nat := 4983230072969 + 3 ^ 40 * 3839743 * 2
def baseEnd_3839743 : Nat := 657211249578958573851283

theorem tailTrace_3839743 : CollatzResearch.WordTrace tailWord_3839743 prefixEnd_3839743 657211249578958573851283 := by
  unfold tailWord_3839743
  simp only [CollatzResearch.WordTrace]
  refine ⟨140046932528274361740523883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93364621685516241160349255 140046932528274361740523883)
  ·
    refine ⟨210070398792411542610785825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140046932528274361740523883 210070398792411542610785825)
    ·
      refine ⟨157552799094308656958089369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210070398792411542610785825 157552799094308656958089369)
      ·
        refine ⟨118164599320731492718567027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157552799094308656958089369 118164599320731492718567027)
        ·
          refine ⟨177246898981097239077850541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118164599320731492718567027 177246898981097239077850541)
          ·
            refine ⟨66467587117911464654193953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177246898981097239077850541 66467587117911464654193953)
            ·
              refine ⟨49850690338433598490645465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66467587117911464654193953 49850690338433598490645465)
              ·
                refine ⟨37388017753825198867984099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49850690338433598490645465 37388017753825198867984099)
                ·
                  refine ⟨56082026630737798301976149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37388017753825198867984099 56082026630737798301976149)
                  ·
                    refine ⟨657211249578958573851283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56082026630737798301976149 657211249578958573851283)
                    ·
                      rfl

theorem cell23_3839743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_3839743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839743 prefixEnd_3839743 := by exact prefixLift 3839743
  have htrace : WordTrace (prefixWord ++ tailWord_3839743) baseStart_3839743 baseEnd_3839743 := by
    simpa [prefixWord, tailWord_3839743, baseEnd_3839743] using wordTrace_append hprefix tailTrace_3839743
  have hstable : (prefixWord ++ tailWord_3839743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839743).length < 2 ^ (prefixWord ++ tailWord_3839743).sum := by decide
  have hdescent : baseEnd_3839743 < baseStart_3839743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839754 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_3839754 : Nat := 118140960795 + 3839754 * 2 ^ 59
def prefixEnd_3839754 : Nat := 4983230072969 + 3 ^ 40 * 3839754 * 2
def baseEnd_3839754 : Nat := 1971639397024075178516299

theorem tailTrace_3839754 : CollatzResearch.WordTrace tailWord_3839754 prefixEnd_3839754 1971639397024075178516299 := by
  unfold tailWord_3839754
  simp only [CollatzResearch.WordTrace]
  refine ⟨35011833432808627654793579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93364889154156340412782877 35011833432808627654793579)
  ·
    refine ⟨52517750149212941482190369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35011833432808627654793579 52517750149212941482190369)
    ·
      refine ⟨39388312611909706111642777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52517750149212941482190369 39388312611909706111642777)
      ·
        refine ⟨29541234458932279583732083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39388312611909706111642777 29541234458932279583732083)
        ·
          refine ⟨44311851688398419375598125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29541234458932279583732083 44311851688398419375598125)
          ·
            refine ⟨16616944383149407265849297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44311851688398419375598125 16616944383149407265849297)
            ·
              refine ⟨12462708287362055449386973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16616944383149407265849297 12462708287362055449386973)
              ·
                refine ⟨4673515607760770793520115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12462708287362055449386973 4673515607760770793520115)
                ·
                  refine ⟨7010273411641156190280173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673515607760770793520115 7010273411641156190280173)
                  ·
                    refine ⟨2628852529365433571355065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7010273411641156190280173 2628852529365433571355065)
                    ·
                      refine ⟨1971639397024075178516299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628852529365433571355065 1971639397024075178516299)
                      ·
                        rfl

theorem cell23_3839754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_3839754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839754 prefixEnd_3839754 := by exact prefixLift 3839754
  have htrace : WordTrace (prefixWord ++ tailWord_3839754) baseStart_3839754 baseEnd_3839754 := by
    simpa [prefixWord, tailWord_3839754, baseEnd_3839754] using wordTrace_append hprefix tailTrace_3839754
  have hstable : (prefixWord ++ tailWord_3839754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839754).length < 2 ^ (prefixWord ++ tailWord_3839754).sum := by decide
  have hdescent : baseEnd_3839754 < baseStart_3839754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839763 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_3839763 : Nat := 118140960795 + 3839763 * 2 ^ 59
def prefixEnd_3839763 : Nat := 4983230072969 + 3 ^ 40 * 3839763 * 2
def baseEnd_3839763 : Nat := 1971644018349965643303757

theorem tailTrace_3839763 : CollatzResearch.WordTrace tailWord_3839763 prefixEnd_3839763 1971644018349965643303757 := by
  unfold tailWord_3839763
  simp only [CollatzResearch.WordTrace]
  refine ⟨140047661988201905156251943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93365107992134603437501295 140047661988201905156251943)
  ·
    refine ⟨210071492982302857734377915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140047661988201905156251943 210071492982302857734377915)
    ·
      refine ⟨315107239473454286601566873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210071492982302857734377915 315107239473454286601566873)
      ·
        refine ⟨236330429605090714951175155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315107239473454286601566873 236330429605090714951175155)
        ·
          refine ⟨354495644407636072426762733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236330429605090714951175155 354495644407636072426762733)
          ·
            refine ⟨132935866652863527160036025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354495644407636072426762733 132935866652863527160036025)
            ·
              refine ⟨99701899989647645370027019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132935866652863527160036025 99701899989647645370027019)
              ·
                refine ⟨149552849984471468055040529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99701899989647645370027019 149552849984471468055040529)
                ·
                  refine ⟨112164637488353601041280397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149552849984471468055040529 112164637488353601041280397)
                  ·
                    refine ⟨42061739058132600390480149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112164637488353601041280397 42061739058132600390480149)
                    ·
                      refine ⟨1971644018349965643303757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42061739058132600390480149 1971644018349965643303757)
                      ·
                        rfl

theorem cell23_3839763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_3839763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839763 prefixEnd_3839763 := by exact prefixLift 3839763
  have htrace : WordTrace (prefixWord ++ tailWord_3839763) baseStart_3839763 baseEnd_3839763 := by
    simpa [prefixWord, tailWord_3839763, baseEnd_3839763] using wordTrace_append hprefix tailTrace_3839763
  have hstable : (prefixWord ++ tailWord_3839763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839763).length < 2 ^ (prefixWord ++ tailWord_3839763).sum := by decide
  have hdescent : baseEnd_3839763 < baseStart_3839763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839801 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3839801 : Nat := 118140960795 + 3839801 * 2 ^ 59
def prefixEnd_3839801 : Nat := 4983230072969 + 3 ^ 40 * 3839801 * 2
def baseEnd_3839801 : Nat := 1971663530614836494628583

theorem tailTrace_3839801 : CollatzResearch.WordTrace tailWord_3839801 prefixEnd_3839801 1971663530614836494628583 := by
  unfold tailWord_3839801
  simp only [CollatzResearch.WordTrace]
  refine ⟨140049047962064237646135257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93366031974709491764090171 140049047962064237646135257)
  ·
    refine ⟨105036785971548178234601443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140049047962064237646135257 105036785971548178234601443)
    ·
      refine ⟨157555178957322267351902165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105036785971548178234601443 157555178957322267351902165)
      ·
        refine ⟨3692699506812240641060207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 157555178957322267351902165 3692699506812240641060207)
        ·
          refine ⟨5539049260218360961590311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692699506812240641060207 5539049260218360961590311)
          ·
            refine ⟨8308573890327541442385467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539049260218360961590311 8308573890327541442385467)
            ·
              refine ⟨12462860835491312163578201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308573890327541442385467 12462860835491312163578201)
              ·
                refine ⟨9347145626618484122683651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12462860835491312163578201 9347145626618484122683651)
                ·
                  refine ⟨14020718439927726184025477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347145626618484122683651 14020718439927726184025477)
                  ·
                    refine ⟨2628884707486448659504777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14020718439927726184025477 2628884707486448659504777)
                    ·
                      refine ⟨1971663530614836494628583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628884707486448659504777 1971663530614836494628583)
                      ·
                        rfl

theorem cell23_3839801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3839801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839801 prefixEnd_3839801 := by exact prefixLift 3839801
  have htrace : WordTrace (prefixWord ++ tailWord_3839801) baseStart_3839801 baseEnd_3839801 := by
    simpa [prefixWord, tailWord_3839801, baseEnd_3839801] using wordTrace_append hprefix tailTrace_3839801
  have hstable : (prefixWord ++ tailWord_3839801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839801).length < 2 ^ (prefixWord ++ tailWord_3839801).sum := by decide
  have hdescent : baseEnd_3839801 < baseStart_3839801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839854 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3839854 : Nat := 118140960795 + 3839854 * 2 ^ 59
def prefixEnd_3839854 : Nat := 4983230072969 + 3 ^ 40 * 3839854 * 2
def baseEnd_3839854 : Nat := 657230248363174929088613

theorem tailTrace_3839854 : CollatzResearch.WordTrace tailWord_3839854 prefixEnd_3839854 657230248363174929088613 := by
  unfold tailWord_3839854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506372628859028462226827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93367320687248151798543077 17506372628859028462226827)
  ·
    refine ⟨26259558943288542693340241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17506372628859028462226827 26259558943288542693340241)
    ·
      refine ⟨19694669207466407020005181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26259558943288542693340241 19694669207466407020005181)
      ·
        refine ⟨7385500952799902632501943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19694669207466407020005181 7385500952799902632501943)
        ·
          refine ⟨11078251429199853948752915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385500952799902632501943 11078251429199853948752915)
          ·
            refine ⟨16617377143799780923129373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078251429199853948752915 16617377143799780923129373)
            ·
              refine ⟨6231516428924917846173515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16617377143799780923129373 6231516428924917846173515)
              ·
                refine ⟨9347274643387376769260273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231516428924917846173515 9347274643387376769260273)
                ·
                  refine ⟨7010455982540532576945205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9347274643387376769260273 7010455982540532576945205)
                  ·
                    refine ⟨657230248363174929088613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7010455982540532576945205 657230248363174929088613)
                    ·
                      rfl

theorem cell23_3839854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3839854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839854 prefixEnd_3839854 := by exact prefixLift 3839854
  have htrace : WordTrace (prefixWord ++ tailWord_3839854) baseStart_3839854 baseEnd_3839854 := by
    simpa [prefixWord, tailWord_3839854, baseEnd_3839854] using wordTrace_append hprefix tailTrace_3839854
  have hstable : (prefixWord ++ tailWord_3839854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839854).length < 2 ^ (prefixWord ++ tailWord_3839854).sum := by decide
  have hdescent : baseEnd_3839854 < baseStart_3839854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839857 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_3839857 : Nat := 118140960795 + 3839857 * 2 ^ 59
def prefixEnd_3839857 : Nat := 4983230072969 + 3 ^ 40 * 3839857 * 2
def baseEnd_3839857 : Nat := 1971692285531488275528325

theorem tailTrace_3839857 : CollatzResearch.WordTrace tailWord_3839857 prefixEnd_3839857 1971692285531488275528325 := by
  unfold tailWord_3839857
  simp only [CollatzResearch.WordTrace]
  refine ⟨140051090449861359210173825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93367393633240906140115883 140051090449861359210173825)
  ·
    refine ⟨105038317837396019407630369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140051090449861359210173825 105038317837396019407630369)
    ·
      refine ⟨78778738378047014555722777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105038317837396019407630369 78778738378047014555722777)
      ·
        refine ⟨59084053783535260916792083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78778738378047014555722777 59084053783535260916792083)
        ·
          refine ⟨88626080675302891375188125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59084053783535260916792083 88626080675302891375188125)
          ·
            refine ⟨33234780253238584265695547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88626080675302891375188125 33234780253238584265695547)
            ·
              refine ⟨49852170379857876398543321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33234780253238584265695547 49852170379857876398543321)
              ·
                refine ⟨37389127784893407298907491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49852170379857876398543321 37389127784893407298907491)
                ·
                  refine ⟨56083691677340110948361237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37389127784893407298907491 56083691677340110948361237)
                  ·
                    refine ⟨2628923047375317700704433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56083691677340110948361237 2628923047375317700704433)
                    ·
                      refine ⟨1971692285531488275528325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2628923047375317700704433 1971692285531488275528325)
                      ·
                        rfl

theorem cell23_3839857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_3839857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839857 prefixEnd_3839857 := by exact prefixLift 3839857
  have htrace : WordTrace (prefixWord ++ tailWord_3839857) baseStart_3839857 baseEnd_3839857 := by
    simpa [prefixWord, tailWord_3839857, baseEnd_3839857] using wordTrace_append hprefix tailTrace_3839857
  have hstable : (prefixWord ++ tailWord_3839857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839857).length < 2 ^ (prefixWord ++ tailWord_3839857).sum := by decide
  have hdescent : baseEnd_3839857 < baseStart_3839857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839877 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_3839877 : Nat := 118140960795 + 3839877 * 2 ^ 59
def prefixEnd_3839877 : Nat := 4983230072969 + 3 ^ 40 * 3839877 * 2
def baseEnd_3839877 : Nat := 1971702555144578197278233

theorem tailTrace_3839877 : CollatzResearch.WordTrace tailWord_3839877 prefixEnd_3839877 1971702555144578197278233 := by
  unfold tailWord_3839877
  simp only [CollatzResearch.WordTrace]
  refine ⟨140051819909788902625901885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93367879939859268417267923 140051819909788902625901885)
  ·
    refine ⟨52519432466170838484713207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140051819909788902625901885 52519432466170838484713207)
    ·
      refine ⟨78779148699256257727069811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52519432466170838484713207 78779148699256257727069811)
      ·
        refine ⟨118168723048884386590604717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78779148699256257727069811 118168723048884386590604717)
        ·
          refine ⟨44313271143331644971476769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118168723048884386590604717 44313271143331644971476769)
          ·
            refine ⟨33234953357498733728607577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44313271143331644971476769 33234953357498733728607577)
            ·
              refine ⟨24926215018124050296455683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33234953357498733728607577 24926215018124050296455683)
              ·
                refine ⟨37389322527186075444683525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24926215018124050296455683 37389322527186075444683525)
                ·
                  refine ⟨7010497973847389145878161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37389322527186075444683525 7010497973847389145878161)
                  ·
                    refine ⟨5257873480385541859408621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010497973847389145878161 5257873480385541859408621)
                    ·
                      refine ⟨1971702555144578197278233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5257873480385541859408621 1971702555144578197278233)
                      ·
                        rfl

theorem cell23_3839877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_3839877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839877 prefixEnd_3839877 := by exact prefixLift 3839877
  have htrace : WordTrace (prefixWord ++ tailWord_3839877) baseStart_3839877 baseEnd_3839877 := by
    simpa [prefixWord, tailWord_3839877, baseEnd_3839877] using wordTrace_append hprefix tailTrace_3839877
  have hstable : (prefixWord ++ tailWord_3839877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839877).length < 2 ^ (prefixWord ++ tailWord_3839877).sum := by decide
  have hdescent : baseEnd_3839877 < baseStart_3839877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839947 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4]
def baseStart_3839947 : Nat := 118140960795 + 3839947 * 2 ^ 59
def prefixEnd_3839947 : Nat := 4983230072969 + 3 ^ 40 * 3839947 * 2
def baseEnd_3839947 : Nat := 1971738498790392923402911

theorem tailTrace_3839947 : CollatzResearch.WordTrace tailWord_3839947 prefixEnd_3839947 1971738498790392923402911 := by
  unfold tailWord_3839947
  simp only [CollatzResearch.WordTrace]
  refine ⟨140054373019535304580950095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93369582013023536387300063 140054373019535304580950095)
  ·
    refine ⟨210081559529302956871425143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140054373019535304580950095 210081559529302956871425143)
    ·
      refine ⟨315122339293954435307137715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210081559529302956871425143 315122339293954435307137715)
      ·
        refine ⟨472683508940931652960706573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315122339293954435307137715 472683508940931652960706573)
        ·
          refine ⟨177256315852849369860264965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472683508940931652960706573 177256315852849369860264965)
          ·
            refine ⟨33235559222409256848799681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177256315852849369860264965 33235559222409256848799681)
            ·
              refine ⟨24926669416806942636599761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33235559222409256848799681 24926669416806942636599761)
              ·
                refine ⟨18695002062605206977449821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24926669416806942636599761 18695002062605206977449821)
                ·
                  refine ⟨7010625773476952616543683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18695002062605206977449821 7010625773476952616543683)
                  ·
                    refine ⟨10515938660215428924815525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7010625773476952616543683 10515938660215428924815525)
                    ·
                      refine ⟨1971738498790392923402911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10515938660215428924815525 1971738498790392923402911)
                      ·
                        rfl

theorem cell23_3839947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4].length) (baseStart_3839947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839947 prefixEnd_3839947 := by exact prefixLift 3839947
  have htrace : WordTrace (prefixWord ++ tailWord_3839947) baseStart_3839947 baseEnd_3839947 := by
    simpa [prefixWord, tailWord_3839947, baseEnd_3839947] using wordTrace_append hprefix tailTrace_3839947
  have hstable : (prefixWord ++ tailWord_3839947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839947).length < 2 ^ (prefixWord ++ tailWord_3839947).sum := by decide
  have hdescent : baseEnd_3839947 < baseStart_3839947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839961 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_3839961 : Nat := 118140960795 + 3839961 * 2 ^ 59
def prefixEnd_3839961 : Nat := 4983230072969 + 3 ^ 40 * 3839961 * 2
def baseEnd_3839961 : Nat := 657248562506518622875949

theorem tailTrace_3839961 : CollatzResearch.WordTrace tailWord_3839961 prefixEnd_3839961 657248562506518622875949 := by
  unfold tailWord_3839961
  simp only [CollatzResearch.WordTrace]
  refine ⟨140054883641484584971959737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93369922427656389981306491 140054883641484584971959737)
  ·
    refine ⟨105041162731113438728969803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140054883641484584971959737 105041162731113438728969803)
    ·
      refine ⟨157561744096670158093454705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105041162731113438728969803 157561744096670158093454705)
      ·
        refine ⟨118171308072502618570091029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157561744096670158093454705 118171308072502618570091029)
        ·
          refine ⟨5539280065898560245473017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118171308072502618570091029 5539280065898560245473017)
          ·
            refine ⟨4154460049423920184104763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5539280065898560245473017 4154460049423920184104763)
            ·
              refine ⟨6231690074135880276157145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154460049423920184104763 6231690074135880276157145)
              ·
                refine ⟨4673767555601910207117859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6231690074135880276157145 4673767555601910207117859)
                ·
                  refine ⟨7010651333402865310676789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673767555601910207117859 7010651333402865310676789)
                  ·
                    refine ⟨657248562506518622875949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7010651333402865310676789 657248562506518622875949)
                    ·
                      rfl

theorem cell23_3839961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_3839961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839961 prefixEnd_3839961 := by exact prefixLift 3839961
  have htrace : WordTrace (prefixWord ++ tailWord_3839961) baseStart_3839961 baseEnd_3839961 := by
    simpa [prefixWord, tailWord_3839961, baseEnd_3839961] using wordTrace_append hprefix tailTrace_3839961
  have hstable : (prefixWord ++ tailWord_3839961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839961).length < 2 ^ (prefixWord ++ tailWord_3839961).sum := by decide
  have hdescent : baseEnd_3839961 < baseStart_3839961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3839984 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_3839984 : Nat := 118140960795 + 3839984 * 2 ^ 59
def prefixEnd_3839984 : Nat := 4983230072969 + 3 ^ 40 * 3839984 * 2
def baseEnd_3839984 : Nat := 1971757497574609278640241

theorem tailTrace_3839984 : CollatzResearch.WordTrace tailWord_3839984 prefixEnd_3839984 1971757497574609278640241 := by
  unfold tailWord_3839984
  simp only [CollatzResearch.WordTrace]
  refine ⟨70027861260200629950023503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93370481680267506600031337 70027861260200629950023503)
  ·
    refine ⟨105041791890300944925035255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70027861260200629950023503 105041791890300944925035255)
    ·
      refine ⟨157562687835451417387552883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105041791890300944925035255 157562687835451417387552883)
      ·
        refine ⟨236344031753177126081329325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157562687835451417387552883 236344031753177126081329325)
        ·
          refine ⟨88629011907441422280498497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236344031753177126081329325 88629011907441422280498497)
          ·
            refine ⟨66471758930581066710373873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88629011907441422280498497 66471758930581066710373873)
            ·
              refine ⟨49853819197935800032780405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66471758930581066710373873 49853819197935800032780405)
              ·
                refine ⟨4673795549806481253073163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49853819197935800032780405 4673795549806481253073163)
                ·
                  refine ⟨7010693324709721879609745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673795549806481253073163 7010693324709721879609745)
                  ·
                    refine ⟨5258019993532291409707309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010693324709721879609745 5258019993532291409707309)
                    ·
                      refine ⟨1971757497574609278640241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258019993532291409707309 1971757497574609278640241)
                      ·
                        rfl

theorem cell23_3839984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_3839984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3839984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3839984 prefixEnd_3839984 := by exact prefixLift 3839984
  have htrace : WordTrace (prefixWord ++ tailWord_3839984) baseStart_3839984 baseEnd_3839984 := by
    simpa [prefixWord, tailWord_3839984, baseEnd_3839984] using wordTrace_append hprefix tailTrace_3839984
  have hstable : (prefixWord ++ tailWord_3839984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3839984).length < 2 ^ (prefixWord ++ tailWord_3839984).sum := by decide
  have hdescent : baseEnd_3839984 < baseStart_3839984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3839984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840048 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3]
def baseStart_3840048 : Nat := 118140960795 + 3840048 * 2 ^ 59
def prefixEnd_3840048 : Nat := 4983230072969 + 3 ^ 40 * 3840048 * 2
def baseEnd_3840048 : Nat := 1971790360336497028239947

theorem tailTrace_3840048 : CollatzResearch.WordTrace tailWord_3840048 prefixEnd_3840048 1971790360336497028239947 := by
  unfold tailWord_3840048
  simp only [CollatzResearch.WordTrace]
  refine ⟨70029028396084699415188399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93372037861446265886917865 70029028396084699415188399)
  ·
    refine ⟨105043542594127049122782599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70029028396084699415188399 105043542594127049122782599)
    ·
      refine ⟨157565313891190573684173899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105043542594127049122782599 157565313891190573684173899)
      ·
        refine ⟨236347970836785860526260849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157565313891190573684173899 236347970836785860526260849)
        ·
          refine ⟨177260978127589395394695637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236347970836785860526260849 177260978127589395394695637)
          ·
            refine ⟨4154554174865376454563179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177260978127589395394695637 4154554174865376454563179)
            ·
              refine ⟨6231831262298064681844769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154554174865376454563179 6231831262298064681844769)
              ·
                refine ⟨4673873446723548511383577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6231831262298064681844769 4673873446723548511383577)
                ·
                  refine ⟨3505405085042661383537683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4673873446723548511383577 3505405085042661383537683)
                  ·
                    refine ⟨5258107627563992075306525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3505405085042661383537683 5258107627563992075306525)
                    ·
                      refine ⟨1971790360336497028239947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258107627563992075306525 1971790360336497028239947)
                      ·
                        rfl

theorem cell23_3840048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_3840048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840048 prefixEnd_3840048 := by exact prefixLift 3840048
  have htrace : WordTrace (prefixWord ++ tailWord_3840048) baseStart_3840048 baseEnd_3840048 := by
    simpa [prefixWord, tailWord_3840048, baseEnd_3840048] using wordTrace_append hprefix tailTrace_3840048
  have hstable : (prefixWord ++ tailWord_3840048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840048).length < 2 ^ (prefixWord ++ tailWord_3840048).sum := by decide
  have hdescent : baseEnd_3840048 < baseStart_3840048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840065 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3840065 : Nat := 118140960795 + 3840065 * 2 ^ 59
def prefixEnd_3840065 : Nat := 4983230072969 + 3 ^ 40 * 3840065 * 2
def baseEnd_3840065 : Nat := 1971799089507623461727369

theorem tailTrace_3840065 : CollatzResearch.WordTrace tailWord_3840065 prefixEnd_3840065 1971799089507623461727369 := by
  unfold tailWord_3840065
  simp only [CollatzResearch.WordTrace]
  refine ⟨140058676833107810733745649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93372451222071873822497099 140058676833107810733745649)
  ·
    refine ⟨105044007624830858050309237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140058676833107810733745649 105044007624830858050309237)
    ·
      refine ⟨9847875714827892942216491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105044007624830858050309237 9847875714827892942216491)
      ·
        refine ⟨14771813572241839413324737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847875714827892942216491 14771813572241839413324737)
        ·
          refine ⟨11078860179181379559993553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14771813572241839413324737 11078860179181379559993553)
          ·
            refine ⟨8309145134386034669995165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11078860179181379559993553 8309145134386034669995165)
            ·
              refine ⟨3115929425394763001248187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8309145134386034669995165 3115929425394763001248187)
              ·
                refine ⟨4673894138092144501872281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115929425394763001248187 4673894138092144501872281)
                ·
                  refine ⟨3505420603569108376404211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4673894138092144501872281 3505420603569108376404211)
                  ·
                    refine ⟨5258130905353662564606317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3505420603569108376404211 5258130905353662564606317)
                    ·
                      refine ⟨1971799089507623461727369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258130905353662564606317 1971799089507623461727369)
                      ·
                        rfl

theorem cell23_3840065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3840065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840065 prefixEnd_3840065 := by exact prefixLift 3840065
  have htrace : WordTrace (prefixWord ++ tailWord_3840065) baseStart_3840065 baseEnd_3840065 := by
    simpa [prefixWord, tailWord_3840065, baseEnd_3840065] using wordTrace_append hprefix tailTrace_3840065
  have hstable : (prefixWord ++ tailWord_3840065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840065).length < 2 ^ (prefixWord ++ tailWord_3840065).sum := by decide
  have hdescent : baseEnd_3840065 < baseStart_3840065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840067 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_3840067 : Nat := 118140960795 + 3840067 * 2 ^ 59
def prefixEnd_3840067 : Nat := 4983230072969 + 3 ^ 40 * 3840067 * 2
def baseEnd_3840067 : Nat := 1971800116468932453902359

theorem tailTrace_3840067 : CollatzResearch.WordTrace tailWord_3840067 prefixEnd_3840067 1971800116468932453902359 := by
  unfold tailWord_3840067
  simp only [CollatzResearch.WordTrace]
  refine ⟨140058749779100565075318455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93372499852733710050212303 140058749779100565075318455)
  ·
    refine ⟨210088124668650847612977683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140058749779100565075318455 210088124668650847612977683)
    ·
      refine ⟨315132187002976271419466525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210088124668650847612977683 315132187002976271419466525)
      ·
        refine ⟨118174570126116101782299947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315132187002976271419466525 118174570126116101782299947)
        ·
          refine ⟨177261855189174152673449921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118174570126116101782299947 177261855189174152673449921)
          ·
            refine ⟨132946391391880614505087441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177261855189174152673449921 132946391391880614505087441)
            ·
              refine ⟨99709793543910460878815581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132946391391880614505087441 99709793543910460878815581)
              ·
                refine ⟨37391172578966422829555843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99709793543910460878815581 37391172578966422829555843)
                ·
                  refine ⟨56086758868449634244333765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37391172578966422829555843 56086758868449634244333765)
                  ·
                    refine ⟨10516267287834306420812581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56086758868449634244333765 10516267287834306420812581)
                    ·
                      refine ⟨1971800116468932453902359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10516267287834306420812581 1971800116468932453902359)
                      ·
                        rfl

theorem cell23_3840067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_3840067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840067 prefixEnd_3840067 := by exact prefixLift 3840067
  have htrace : WordTrace (prefixWord ++ tailWord_3840067) baseStart_3840067 baseEnd_3840067 := by
    simpa [prefixWord, tailWord_3840067, baseEnd_3840067] using wordTrace_append hprefix tailTrace_3840067
  have hstable : (prefixWord ++ tailWord_3840067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840067).length < 2 ^ (prefixWord ++ tailWord_3840067).sum := by decide
  have hdescent : baseEnd_3840067 < baseStart_3840067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840161 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3840161 : Nat := 118140960795 + 3840161 * 2 ^ 59
def prefixEnd_3840161 : Nat := 4983230072969 + 3 ^ 40 * 3840161 * 2
def baseEnd_3840161 : Nat := 1971848383650455086126927

theorem tailTrace_3840161 : CollatzResearch.WordTrace tailWord_3840161 prefixEnd_3840161 1971848383650455086126927 := by
  unfold tailWord_3840161
  simp only [CollatzResearch.WordTrace]
  refine ⟨140062178240760019129240337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93374785493840012752826891 140062178240760019129240337)
  ·
    refine ⟨105046633680570014346930253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140062178240760019129240337 105046633680570014346930253)
    ·
      refine ⟨39392487630213755380098845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105046633680570014346930253 39392487630213755380098845)
      ·
        refine ⟨14772182861330158267537067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39392487630213755380098845 14772182861330158267537067)
        ·
          refine ⟨22158274291995237401305601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14772182861330158267537067 22158274291995237401305601)
          ·
            refine ⟨16618705718996428050979201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22158274291995237401305601 16618705718996428050979201)
            ·
              refine ⟨12464029289247321038234401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16618705718996428050979201 12464029289247321038234401)
              ·
                refine ⟨9348021966935490778675801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12464029289247321038234401 9348021966935490778675801)
                ·
                  refine ⟨7011016475201618084006851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9348021966935490778675801 7011016475201618084006851)
                  ·
                    refine ⟨10516524712802427126010277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011016475201618084006851 10516524712802427126010277)
                    ·
                      refine ⟨1971848383650455086126927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10516524712802427126010277 1971848383650455086126927)
                      ·
                        rfl

theorem cell23_3840161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3840161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840161 prefixEnd_3840161 := by exact prefixLift 3840161
  have htrace : WordTrace (prefixWord ++ tailWord_3840161) baseStart_3840161 baseEnd_3840161 := by
    simpa [prefixWord, tailWord_3840161, baseEnd_3840161] using wordTrace_append hprefix tailTrace_3840161
  have hstable : (prefixWord ++ tailWord_3840161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840161).length < 2 ^ (prefixWord ++ tailWord_3840161).sum := by decide
  have hdescent : baseEnd_3840161 < baseStart_3840161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840184 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 6]
def baseStart_3840184 : Nat := 118140960795 + 3840184 * 2 ^ 59
def prefixEnd_3840184 : Nat := 4983230072969 + 3 ^ 40 * 3840184 * 2
def baseEnd_3840184 : Nat := 219095577078389832904369

theorem tailTrace_3840184 : CollatzResearch.WordTrace tailWord_3840184 prefixEnd_3840184 219095577078389832904369 := by
  unfold tailWord_3840184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70031508559838347028663803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93375344746451129371551737 70031508559838347028663803)
  ·
    refine ⟨105047262839757520542995705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70031508559838347028663803 105047262839757520542995705)
    ·
      refine ⟨78785447129818140407246779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105047262839757520542995705 78785447129818140407246779)
      ·
        refine ⟨118178170694727210610870169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78785447129818140407246779 118178170694727210610870169)
        ·
          refine ⟨88633628021045407958152627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118178170694727210610870169 88633628021045407958152627)
          ·
            refine ⟨132950442031568111937228941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88633628021045407958152627 132950442031568111937228941)
            ·
              refine ⟨49856415761838041976460853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132950442031568111937228941 49856415761838041976460853)
              ·
                refine ⟨4674038977672316435293205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49856415761838041976460853 4674038977672316435293205)
                ·
                  refine ⟨219095577078389832904369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4674038977672316435293205 219095577078389832904369)
                  ·
                    rfl

theorem cell23_3840184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_3840184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840184 prefixEnd_3840184 := by exact prefixLift 3840184
  have htrace : WordTrace (prefixWord ++ tailWord_3840184) baseStart_3840184 baseEnd_3840184 := by
    simpa [prefixWord, tailWord_3840184, baseEnd_3840184] using wordTrace_append hprefix tailTrace_3840184
  have hstable : (prefixWord ++ tailWord_3840184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840184).length < 2 ^ (prefixWord ++ tailWord_3840184).sum := by decide
  have hdescent : baseEnd_3840184 < baseStart_3840184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840188 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_3840188 : Nat := 118140960795 + 3840188 * 2 ^ 59
def prefixEnd_3840188 : Nat := 4983230072969 + 3 ^ 40 * 3840188 * 2
def baseEnd_3840188 : Nat := 657287415876042160163101

theorem tailTrace_3840188 : CollatzResearch.WordTrace tailWord_3840188 prefixEnd_3840188 657287415876042160163101 := by
  unfold tailWord_3840188
  simp only [CollatzResearch.WordTrace]
  refine ⟨70031581505831101370236609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93375442007774801826982145 70031581505831101370236609)
  ·
    refine ⟨52523686129373326027677457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70031581505831101370236609 52523686129373326027677457)
    ·
      refine ⟨39392764597029994520758093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52523686129373326027677457 39392764597029994520758093)
      ·
        refine ⟨14772286723886247945284285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39392764597029994520758093 14772286723886247945284285)
        ·
          refine ⟨5539607521457342979481607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14772286723886247945284285 5539607521457342979481607)
          ·
            refine ⟨8309411282186014469222411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539607521457342979481607 8309411282186014469222411)
            ·
              refine ⟨12464116923279021703833617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309411282186014469222411 12464116923279021703833617)
              ·
                refine ⟨9348087692459266277875213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12464116923279021703833617 9348087692459266277875213)
                ·
                  refine ⟨3505532884672224854203205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9348087692459266277875213 3505532884672224854203205)
                  ·
                    refine ⟨657287415876042160163101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3505532884672224854203205 657287415876042160163101)
                    ·
                      rfl

theorem cell23_3840188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_3840188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840188 prefixEnd_3840188 := by exact prefixLift 3840188
  have htrace : WordTrace (prefixWord ++ tailWord_3840188) baseStart_3840188 baseEnd_3840188 := by
    simpa [prefixWord, tailWord_3840188, baseEnd_3840188] using wordTrace_append hprefix tailTrace_3840188
  have hstable : (prefixWord ++ tailWord_3840188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840188).length < 2 ^ (prefixWord ++ tailWord_3840188).sum := by decide
  have hdescent : baseEnd_3840188 < baseStart_3840188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840221 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3840221 : Nat := 118140960795 + 3840221 * 2 ^ 59
def prefixEnd_3840221 : Nat := 4983230072969 + 3 ^ 40 * 3840221 * 2
def baseEnd_3840221 : Nat := 1971879192489724851376651

theorem tailTrace_3840221 : CollatzResearch.WordTrace tailWord_3840221 prefixEnd_3840221 1971879192489724851376651 := by
  unfold tailWord_3840221
  simp only [CollatzResearch.WordTrace]
  refine ⟨140064366620542649376424517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93376244413695099584283011 140064366620542649376424517)
  ·
    refine ⟨26262068741351746758079597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140064366620542649376424517 26262068741351746758079597)
    ·
      refine ⟨9848275778006905034279849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26262068741351746758079597 9848275778006905034279849)
      ·
        refine ⟨7386206833505178775709887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9848275778006905034279849 7386206833505178775709887)
        ·
          refine ⟨11079310250257768163564831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386206833505178775709887 11079310250257768163564831)
          ·
            refine ⟨16618965375386652245347247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079310250257768163564831 16618965375386652245347247)
            ·
              refine ⟨24928448063079978368020871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16618965375386652245347247 24928448063079978368020871)
              ·
                refine ⟨37392672094619967552031307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24928448063079978368020871 37392672094619967552031307)
                ·
                  refine ⟨56089008141929951328046961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37392672094619967552031307 56089008141929951328046961)
                  ·
                    refine ⟨42066756106447463496035221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56089008141929951328046961 42066756106447463496035221)
                    ·
                      refine ⟨1971879192489724851376651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42066756106447463496035221 1971879192489724851376651)
                      ·
                        rfl

theorem cell23_3840221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3840221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840221 prefixEnd_3840221 := by exact prefixLift 3840221
  have htrace : WordTrace (prefixWord ++ tailWord_3840221) baseStart_3840221 baseEnd_3840221 := by
    simpa [prefixWord, tailWord_3840221, baseEnd_3840221] using wordTrace_append hprefix tailTrace_3840221
  have hstable : (prefixWord ++ tailWord_3840221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840221).length < 2 ^ (prefixWord ++ tailWord_3840221).sum := by decide
  have hdescent : baseEnd_3840221 < baseStart_3840221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840304 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_3840304 : Nat := 118140960795 + 3840304 * 2 ^ 59
def prefixEnd_3840304 : Nat := 4983230072969 + 3 ^ 40 * 3840304 * 2
def baseEnd_3840304 : Nat := 657307270461349342212923

theorem tailTrace_3840304 : CollatzResearch.WordTrace tailWord_3840304 prefixEnd_3840304 657307270461349342212923 := by
  unfold tailWord_3840304
  simp only [CollatzResearch.WordTrace]
  refine ⟨70033696939620977275847983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93378262586161303034463977 70033696939620977275847983)
  ·
    refine ⟨105050545409431465913771975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70033696939620977275847983 105050545409431465913771975)
    ·
      refine ⟨157575818114147198870657963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105050545409431465913771975 157575818114147198870657963)
      ·
        refine ⟨236363727171220798305986945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157575818114147198870657963 236363727171220798305986945)
        ·
          refine ⟨177272795378415598729490209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236363727171220798305986945 177272795378415598729490209)
          ·
            refine ⟨132954596533811699047117657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177272795378415598729490209 132954596533811699047117657)
            ·
              refine ⟨99715947400358774285338243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132954596533811699047117657 99715947400358774285338243)
              ·
                refine ⟨149573921100538161428007365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99715947400358774285338243 149573921100538161428007365)
                ·
                  refine ⟨28045110206350905267751381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149573921100538161428007365 28045110206350905267751381)
                  ·
                    refine ⟨657307270461349342212923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28045110206350905267751381 657307270461349342212923)
                    ·
                      rfl

theorem cell23_3840304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_3840304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840304 prefixEnd_3840304 := by exact prefixLift 3840304
  have htrace : WordTrace (prefixWord ++ tailWord_3840304) baseStart_3840304 baseEnd_3840304 := by
    simpa [prefixWord, tailWord_3840304, baseEnd_3840304] using wordTrace_append hprefix tailTrace_3840304
  have hstable : (prefixWord ++ tailWord_3840304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840304).length < 2 ^ (prefixWord ++ tailWord_3840304).sum := by decide
  have hdescent : baseEnd_3840304 < baseStart_3840304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840318 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3840318 : Nat := 118140960795 + 3840318 * 2 ^ 59
def prefixEnd_3840318 : Nat := 4983230072969 + 3 ^ 40 * 3840318 * 2
def baseEnd_3840318 : Nat := 1971929000113210971863705

theorem tailTrace_3840318 : CollatzResearch.WordTrace tailWord_3840318 prefixEnd_3840318 1971929000113210971863705 := by
  unfold tailWord_3840318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508488062648904367838201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93378603000794156628470405 17508488062648904367838201)
  ·
    refine ⟨13131366046986678275878651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17508488062648904367838201 13131366046986678275878651)
    ·
      refine ⟨19697049070480017413817977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13131366046986678275878651 19697049070480017413817977)
      ·
        refine ⟨14772786802860013060363483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19697049070480017413817977 14772786802860013060363483)
        ·
          refine ⟨22159180204290019590545225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14772786802860013060363483 22159180204290019590545225)
          ·
            refine ⟨16619385153217514692908919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22159180204290019590545225 16619385153217514692908919)
            ·
              refine ⟨24929077729826272039363379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16619385153217514692908919 24929077729826272039363379)
              ·
                refine ⟨37393616594739408059045069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24929077729826272039363379 37393616594739408059045069)
                ·
                  refine ⟨14022606223027278022141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37393616594739408059045069 14022606223027278022141901)
                  ·
                    refine ⟨5258477333635229258303213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14022606223027278022141901 5258477333635229258303213)
                    ·
                      refine ⟨1971929000113210971863705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258477333635229258303213 1971929000113210971863705)
                      ·
                        rfl

theorem cell23_3840318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3840318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840318 prefixEnd_3840318 := by exact prefixLift 3840318
  have htrace : WordTrace (prefixWord ++ tailWord_3840318) baseStart_3840318 baseEnd_3840318 := by
    simpa [prefixWord, tailWord_3840318, baseEnd_3840318] using wordTrace_append hprefix tailTrace_3840318
  have hstable : (prefixWord ++ tailWord_3840318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840318).length < 2 ^ (prefixWord ++ tailWord_3840318).sum := by decide
  have hdescent : baseEnd_3840318 < baseStart_3840318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840361 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_3840361 : Nat := 118140960795 + 3840361 * 2 ^ 59
def prefixEnd_3840361 : Nat := 4983230072969 + 3 ^ 40 * 3840361 * 2
def baseEnd_3840361 : Nat := 1971951079781354303626007

theorem tailTrace_3840361 : CollatzResearch.WordTrace tailWord_3840361 prefixEnd_3840361 1971951079781354303626007 := by
  unfold tailWord_3840361
  simp only [CollatzResearch.WordTrace]
  refine ⟨140069472840035453286520937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93379648560023635524347291 140069472840035453286520937)
  ·
    refine ⟨105052104630026589964890703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140069472840035453286520937 105052104630026589964890703)
    ·
      refine ⟨157578156945039884947336055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105052104630026589964890703 157578156945039884947336055)
      ·
        refine ⟨236367235417559827421004083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157578156945039884947336055 236367235417559827421004083)
        ·
          refine ⟨354550853126339741131506125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236367235417559827421004083 354550853126339741131506125)
          ·
            refine ⟨132956569922377402924314797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354550853126339741131506125 132956569922377402924314797)
            ·
              refine ⟨49858713720891526096618049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132956569922377402924314797 49858713720891526096618049)
              ·
                refine ⟨37394035290668644572463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49858713720891526096618049 37394035290668644572463537)
                ·
                  refine ⟨28045526468001483429347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37394035290668644572463537 28045526468001483429347653)
                  ·
                    refine ⟨5258536212750278143002685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28045526468001483429347653 5258536212750278143002685)
                    ·
                      refine ⟨1971951079781354303626007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258536212750278143002685 1971951079781354303626007)
                      ·
                        rfl

theorem cell23_3840361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_3840361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840361 prefixEnd_3840361 := by exact prefixLift 3840361
  have htrace : WordTrace (prefixWord ++ tailWord_3840361) baseStart_3840361 baseEnd_3840361 := by
    simpa [prefixWord, tailWord_3840361, baseEnd_3840361] using wordTrace_append hprefix tailTrace_3840361
  have hstable : (prefixWord ++ tailWord_3840361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840361).length < 2 ^ (prefixWord ++ tailWord_3840361).sum := by decide
  have hdescent : baseEnd_3840361 < baseStart_3840361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840386 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3840386 : Nat := 118140960795 + 3840386 * 2 ^ 59
def prefixEnd_3840386 : Nat := 4983230072969 + 3 ^ 40 * 3840386 * 2
def baseEnd_3840386 : Nat := 1971963916797716705813393

theorem tailTrace_3840386 : CollatzResearch.WordTrace tailWord_3840386 prefixEnd_3840386 1971963916797716705813393 := by
  unfold tailWord_3840386
  simp only [CollatzResearch.WordTrace]
  refine ⟨35017596166236220639045253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93380256443296588370787341 35017596166236220639045253)
  ·
    refine ⟨6565799281169291369820985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35017596166236220639045253 6565799281169291369820985)
    ·
      refine ⟨4924349460876968527365739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565799281169291369820985 4924349460876968527365739)
      ·
        refine ⟨7386524191315452791048609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924349460876968527365739 7386524191315452791048609)
        ·
          refine ⟨5539893143486589593286457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7386524191315452791048609 5539893143486589593286457)
          ·
            refine ⟨4154919857614942194964843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5539893143486589593286457 4154919857614942194964843)
            ·
              refine ⟨6232379786422413292447265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154919857614942194964843 6232379786422413292447265)
              ·
                refine ⟨4674284839816809969335449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232379786422413292447265 4674284839816809969335449)
                ·
                  refine ⟨3505713629862607477001587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4674284839816809969335449 3505713629862607477001587)
                  ·
                    refine ⟨5258570444793911215502381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3505713629862607477001587 5258570444793911215502381)
                    ·
                      refine ⟨1971963916797716705813393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258570444793911215502381 1971963916797716705813393)
                      ·
                        rfl

theorem cell23_3840386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3840386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840386 prefixEnd_3840386 := by exact prefixLift 3840386
  have htrace : WordTrace (prefixWord ++ tailWord_3840386) baseStart_3840386 baseEnd_3840386 := by
    simpa [prefixWord, tailWord_3840386, baseEnd_3840386] using wordTrace_append hprefix tailTrace_3840386
  have hstable : (prefixWord ++ tailWord_3840386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840386).length < 2 ^ (prefixWord ++ tailWord_3840386).sum := by decide
  have hdescent : baseEnd_3840386 < baseStart_3840386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840398 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_3840398 : Nat := 118140960795 + 3840398 * 2 ^ 59
def prefixEnd_3840398 : Nat := 4983230072969 + 3 ^ 40 * 3840398 * 2
def baseEnd_3840398 : Nat := 219107786507285628762593

theorem tailTrace_3840398 : CollatzResearch.WordTrace tailWord_3840398 prefixEnd_3840398 219107786507285628762593 := by
  unfold tailWord_3840398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508852792612676075702231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93380548227267605737078565 17508852792612676075702231)
  ·
    refine ⟨26263279188919014113553347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17508852792612676075702231 26263279188919014113553347)
    ·
      refine ⟨39394918783378521170330021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26263279188919014113553347 39394918783378521170330021)
      ·
        refine ⟨7386547271883472719436879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39394918783378521170330021 7386547271883472719436879)
        ·
          refine ⟨11079820907825209079155319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386547271883472719436879 11079820907825209079155319)
          ·
            refine ⟨16619731361737813618732979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079820907825209079155319 16619731361737813618732979)
            ·
              refine ⟨24929597042606720428099469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16619731361737813618732979 24929597042606720428099469)
              ·
                refine ⟨9348598890977520160537301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24929597042606720428099469 9348598890977520160537301)
                ·
                  refine ⟨219107786507285628762593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9348598890977520160537301 219107786507285628762593)
                  ·
                    rfl

theorem cell23_3840398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_3840398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840398 prefixEnd_3840398 := by exact prefixLift 3840398
  have htrace : WordTrace (prefixWord ++ tailWord_3840398) baseStart_3840398 baseEnd_3840398 := by
    simpa [prefixWord, tailWord_3840398, baseEnd_3840398] using wordTrace_append hprefix tailTrace_3840398
  have hstable : (prefixWord ++ tailWord_3840398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840398).length < 2 ^ (prefixWord ++ tailWord_3840398).sum := by decide
  have hdescent : baseEnd_3840398 < baseStart_3840398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840449 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 7]
def baseStart_3840449 : Nat := 118140960795 + 3840449 * 2 ^ 59
def prefixEnd_3840449 : Nat := 4983230072969 + 3 ^ 40 * 3840449 * 2
def baseEnd_3840449 : Nat := 219110696230994439925067

theorem tailTrace_3840449 : CollatzResearch.WordTrace tailWord_3840449 prefixEnd_3840449 219110696230994439925067 := by
  unfold tailWord_3840449
  simp only [CollatzResearch.WordTrace]
  refine ⟨140072682463716644315724401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93381788309144429543816267 140072682463716644315724401)
  ·
    refine ⟨105054511847787483236793301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140072682463716644315724401 105054511847787483236793301)
    ·
      refine ⟨2462215121432519138362343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 105054511847787483236793301 2462215121432519138362343)
      ·
        refine ⟨3693322682148778707543515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462215121432519138362343 3693322682148778707543515)
        ·
          refine ⟨5539984023223168061315273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693322682148778707543515 5539984023223168061315273)
          ·
            refine ⟨4154988017417376045986455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5539984023223168061315273 4154988017417376045986455)
            ·
              refine ⟨6232482026126064068979683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154988017417376045986455 6232482026126064068979683)
              ·
                refine ⟨9348723039189096103469525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232482026126064068979683 9348723039189096103469525)
                ·
                  refine ⟨219110696230994439925067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9348723039189096103469525 219110696230994439925067)
                  ·
                    rfl

theorem cell23_3840449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 7].length) (baseStart_3840449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840449 prefixEnd_3840449 := by exact prefixLift 3840449
  have htrace : WordTrace (prefixWord ++ tailWord_3840449) baseStart_3840449 baseEnd_3840449 := by
    simpa [prefixWord, tailWord_3840449, baseEnd_3840449] using wordTrace_append hprefix tailTrace_3840449
  have hstable : (prefixWord ++ tailWord_3840449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840449).length < 2 ^ (prefixWord ++ tailWord_3840449).sum := by decide
  have hdescent : baseEnd_3840449 < baseStart_3840449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840515 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 3]
def baseStart_3840515 : Nat := 118140960795 + 3840515 * 2 ^ 59
def prefixEnd_3840515 : Nat := 4983230072969 + 3 ^ 40 * 3840515 * 2
def baseEnd_3840515 : Nat := 1972030155802146701100299

theorem tailTrace_3840515 : CollatzResearch.WordTrace tailWord_3840515 prefixEnd_3840515 1972030155802146701100299 := by
  unfold tailWord_3840515
  simp only [CollatzResearch.WordTrace]
  refine ⟨140075089681477537587626999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93383393120985025058417999 140075089681477537587626999)
  ·
    refine ⟨210112634522216306381440499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140075089681477537587626999 210112634522216306381440499)
    ·
      refine ⟨315168951783324459572160749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210112634522216306381440499 315168951783324459572160749)
      ·
        refine ⟨118188356918746672339560281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315168951783324459572160749 118188356918746672339560281)
        ·
          refine ⟨88641267689060004254670211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118188356918746672339560281 88641267689060004254670211)
          ·
            refine ⟨132961901533590006382005317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88641267689060004254670211 132961901533590006382005317)
            ·
              refine ⟨24930356537548126196625997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132961901533590006382005317 24930356537548126196625997)
              ·
                refine ⟨9348883701580547323734749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24930356537548126196625997 9348883701580547323734749)
                ·
                  refine ⟨3505831388092705246400531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9348883701580547323734749 3505831388092705246400531)
                  ·
                    refine ⟨5258747082139057869600797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3505831388092705246400531 5258747082139057869600797)
                    ·
                      refine ⟨1972030155802146701100299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258747082139057869600797 1972030155802146701100299)
                      ·
                        rfl

theorem cell23_3840515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_3840515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840515 prefixEnd_3840515 := by exact prefixLift 3840515
  have htrace : WordTrace (prefixWord ++ tailWord_3840515) baseStart_3840515 baseEnd_3840515 := by
    simpa [prefixWord, tailWord_3840515, baseEnd_3840515] using wordTrace_append hprefix tailTrace_3840515
  have hstable : (prefixWord ++ tailWord_3840515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840515).length < 2 ^ (prefixWord ++ tailWord_3840515).sum := by decide
  have hdescent : baseEnd_3840515 < baseStart_3840515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840552 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3840552 : Nat := 118140960795 + 3840552 * 2 ^ 59
def prefixEnd_3840552 : Nat := 4983230072969 + 3 ^ 40 * 3840552 * 2
def baseEnd_3840552 : Nat := 657349718195454352112543

theorem tailTrace_3840552 : CollatzResearch.WordTrace tailWord_3840552 prefixEnd_3840552 657349718195454352112543 := by
  unfold tailWord_3840552
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038219591171746453361955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93384292788228995271149273 70038219591171746453361955)
  ·
    refine ⟨105057329386757619680042933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70038219591171746453361955 105057329386757619680042933)
    ·
      refine ⟨9849124630008526845004025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105057329386757619680042933 9849124630008526845004025)
      ·
        refine ⟨7386843472506395133753019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9849124630008526845004025 7386843472506395133753019)
        ·
          refine ⟨11080265208759592700629529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386843472506395133753019 11080265208759592700629529)
          ·
            refine ⟨8310198906569694525472147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11080265208759592700629529 8310198906569694525472147)
            ·
              refine ⟨12465298359854541788208221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310198906569694525472147 12465298359854541788208221)
              ·
                refine ⟨4674486884945453170578083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12465298359854541788208221 4674486884945453170578083)
                ·
                  refine ⟨7011730327418179755867125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674486884945453170578083 7011730327418179755867125)
                  ·
                    refine ⟨657349718195454352112543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7011730327418179755867125 657349718195454352112543)
                    ·
                      rfl

theorem cell23_3840552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3840552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840552 prefixEnd_3840552 := by exact prefixLift 3840552
  have htrace : WordTrace (prefixWord ++ tailWord_3840552) baseStart_3840552 baseEnd_3840552 := by
    simpa [prefixWord, tailWord_3840552, baseEnd_3840552] using wordTrace_append hprefix tailTrace_3840552
  have hstable : (prefixWord ++ tailWord_3840552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840552).length < 2 ^ (prefixWord ++ tailWord_3840552).sum := by decide
  have hdescent : baseEnd_3840552 < baseStart_3840552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840565 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3840565 : Nat := 118140960795 + 3840565 * 2 ^ 59
def prefixEnd_3840565 : Nat := 4983230072969 + 3 ^ 40 * 3840565 * 2
def baseEnd_3840565 : Nat := 657351943278290501825023

theorem tailTrace_3840565 : CollatzResearch.WordTrace tailWord_3840565 prefixEnd_3840565 657351943278290501825023 := by
  unfold tailWord_3840565
  simp only [CollatzResearch.WordTrace]
  refine ⟨140076913331296396126947149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93384608887530930751298099 140076913331296396126947149)
  ·
    refine ⟨52528842499236148547605181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140076913331296396126947149 52528842499236148547605181)
    ·
      refine ⟨19698315937213555705351943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52528842499236148547605181 19698315937213555705351943)
      ·
        refine ⟨29547473905820333558027915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19698315937213555705351943 29547473905820333558027915)
        ·
          refine ⟨44321210858730500337041873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29547473905820333558027915 44321210858730500337041873)
          ·
            refine ⟨33240908144047875252781405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44321210858730500337041873 33240908144047875252781405)
            ·
              refine ⟨12465340554017953219793027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33240908144047875252781405 12465340554017953219793027)
              ·
                refine ⟨18698010831026929829689541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12465340554017953219793027 18698010831026929829689541)
                ·
                  refine ⟨3505877030817549343066789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18698010831026929829689541 3505877030817549343066789)
                  ·
                    refine ⟨657351943278290501825023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3505877030817549343066789 657351943278290501825023)
                    ·
                      rfl

theorem cell23_3840565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3840565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840565 prefixEnd_3840565 := by exact prefixLift 3840565
  have htrace : WordTrace (prefixWord ++ tailWord_3840565) baseStart_3840565 baseEnd_3840565 := by
    simpa [prefixWord, tailWord_3840565, baseEnd_3840565] using wordTrace_append hprefix tailTrace_3840565
  have hstable : (prefixWord ++ tailWord_3840565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840565).length < 2 ^ (prefixWord ++ tailWord_3840565).sum := by decide
  have hdescent : baseEnd_3840565 < baseStart_3840565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840566 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_3840566 : Nat := 118140960795 + 3840566 * 2 ^ 59
def prefixEnd_3840566 : Nat := 4983230072969 + 3 ^ 40 * 3840566 * 2
def baseEnd_3840566 : Nat := 1972056343315526001562565

theorem tailTrace_3840566 : CollatzResearch.WordTrace tailWord_3840566 prefixEnd_3840566 1972056343315526001562565 := by
  unfold tailWord_3840566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754809362768298331108347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93384633202861848865155701 8754809362768298331108347)
  ·
    refine ⟨13132214044152447496662521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8754809362768298331108347 13132214044152447496662521)
    ·
      refine ⟨9849160533114335622496891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13132214044152447496662521 9849160533114335622496891)
      ·
        refine ⟨14773740799671503433745337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849160533114335622496891 14773740799671503433745337)
        ·
          refine ⟨11080305599753627575309003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14773740799671503433745337 11080305599753627575309003)
          ·
            refine ⟨16620458399630441362963505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11080305599753627575309003 16620458399630441362963505)
            ·
              refine ⟨12465343799722831022222629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16620458399630441362963505 12465343799722831022222629)
              ·
                refine ⟨2337251962448030816666743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12465343799722831022222629 2337251962448030816666743)
                ·
                  refine ⟨3505877943672046225000115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337251962448030816666743 3505877943672046225000115)
                  ·
                    refine ⟨5258816915508069337500173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3505877943672046225000115 5258816915508069337500173)
                    ·
                      refine ⟨1972056343315526001562565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5258816915508069337500173 1972056343315526001562565)
                      ·
                        rfl

theorem cell23_3840566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_3840566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840566 prefixEnd_3840566 := by exact prefixLift 3840566
  have htrace : WordTrace (prefixWord ++ tailWord_3840566) baseStart_3840566 baseEnd_3840566 := by
    simpa [prefixWord, tailWord_3840566, baseEnd_3840566] using wordTrace_append hprefix tailTrace_3840566
  have hstable : (prefixWord ++ tailWord_3840566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840566).length < 2 ^ (prefixWord ++ tailWord_3840566).sum := by decide
  have hdescent : baseEnd_3840566 < baseStart_3840566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840568 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_3840568 : Nat := 118140960795 + 3840568 * 2 ^ 59
def prefixEnd_3840568 : Nat := 4983230072969 + 3 ^ 40 * 3840568 * 2
def baseEnd_3840568 : Nat := 1972057370276834993737555

theorem tailTrace_3840568 : CollatzResearch.WordTrace tailWord_3840568 prefixEnd_3840568 1972057370276834993737555 := by
  unfold tailWord_3840568
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038511375142763819653179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93384681833523685092870905 70038511375142763819653179)
  ·
    refine ⟨105057767062714145729479769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70038511375142763819653179 105057767062714145729479769)
    ·
      refine ⟨78793325297035609297109827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105057767062714145729479769 78793325297035609297109827)
      ·
        refine ⟨118189987945553413945664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78793325297035609297109827 118189987945553413945664741)
        ·
          refine ⟨22160622739791265114812139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118189987945553413945664741 22160622739791265114812139)
          ·
            refine ⟨33240934109686897672218209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22160622739791265114812139 33240934109686897672218209)
            ·
              refine ⟨24930700582265173254163657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33240934109686897672218209 24930700582265173254163657)
              ·
                refine ⟨18698025436698879940622743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24930700582265173254163657 18698025436698879940622743)
                ·
                  refine ⟨28047038155048319910934115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698025436698879940622743 28047038155048319910934115)
                  ·
                    refine ⟨42070557232572479866401173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28047038155048319910934115 42070557232572479866401173)
                    ·
                      refine ⟨1972057370276834993737555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42070557232572479866401173 1972057370276834993737555)
                      ·
                        rfl

theorem cell23_3840568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_3840568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840568 prefixEnd_3840568 := by exact prefixLift 3840568
  have htrace : WordTrace (prefixWord ++ tailWord_3840568) baseStart_3840568 baseEnd_3840568 := by
    simpa [prefixWord, tailWord_3840568, baseEnd_3840568] using wordTrace_append hprefix tailTrace_3840568
  have hstable : (prefixWord ++ tailWord_3840568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840568).length < 2 ^ (prefixWord ++ tailWord_3840568).sum := by decide
  have hdescent : baseEnd_3840568 < baseStart_3840568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840589 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3840589 : Nat := 118140960795 + 3840589 * 2 ^ 59
def prefixEnd_3840589 : Nat := 4983230072969 + 3 ^ 40 * 3840589 * 2
def baseEnd_3840589 : Nat := 1972068153370579411574959

theorem tailTrace_3840589 : CollatzResearch.WordTrace tailWord_3840589 prefixEnd_3840589 1972068153370579411574959 := by
  unfold tailWord_3840589
  simp only [CollatzResearch.WordTrace]
  refine ⟨140077788683209448225820821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93385192455472965483880547 140077788683209448225820821)
  ·
    refine ⟨6566146344525442885585351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140077788683209448225820821 6566146344525442885585351)
    ·
      refine ⟨9849219516788164328378027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6566146344525442885585351 9849219516788164328378027)
      ·
        refine ⟨14773829275182246492567041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849219516788164328378027 14773829275182246492567041)
        ·
          refine ⟨11080371956386684869425281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14773829275182246492567041 11080371956386684869425281)
          ·
            refine ⟨8310278967290013652068961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11080371956386684869425281 8310278967290013652068961)
            ·
              refine ⟨6232709225467510239051721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8310278967290013652068961 6232709225467510239051721)
              ·
                refine ⟨4674531919100632679288791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232709225467510239051721 4674531919100632679288791)
                ·
                  refine ⟨7011797878650949018933187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674531919100632679288791 7011797878650949018933187)
                  ·
                    refine ⟨10517696817976423528399781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011797878650949018933187 10517696817976423528399781)
                    ·
                      refine ⟨1972068153370579411574959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10517696817976423528399781 1972068153370579411574959)
                      ·
                        rfl

theorem cell23_3840589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3840589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840589 prefixEnd_3840589 := by exact prefixLift 3840589
  have htrace : WordTrace (prefixWord ++ tailWord_3840589) baseStart_3840589 baseEnd_3840589 := by
    simpa [prefixWord, tailWord_3840589, baseEnd_3840589] using wordTrace_append hprefix tailTrace_3840589
  have hstable : (prefixWord ++ tailWord_3840589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840589).length < 2 ^ (prefixWord ++ tailWord_3840589).sum := by decide
  have hdescent : baseEnd_3840589 < baseStart_3840589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840688 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_3840688 : Nat := 118140960795 + 3840688 * 2 ^ 59
def prefixEnd_3840688 : Nat := 4983230072969 + 3 ^ 40 * 3840688 * 2
def baseEnd_3840688 : Nat := 1972118987955374524237003

theorem tailTrace_3840688 : CollatzResearch.WordTrace tailWord_3840688 prefixEnd_3840688 1972118987955374524237003 := by
  unfold tailWord_3840688
  simp only [CollatzResearch.WordTrace]
  refine ⟨70040699754925394066837359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93387599673233858755783145 70040699754925394066837359)
  ·
    refine ⟨105061049632388091100256039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70040699754925394066837359 105061049632388091100256039)
    ·
      refine ⟨157591574448582136650384059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105061049632388091100256039 157591574448582136650384059)
      ·
        refine ⟨236387361672873204975576089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157591574448582136650384059 236387361672873204975576089)
        ·
          refine ⟨177290521254654903731682067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236387361672873204975576089 177290521254654903731682067)
          ·
            refine ⟨265935781881982355597523101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177290521254654903731682067 265935781881982355597523101)
            ·
              refine ⟨99725918205743383349071163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265935781881982355597523101 99725918205743383349071163)
              ·
                refine ⟨149588877308615075023606745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99725918205743383349071163 149588877308615075023606745)
                ·
                  refine ⟨112191657981461306267705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149588877308615075023606745 112191657981461306267705059)
                  ·
                    refine ⟨168287486972191959401557589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112191657981461306267705059 168287486972191959401557589)
                    ·
                      refine ⟨1972118987955374524237003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168287486972191959401557589 1972118987955374524237003)
                      ·
                        rfl

theorem cell23_3840688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_3840688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840688 prefixEnd_3840688 := by exact prefixLift 3840688
  have htrace : WordTrace (prefixWord ++ tailWord_3840688) baseStart_3840688 baseEnd_3840688 := by
    simpa [prefixWord, tailWord_3840688, baseEnd_3840688] using wordTrace_append hprefix tailTrace_3840688
  have hstable : (prefixWord ++ tailWord_3840688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840688).length < 2 ^ (prefixWord ++ tailWord_3840688).sum := by decide
  have hdescent : baseEnd_3840688 < baseStart_3840688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840717 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3840717 : Nat := 118140960795 + 3840717 * 2 ^ 59
def prefixEnd_3840717 : Nat := 4983230072969 + 3 ^ 40 * 3840717 * 2
def baseEnd_3840717 : Nat := 1972133878894354910774371

theorem tailTrace_3840717 : CollatzResearch.WordTrace tailWord_3840717 prefixEnd_3840717 1972133878894354910774371 := by
  unfold tailWord_3840717
  simp only [CollatzResearch.WordTrace]
  refine ⟨140082457226745726086480405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93388304817830484057653603 140082457226745726086480405)
  ·
    refine ⟨6566365182503705910303769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140082457226745726086480405 6566365182503705910303769)
    ·
      refine ⟨4924773886877779432727827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6566365182503705910303769 4924773886877779432727827)
      ·
        refine ⟨7387160830316669149091741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924773886877779432727827 7387160830316669149091741)
        ·
          refine ⟨2770185311368750930909403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7387160830316669149091741 2770185311368750930909403)
          ·
            refine ⟨4155277967053126396364105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770185311368750930909403 4155277967053126396364105)
            ·
              refine ⟨3116458475289844797273079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155277967053126396364105 3116458475289844797273079)
              ·
                refine ⟨4674687712934767195909619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116458475289844797273079 4674687712934767195909619)
                ·
                  refine ⟨7012031569402150793864429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674687712934767195909619 7012031569402150793864429)
                  ·
                    refine ⟨2629511838525806547699161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7012031569402150793864429 2629511838525806547699161)
                    ·
                      refine ⟨1972133878894354910774371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629511838525806547699161 1972133878894354910774371)
                      ·
                        rfl

theorem cell23_3840717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3840717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840717 prefixEnd_3840717 := by exact prefixLift 3840717
  have htrace : WordTrace (prefixWord ++ tailWord_3840717) baseStart_3840717 baseEnd_3840717 := by
    simpa [prefixWord, tailWord_3840717, baseEnd_3840717] using wordTrace_append hprefix tailTrace_3840717
  have hstable : (prefixWord ++ tailWord_3840717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840717).length < 2 ^ (prefixWord ++ tailWord_3840717).sum := by decide
  have hdescent : baseEnd_3840717 < baseStart_3840717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840752 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2]
def baseStart_3840752 : Nat := 118140960795 + 3840752 * 2 ^ 59
def prefixEnd_3840752 : Nat := 4983230072969 + 3 ^ 40 * 3840752 * 2
def baseEnd_3840752 : Nat := 1972151850717262273836709

theorem tailTrace_3840752 : CollatzResearch.WordTrace tailWord_3840752 prefixEnd_3840752 1972151850717262273836709 := by
  unfold tailWord_3840752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70041866890809463532002255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93389155854412618042669673 70041866890809463532002255)
  ·
    refine ⟨105062800336214195298003383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70041866890809463532002255 105062800336214195298003383)
    ·
      refine ⟨157594200504321292947005075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105062800336214195298003383 157594200504321292947005075)
      ·
        refine ⟨236391300756481939420507613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157594200504321292947005075 236391300756481939420507613)
        ·
          refine ⟨88646737783680727282690355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236391300756481939420507613 88646737783680727282690355)
          ·
            refine ⟨132970106675521090924035533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88646737783680727282690355 132970106675521090924035533)
            ·
              refine ⟨49863790003320409096513325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132970106675521090924035533 49863790003320409096513325)
              ·
                refine ⟨18698921251245153411192497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49863790003320409096513325 18698921251245153411192497)
                ·
                  refine ⟨14024190938433865058394373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18698921251245153411192497 14024190938433865058394373)
                  ·
                    refine ⟨2629535800956349698448945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14024190938433865058394373 2629535800956349698448945)
                    ·
                      refine ⟨1972151850717262273836709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629535800956349698448945 1972151850717262273836709)
                      ·
                        rfl

theorem cell23_3840752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2].length) (baseStart_3840752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840752 prefixEnd_3840752 := by exact prefixLift 3840752
  have htrace : WordTrace (prefixWord ++ tailWord_3840752) baseStart_3840752 baseEnd_3840752 := by
    simpa [prefixWord, tailWord_3840752, baseEnd_3840752] using wordTrace_append hprefix tailTrace_3840752
  have hstable : (prefixWord ++ tailWord_3840752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840752).length < 2 ^ (prefixWord ++ tailWord_3840752).sum := by decide
  have hdescent : baseEnd_3840752 < baseStart_3840752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840762 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_3840762 : Nat := 118140960795 + 3840762 * 2 ^ 59
def prefixEnd_3840762 : Nat := 4983230072969 + 3 ^ 40 * 3840762 * 2
def baseEnd_3840762 : Nat := 657385661841269078237221

theorem tailTrace_3840762 : CollatzResearch.WordTrace tailWord_3840762 prefixEnd_3840762 657385661841269078237221 := by
  unfold tailWord_3840762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35021024627895674692967135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93389399007721799181245693 35021024627895674692967135)
  ·
    refine ⟨52531536941843512039450703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35021024627895674692967135 52531536941843512039450703)
    ·
      refine ⟨78797305412765268059176055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52531536941843512039450703 78797305412765268059176055)
      ·
        refine ⟨118195958119147902088764083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78797305412765268059176055 118195958119147902088764083)
        ·
          refine ⟨177293937178721853133146125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118195958119147902088764083 177293937178721853133146125)
          ·
            refine ⟨66485226442020694924929797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177293937178721853133146125 66485226442020694924929797)
            ·
              refine ⟨12465979957878880298424337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66485226442020694924929797 12465979957878880298424337)
              ·
                refine ⟨9349484968409160223818253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12465979957878880298424337 9349484968409160223818253)
                ·
                  refine ⟨3506056863153435083931845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9349484968409160223818253 3506056863153435083931845)
                  ·
                    refine ⟨657385661841269078237221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3506056863153435083931845 657385661841269078237221)
                    ·
                      rfl

theorem cell23_3840762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_3840762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840762 prefixEnd_3840762 := by exact prefixLift 3840762
  have htrace : WordTrace (prefixWord ++ tailWord_3840762) baseStart_3840762 baseEnd_3840762 := by
    simpa [prefixWord, tailWord_3840762, baseEnd_3840762] using wordTrace_append hprefix tailTrace_3840762
  have hstable : (prefixWord ++ tailWord_3840762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840762).length < 2 ^ (prefixWord ++ tailWord_3840762).sum := by decide
  have hdescent : baseEnd_3840762 < baseStart_3840762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840765 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3840765 : Nat := 118140960795 + 3840765 * 2 ^ 59
def prefixEnd_3840765 : Nat := 4983230072969 + 3 ^ 40 * 3840765 * 2
def baseEnd_3840765 : Nat := 1972158525965770722974149

theorem tailTrace_3840765 : CollatzResearch.WordTrace tailWord_3840765 prefixEnd_3840765 1972158525965770722974149 := by
  unfold tailWord_3840765
  simp only [CollatzResearch.WordTrace]
  refine ⟨140084207930571830284227749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93389471953714553522818499 140084207930571830284227749)
  ·
    refine ⟨26265788986982218178292703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140084207930571830284227749 26265788986982218178292703)
    ·
      refine ⟨39398683480473327267439055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26265788986982218178292703 39398683480473327267439055)
      ·
        refine ⟨59098025220709990901158583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39398683480473327267439055 59098025220709990901158583)
        ·
          refine ⟨88647037831064986351737875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59098025220709990901158583 88647037831064986351737875)
          ·
            refine ⟨132970556746597479527606813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88647037831064986351737875 132970556746597479527606813)
            ·
              refine ⟨49863958779974054822852555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132970556746597479527606813 49863958779974054822852555)
              ·
                refine ⟨74795938169961082234278833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49863958779974054822852555 74795938169961082234278833)
                ·
                  refine ⟨56096953627470811675709125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74795938169961082234278833 56096953627470811675709125)
                  ·
                    refine ⟨10518178805150777189195461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56096953627470811675709125 10518178805150777189195461)
                    ·
                      refine ⟨1972158525965770722974149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10518178805150777189195461 1972158525965770722974149)
                      ·
                        rfl

theorem cell23_3840765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3840765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840765 prefixEnd_3840765 := by exact prefixLift 3840765
  have htrace : WordTrace (prefixWord ++ tailWord_3840765) baseStart_3840765 baseEnd_3840765 := by
    simpa [prefixWord, tailWord_3840765, baseEnd_3840765] using wordTrace_append hprefix tailTrace_3840765
  have hstable : (prefixWord ++ tailWord_3840765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840765).length < 2 ^ (prefixWord ++ tailWord_3840765).sum := by decide
  have hdescent : baseEnd_3840765 < baseStart_3840765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840772 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3840772 : Nat := 118140960795 + 3840772 * 2 ^ 59
def prefixEnd_3840772 : Nat := 4983230072969 + 3 ^ 40 * 3840772 * 2
def baseEnd_3840772 : Nat := 1972162120330352195586617

theorem tailTrace_3840772 : CollatzResearch.WordTrace tailWord_3840772 prefixEnd_3840772 1972162120330352195586617 := by
  unfold tailWord_3840772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70042231620773235239866285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93389642161030980319821713 70042231620773235239866285)
  ·
    refine ⟨26265836857789963214949857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70042231620773235239866285 26265836857789963214949857)
    ·
      refine ⟨19699377643342472411212393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26265836857789963214949857 19699377643342472411212393)
      ·
        refine ⟨14774533232506854308409295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19699377643342472411212393 14774533232506854308409295)
        ·
          refine ⟨22161799848760281462613943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774533232506854308409295 22161799848760281462613943)
          ·
            refine ⟨33242699773140422193920915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22161799848760281462613943 33242699773140422193920915)
            ·
              refine ⟨49864049659710633290881373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33242699773140422193920915 49864049659710633290881373)
              ·
                refine ⟨18699018622391487484080515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49864049659710633290881373 18699018622391487484080515)
                ·
                  refine ⟨28048527933587231226120773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18699018622391487484080515 28048527933587231226120773)
                  ·
                    refine ⟨5259098987547605854897645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28048527933587231226120773 5259098987547605854897645)
                    ·
                      refine ⟨1972162120330352195586617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5259098987547605854897645 1972162120330352195586617)
                      ·
                        rfl

theorem cell23_3840772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3840772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840772 prefixEnd_3840772 := by exact prefixLift 3840772
  have htrace : WordTrace (prefixWord ++ tailWord_3840772) baseStart_3840772 baseEnd_3840772 := by
    simpa [prefixWord, tailWord_3840772, baseEnd_3840772] using wordTrace_append hprefix tailTrace_3840772
  have hstable : (prefixWord ++ tailWord_3840772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840772).length < 2 ^ (prefixWord ++ tailWord_3840772).sum := by decide
  have hdescent : baseEnd_3840772 < baseStart_3840772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840786 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3840786 : Nat := 118140960795 + 3840786 * 2 ^ 59
def prefixEnd_3840786 : Nat := 4983230072969 + 3 ^ 40 * 3840786 * 2
def baseEnd_3840786 : Nat := 1972169309059515140811553

theorem tailTrace_3840786 : CollatzResearch.WordTrace tailWord_3840786 prefixEnd_3840786 1972169309059515140811553 := by
  unfold tailWord_3840786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35021243465873937717685553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93389982575663833913828141 35021243465873937717685553)
  ·
    refine ⟨26265932599405453288264165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35021243465873937717685553 26265932599405453288264165)
    ·
      refine ⟨4924862362388522491549531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26265932599405453288264165 4924862362388522491549531)
      ·
        refine ⟨7387293543582783737324297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924862362388522491549531 7387293543582783737324297)
        ·
          refine ⟨5540470157687087802993223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7387293543582783737324297 5540470157687087802993223)
          ·
            refine ⟨8310705236530631704489835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540470157687087802993223 8310705236530631704489835)
            ·
              refine ⟨12466057854795947556734753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310705236530631704489835 12466057854795947556734753)
              ·
                refine ⟨9349543391096960667551065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12466057854795947556734753 9349543391096960667551065)
                ·
                  refine ⟨7012157543322720500663299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9349543391096960667551065 7012157543322720500663299)
                  ·
                    refine ⟨10518236314984080750994949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012157543322720500663299 10518236314984080750994949)
                    ·
                      refine ⟨1972169309059515140811553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10518236314984080750994949 1972169309059515140811553)
                      ·
                        rfl

theorem cell23_3840786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3840786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840786 prefixEnd_3840786 := by exact prefixLift 3840786
  have htrace : WordTrace (prefixWord ++ tailWord_3840786) baseStart_3840786 baseEnd_3840786 := by
    simpa [prefixWord, tailWord_3840786, baseEnd_3840786] using wordTrace_append hprefix tailTrace_3840786
  have hstable : (prefixWord ++ tailWord_3840786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840786).length < 2 ^ (prefixWord ++ tailWord_3840786).sum := by decide
  have hdescent : baseEnd_3840786 < baseStart_3840786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840865 : List Nat := [1, 2, 3, 1, 1, 1, 2, 12]
def baseStart_3840865 : Nat := 118140960795 + 3840865 * 2 ^ 59
def prefixEnd_3840865 : Nat := 4983230072969 + 3 ^ 40 * 3840865 * 2
def baseEnd_3840865 : Nat := 73044810149304456730507

theorem tailTrace_3840865 : CollatzResearch.WordTrace tailWord_3840865 prefixEnd_3840865 73044810149304456730507 := by
  unfold tailWord_3840865
  simp only [CollatzResearch.WordTrace]
  refine ⟨140087855230209547362868049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93391903486806364908578699 140087855230209547362868049)
  ·
    refine ⟨105065891422657160522151037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140087855230209547362868049 105065891422657160522151037)
    ·
      refine ⟨39399709283496435195806639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105065891422657160522151037 39399709283496435195806639)
      ·
        refine ⟨59099563925244652793709959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39399709283496435195806639 59099563925244652793709959)
        ·
          refine ⟨88649345887866979190564939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59099563925244652793709959 88649345887866979190564939)
          ·
            refine ⟨132974018831800468785847409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88649345887866979190564939 132974018831800468785847409)
            ·
              refine ⟨99730514123850351589385557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132974018831800468785847409 99730514123850351589385557)
              ·
                refine ⟨73044810149304456730507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 99730514123850351589385557 73044810149304456730507)
                ·
                  rfl

theorem cell23_3840865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 12].length) (baseStart_3840865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840865 prefixEnd_3840865 := by exact prefixLift 3840865
  have htrace : WordTrace (prefixWord ++ tailWord_3840865) baseStart_3840865 baseEnd_3840865 := by
    simpa [prefixWord, tailWord_3840865, baseEnd_3840865] using wordTrace_append hprefix tailTrace_3840865
  have hstable : (prefixWord ++ tailWord_3840865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840865).length < 2 ^ (prefixWord ++ tailWord_3840865).sum := by decide
  have hdescent : baseEnd_3840865 < baseStart_3840865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840869 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_3840869 : Nat := 118140960795 + 3840869 * 2 ^ 59
def prefixEnd_3840869 : Nat := 4983230072969 + 3 ^ 40 * 3840869 * 2
def baseEnd_3840869 : Nat := 657403975984612772024557

theorem tailTrace_3840869 : CollatzResearch.WordTrace tailWord_3840869 prefixEnd_3840869 657403975984612772024557 := by
  unfold tailWord_3840869
  simp only [CollatzResearch.WordTrace]
  refine ⟨140088001122195056046013661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93392000748130037364009107 140088001122195056046013661)
  ·
    refine ⟨52533000420823146017255123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140088001122195056046013661 52533000420823146017255123)
    ·
      refine ⟨78799500631234719025882685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52533000420823146017255123 78799500631234719025882685)
      ·
        refine ⟨29549812736713019634706007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78799500631234719025882685 29549812736713019634706007)
        ·
          refine ⟨44324719105069529452059011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29549812736713019634706007 44324719105069529452059011)
          ·
            refine ⟨66487078657604294178088517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44324719105069529452059011 66487078657604294178088517)
            ·
              refine ⟨12466327248300805158391597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66487078657604294178088517 12466327248300805158391597)
              ·
                refine ⟨4674872718112801934396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12466327248300805158391597 4674872718112801934396849)
                ·
                  refine ⟨3506154538584601450797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4674872718112801934396849 3506154538584601450797637)
                  ·
                    refine ⟨657403975984612772024557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3506154538584601450797637 657403975984612772024557)
                    ·
                      rfl

theorem cell23_3840869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_3840869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840869 prefixEnd_3840869 := by exact prefixLift 3840869
  have htrace : WordTrace (prefixWord ++ tailWord_3840869) baseStart_3840869 baseEnd_3840869 := by
    simpa [prefixWord, tailWord_3840869, baseEnd_3840869] using wordTrace_append hprefix tailTrace_3840869
  have hstable : (prefixWord ++ tailWord_3840869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840869).length < 2 ^ (prefixWord ++ tailWord_3840869).sum := by decide
  have hdescent : baseEnd_3840869 < baseStart_3840869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840876 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_3840876 : Nat := 118140960795 + 3840876 * 2 ^ 59
def prefixEnd_3840876 : Nat := 4983230072969 + 3 ^ 40 * 3840876 * 2
def baseEnd_3840876 : Nat := 1972215522318419788686139

theorem tailTrace_3840876 : CollatzResearch.WordTrace tailWord_3840876 prefixEnd_3840876 1972215522318419788686139 := by
  unfold tailWord_3840876
  simp only [CollatzResearch.WordTrace]
  refine ⟨70044128216584848120759241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93392170955446464161012321 70044128216584848120759241)
  ·
    refine ⟨52533096162438636090569431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70044128216584848120759241 52533096162438636090569431)
    ·
      refine ⟨78799644243657954135854147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52533096162438636090569431 78799644243657954135854147)
      ·
        refine ⟨118199466365486931203781221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78799644243657954135854147 118199466365486931203781221)
        ·
          refine ⟨22162399943528799600708979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118199466365486931203781221 22162399943528799600708979)
          ·
            refine ⟨33243599915293199401063469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22162399943528799600708979 33243599915293199401063469)
            ·
              refine ⟨12466349968234949775398801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33243599915293199401063469 12466349968234949775398801)
              ·
                refine ⟨9349762476176212331549101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12466349968234949775398801 9349762476176212331549101)
                ·
                  refine ⟨3506160928566079624330913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9349762476176212331549101 3506160928566079624330913)
                  ·
                    refine ⟨2629620696424559718248185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506160928566079624330913 2629620696424559718248185)
                    ·
                      refine ⟨1972215522318419788686139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629620696424559718248185 1972215522318419788686139)
                      ·
                        rfl

theorem cell23_3840876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_3840876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840876 prefixEnd_3840876 := by exact prefixLift 3840876
  have htrace : WordTrace (prefixWord ++ tailWord_3840876) baseStart_3840876 baseEnd_3840876 := by
    simpa [prefixWord, tailWord_3840876, baseEnd_3840876] using wordTrace_append hprefix tailTrace_3840876
  have hstable : (prefixWord ++ tailWord_3840876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840876).length < 2 ^ (prefixWord ++ tailWord_3840876).sum := by decide
  have hdescent : baseEnd_3840876 < baseStart_3840876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840893 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_3840893 : Nat := 118140960795 + 3840893 * 2 ^ 59
def prefixEnd_3840893 : Nat := 4983230072969 + 3 ^ 40 * 3840893 * 2
def baseEnd_3840893 : Nat := 1972224251489546222173561

theorem tailTrace_3840893 : CollatzResearch.WordTrace tailWord_3840893 prefixEnd_3840893 1972224251489546222173561 := by
  unfold tailWord_3840893
  simp only [CollatzResearch.WordTrace]
  refine ⟨140088876474108108144887333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93392584316072072096591555 140088876474108108144887333)
  ·
    refine ⟨26266664338895270277166375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140088876474108108144887333 26266664338895270277166375)
    ·
      refine ⟨39399996508342905415749563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26266664338895270277166375 39399996508342905415749563)
      ·
        refine ⟨59099994762514358123624345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39399996508342905415749563 59099994762514358123624345)
        ·
          refine ⟨44324996071885768592718259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59099994762514358123624345 44324996071885768592718259)
          ·
            refine ⟨66487494107828652889077389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44324996071885768592718259 66487494107828652889077389)
            ·
              refine ⟨24932810290435744833404021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66487494107828652889077389 24932810290435744833404021)
              ·
                refine ⟨2337450964728351078131627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24932810290435744833404021 2337450964728351078131627)
                ·
                  refine ⟨3506176447092526617197441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337450964728351078131627 3506176447092526617197441)
                  ·
                    refine ⟨2629632335319394962898081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506176447092526617197441 2629632335319394962898081)
                    ·
                      refine ⟨1972224251489546222173561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629632335319394962898081 1972224251489546222173561)
                      ·
                        rfl

theorem cell23_3840893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_3840893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840893 prefixEnd_3840893 := by exact prefixLift 3840893
  have htrace : WordTrace (prefixWord ++ tailWord_3840893) baseStart_3840893 baseEnd_3840893 := by
    simpa [prefixWord, tailWord_3840893, baseEnd_3840893] using wordTrace_append hprefix tailTrace_3840893
  have hstable : (prefixWord ++ tailWord_3840893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840893).length < 2 ^ (prefixWord ++ tailWord_3840893).sum := by decide
  have hdescent : baseEnd_3840893 < baseStart_3840893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840950 : List Nat := [5, 1, 4, 1, 2, 1, 9]
def baseStart_3840950 : Nat := 118140960795 + 3840950 * 2 ^ 59
def prefixEnd_3840950 : Nat := 4983230072969 + 3 ^ 40 * 3840950 * 2
def baseEnd_3840950 : Nat := 24348808887492006162479

theorem tailTrace_3840950 : CollatzResearch.WordTrace tailWord_3840950 prefixEnd_3840950 24348808887492006162479 := by
  unfold tailWord_3840950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755684714681350429982019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93393970289934404586474869 8755684714681350429982019)
  ·
    refine ⟨13133527072022025644973029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755684714681350429982019 13133527072022025644973029)
    ·
      refine ⟨2462536326004129808432443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13133527072022025644973029 2462536326004129808432443)
      ·
        refine ⟨3693804489006194712648665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462536326004129808432443 3693804489006194712648665)
        ·
          refine ⟨2770353366754646034486499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693804489006194712648665 2770353366754646034486499)
          ·
            refine ⟨4155530050131969051729749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770353366754646034486499 4155530050131969051729749)
            ·
              refine ⟨24348808887492006162479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4155530050131969051729749 24348808887492006162479)
              ·
                rfl

theorem cell23_3840950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 9].length) (baseStart_3840950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840950 prefixEnd_3840950 := by exact prefixLift 3840950
  have htrace : WordTrace (prefixWord ++ tailWord_3840950) baseStart_3840950 baseEnd_3840950 := by
    simpa [prefixWord, tailWord_3840950, baseEnd_3840950] using wordTrace_append hprefix tailTrace_3840950
  have hstable : (prefixWord ++ tailWord_3840950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840950).length < 2 ^ (prefixWord ++ tailWord_3840950).sum := by decide
  have hdescent : baseEnd_3840950 < baseStart_3840950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3840952 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_3840952 : Nat := 118140960795 + 3840952 * 2 ^ 59
def prefixEnd_3840952 : Nat := 4983230072969 + 3 ^ 40 * 3840952 * 2
def baseEnd_3840952 : Nat := 1972254546848161491335789

theorem tailTrace_3840952 : CollatzResearch.WordTrace tailWord_3840952 prefixEnd_3840952 1972254546848161491335789 := by
  unfold tailWord_3840952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70045514190447180610642555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93394018920596240814190073 70045514190447180610642555)
  ·
    refine ⟨105068271285670770915963833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70045514190447180610642555 105068271285670770915963833)
    ·
      refine ⟨78801203464253078186972875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105068271285670770915963833 78801203464253078186972875)
      ·
        refine ⟨118201805196379617280459313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78801203464253078186972875 118201805196379617280459313)
        ·
          refine ⟨88651353897284712960344485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118201805196379617280459313 88651353897284712960344485)
          ·
            refine ⟨16622128855740883680064591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88651353897284712960344485 16622128855740883680064591)
            ·
              refine ⟨24933193283611325520096887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16622128855740883680064591 24933193283611325520096887)
              ·
                refine ⟨37399789925416988280145331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24933193283611325520096887 37399789925416988280145331)
                ·
                  refine ⟨56099684888125482420217997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37399789925416988280145331 56099684888125482420217997)
                  ·
                    refine ⟨21037381833047055907581749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56099684888125482420217997 21037381833047055907581749)
                    ·
                      refine ⟨1972254546848161491335789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21037381833047055907581749 1972254546848161491335789)
                      ·
                        rfl

theorem cell23_3840952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_3840952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3840952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3840952 prefixEnd_3840952 := by exact prefixLift 3840952
  have htrace : WordTrace (prefixWord ++ tailWord_3840952) baseStart_3840952 baseEnd_3840952 := by
    simpa [prefixWord, tailWord_3840952, baseEnd_3840952] using wordTrace_append hprefix tailTrace_3840952
  have hstable : (prefixWord ++ tailWord_3840952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3840952).length < 2 ^ (prefixWord ++ tailWord_3840952).sum := by decide
  have hdescent : baseEnd_3840952 < baseStart_3840952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3840952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841049 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_3841049 : Nat := 118140960795 + 3841049 * 2 ^ 59
def prefixEnd_3841049 : Nat := 4983230072969 + 3 ^ 40 * 3841049 * 2
def baseEnd_3841049 : Nat := 657434784823882537274281

theorem tailTrace_3841049 : CollatzResearch.WordTrace tailWord_3841049 prefixEnd_3841049 657434784823882537274281 := by
  unfold tailWord_3841049
  simp only [CollatzResearch.WordTrace]
  refine ⟨140094566261542946787566201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93396377507695297858377467 140094566261542946787566201)
  ·
    refine ⟨105070924696157210090674651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140094566261542946787566201 105070924696157210090674651)
    ·
      refine ⟨157606387044235815136011977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105070924696157210090674651 157606387044235815136011977)
      ·
        refine ⟨118204790283176861352008983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157606387044235815136011977 118204790283176861352008983)
        ·
          refine ⟨177307185424765292028013475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118204790283176861352008983 177307185424765292028013475)
          ·
            refine ⟨265960778137147938042020213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177307185424765292028013475 265960778137147938042020213)
            ·
              refine ⟨24933822950357619191439395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265960778137147938042020213 24933822950357619191439395)
              ·
                refine ⟨37400734425536428787159093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24933822950357619191439395 37400734425536428787159093)
                ·
                  refine ⟨3506318852394040198796165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37400734425536428787159093 3506318852394040198796165)
                  ·
                    refine ⟨657434784823882537274281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3506318852394040198796165 657434784823882537274281)
                    ·
                      rfl

theorem cell23_3841049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_3841049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841049 prefixEnd_3841049 := by exact prefixLift 3841049
  have htrace : WordTrace (prefixWord ++ tailWord_3841049) baseStart_3841049 baseEnd_3841049 := by
    simpa [prefixWord, tailWord_3841049, baseEnd_3841049] using wordTrace_append hprefix tailTrace_3841049
  have hstable : (prefixWord ++ tailWord_3841049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841049).length < 2 ^ (prefixWord ++ tailWord_3841049).sum := by decide
  have hdescent : baseEnd_3841049 < baseStart_3841049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841053 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3841053 : Nat := 118140960795 + 3841053 * 2 ^ 59
def prefixEnd_3841053 : Nat := 4983230072969 + 3 ^ 40 * 3841053 * 2
def baseEnd_3841053 : Nat := 657435469464755198724275

theorem tailTrace_3841053 : CollatzResearch.WordTrace tailWord_3841053 prefixEnd_3841053 657435469464755198724275 := by
  unfold tailWord_3841053
  simp only [CollatzResearch.WordTrace]
  refine ⟨140094712153528455470711813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93396474769018970313807875 140094712153528455470711813)
  ·
    refine ⟨26267758528786585400758465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140094712153528455470711813 26267758528786585400758465)
    ·
      refine ⟨19700818896589939050568849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26267758528786585400758465 19700818896589939050568849)
      ·
        refine ⟨14775614172442454287926637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19700818896589939050568849 14775614172442454287926637)
        ·
          refine ⟨5540855314665920357972489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14775614172442454287926637 5540855314665920357972489)
          ·
            refine ⟨4155641485999440268479367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540855314665920357972489 4155641485999440268479367)
            ·
              refine ⟨6233462228999160402719051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155641485999440268479367 6233462228999160402719051)
              ·
                refine ⟨9350193343498740604078577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233462228999160402719051 9350193343498740604078577)
                ·
                  refine ⟨7012645007624055453058933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350193343498740604078577 7012645007624055453058933)
                  ·
                    refine ⟨657435469464755198724275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7012645007624055453058933 657435469464755198724275)
                    ·
                      rfl

theorem cell23_3841053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3841053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841053 prefixEnd_3841053 := by exact prefixLift 3841053
  have htrace : WordTrace (prefixWord ++ tailWord_3841053) baseStart_3841053 baseEnd_3841053 := by
    simpa [prefixWord, tailWord_3841053, baseEnd_3841053] using wordTrace_append hprefix tailTrace_3841053
  have hstable : (prefixWord ++ tailWord_3841053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841053).length < 2 ^ (prefixWord ++ tailWord_3841053).sum := by decide
  have hdescent : baseEnd_3841053 < baseStart_3841053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841096 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 6]
def baseStart_3841096 : Nat := 118140960795 + 3841096 * 2 ^ 59
def prefixEnd_3841096 : Nat := 4983230072969 + 3 ^ 40 * 3841096 * 2
def baseEnd_3841096 : Nat := 219147609784712103103903

theorem tailTrace_3841096 : CollatzResearch.WordTrace tailWord_3841096 prefixEnd_3841096 219147609784712103103903 := by
  unfold tailWord_3841096
  simp only [CollatzResearch.WordTrace]
  refine ⟨70048140246186336907263571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93397520328248449209684761 70048140246186336907263571)
  ·
    refine ⟨105072210369279505360895357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70048140246186336907263571 105072210369279505360895357)
    ·
      refine ⟨39402078888479814510335759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105072210369279505360895357 39402078888479814510335759)
      ·
        refine ⟨59103118332719721765503639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39402078888479814510335759 59103118332719721765503639)
        ·
          refine ⟨88654677499079582648255459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59103118332719721765503639 88654677499079582648255459)
          ·
            refine ⟨132982016248619373972383189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88654677499079582648255459 132982016248619373972383189)
            ·
              refine ⟨3116766005827016577477731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132982016248619373972383189 3116766005827016577477731)
              ·
                refine ⟨4675149008740524866216597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116766005827016577477731 4675149008740524866216597)
                ·
                  refine ⟨219147609784712103103903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4675149008740524866216597 219147609784712103103903)
                  ·
                    rfl

theorem cell23_3841096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 6].length) (baseStart_3841096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841096 prefixEnd_3841096 := by exact prefixLift 3841096
  have htrace : WordTrace (prefixWord ++ tailWord_3841096) baseStart_3841096 baseEnd_3841096 := by
    simpa [prefixWord, tailWord_3841096, baseEnd_3841096] using wordTrace_append hprefix tailTrace_3841096
  have hstable : (prefixWord ++ tailWord_3841096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841096).length < 2 ^ (prefixWord ++ tailWord_3841096).sum := by decide
  have hdescent : baseEnd_3841096 < baseStart_3841096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841133 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_3841133 : Nat := 118140960795 + 3841133 * 2 ^ 59
def prefixEnd_3841133 : Nat := 4983230072969 + 3 ^ 40 * 3841133 * 2
def baseEnd_3841133 : Nat := 1972347486846625283172457

theorem tailTrace_3841133 : CollatzResearch.WordTrace tailWord_3841133 prefixEnd_3841133 1972347486846625283172457 := by
  unfold tailWord_3841133
  simp only [CollatzResearch.WordTrace]
  refine ⟨140097629993238629133624053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93398419995492419422416035 140097629993238629133624053)
  ·
    refine ⟨13134152811866121481277255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140097629993238629133624053 13134152811866121481277255)
    ·
      refine ⟨19701229217799182221915883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134152811866121481277255 19701229217799182221915883)
      ·
        refine ⟨29551843826698773332873825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19701229217799182221915883 29551843826698773332873825)
        ·
          refine ⟨22163882870024079999655369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29551843826698773332873825 22163882870024079999655369)
          ·
            refine ⟨16622912152518059999741527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22163882870024079999655369 16622912152518059999741527)
            ·
              refine ⟨24934368228777089999612291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16622912152518059999741527 24934368228777089999612291)
              ·
                refine ⟨37401552343165634999418437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24934368228777089999612291 37401552343165634999418437)
                ·
                  refine ⟨7012791064343556562390957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37401552343165634999418437 7012791064343556562390957)
                  ·
                    refine ⟨2629796649128833710896609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7012791064343556562390957 2629796649128833710896609)
                    ·
                      refine ⟨1972347486846625283172457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629796649128833710896609 1972347486846625283172457)
                      ·
                        rfl

theorem cell23_3841133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_3841133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841133 prefixEnd_3841133 := by exact prefixLift 3841133
  have htrace : WordTrace (prefixWord ++ tailWord_3841133) baseStart_3841133 baseEnd_3841133 := by
    simpa [prefixWord, tailWord_3841133, baseEnd_3841133] using wordTrace_append hprefix tailTrace_3841133
  have hstable : (prefixWord ++ tailWord_3841133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841133).length < 2 ^ (prefixWord ++ tailWord_3841133).sum := by decide
  have hdescent : baseEnd_3841133 < baseStart_3841133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841160 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_3841160 : Nat := 118140960795 + 3841160 * 2 ^ 59
def prefixEnd_3841160 : Nat := 4983230072969 + 3 ^ 40 * 3841160 * 2
def baseEnd_3841160 : Nat := 657453783608098892511611

theorem tailTrace_3841160 : CollatzResearch.WordTrace tailWord_3841160 prefixEnd_3841160 657453783608098892511611 := by
  unfold tailWord_3841160
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049307382070406372428467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93399076509427208496571289 70049307382070406372428467)
  ·
    refine ⟨105073961073105609558642701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70049307382070406372428467 105073961073105609558642701)
    ·
      refine ⟨39402735402414603584491013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105073961073105609558642701 39402735402414603584491013)
      ·
        refine ⟨7388012887952738172092065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39402735402414603584491013 7388012887952738172092065)
        ·
          refine ⟨5541009665964553629069049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7388012887952738172092065 5541009665964553629069049)
          ·
            refine ⟨4155757249473415221801787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5541009665964553629069049 4155757249473415221801787)
            ·
              refine ⟨6233635874210122832702681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155757249473415221801787 6233635874210122832702681)
              ·
                refine ⟨4675226905657592124527011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233635874210122832702681 4675226905657592124527011)
                ·
                  refine ⟨7012840358486388186790517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675226905657592124527011 7012840358486388186790517)
                  ·
                    refine ⟨657453783608098892511611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7012840358486388186790517 657453783608098892511611)
                    ·
                      rfl

theorem cell23_3841160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_3841160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841160 prefixEnd_3841160 := by exact prefixLift 3841160
  have htrace : WordTrace (prefixWord ++ tailWord_3841160) baseStart_3841160 baseEnd_3841160 := by
    simpa [prefixWord, tailWord_3841160, baseEnd_3841160] using wordTrace_append hprefix tailTrace_3841160
  have hstable : (prefixWord ++ tailWord_3841160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841160).length < 2 ^ (prefixWord ++ tailWord_3841160).sum := by decide
  have hdescent : baseEnd_3841160 < baseStart_3841160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841163 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 3, 2, 2]
def baseStart_3841163 : Nat := 118140960795 + 3841163 * 2 ^ 59
def prefixEnd_3841163 : Nat := 4983230072969 + 3 ^ 40 * 3841163 * 2
def baseEnd_3841163 : Nat := 1972362891266260165797319

theorem tailTrace_3841163 : CollatzResearch.WordTrace tailWord_3841163 prefixEnd_3841163 1972362891266260165797319 := by
  unfold tailWord_3841163
  simp only [CollatzResearch.WordTrace]
  refine ⟨140098724183129944257216143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93399149455419962838144095 140098724183129944257216143)
  ·
    refine ⟨210148086274694916385824215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140098724183129944257216143 210148086274694916385824215)
    ·
      refine ⟨315222129412042374578736323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210148086274694916385824215 315222129412042374578736323)
      ·
        refine ⟨472833194118063561868104485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315222129412042374578736323 472833194118063561868104485)
        ·
          refine ⟨88656223897136917850269591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472833194118063561868104485 88656223897136917850269591)
          ·
            refine ⟨132984335845705376775404387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88656223897136917850269591 132984335845705376775404387)
            ·
              refine ⟨199476503768558065163106581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132984335845705376775404387 199476503768558065163106581)
              ·
                refine ⟨9350461114151159304520621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199476503768558065163106581 9350461114151159304520621)
                ·
                  refine ⟨3506422917806684739195233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9350461114151159304520621 3506422917806684739195233)
                  ·
                    refine ⟨2629817188355013554396425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506422917806684739195233 2629817188355013554396425)
                    ·
                      refine ⟨1972362891266260165797319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629817188355013554396425 1972362891266260165797319)
                      ·
                        rfl

theorem cell23_3841163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2, 2].length) (baseStart_3841163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841163 prefixEnd_3841163 := by exact prefixLift 3841163
  have htrace : WordTrace (prefixWord ++ tailWord_3841163) baseStart_3841163 baseEnd_3841163 := by
    simpa [prefixWord, tailWord_3841163, baseEnd_3841163] using wordTrace_append hprefix tailTrace_3841163
  have hstable : (prefixWord ++ tailWord_3841163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841163).length < 2 ^ (prefixWord ++ tailWord_3841163).sum := by decide
  have hdescent : baseEnd_3841163 < baseStart_3841163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841176 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3841176 : Nat := 118140960795 + 3841176 * 2 ^ 59
def prefixEnd_3841176 : Nat := 4983230072969 + 3 ^ 40 * 3841176 * 2
def baseEnd_3841176 : Nat := 1972369566514768614934759

theorem tailTrace_3841176 : CollatzResearch.WordTrace tailWord_3841176 prefixEnd_3841176 1972369566514768614934759 := by
  unfold tailWord_3841176
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049599166041423738719691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93399465554721898318292921 70049599166041423738719691)
  ·
    refine ⟨105074398749062135608079537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70049599166041423738719691 105074398749062135608079537)
    ·
      refine ⟨78805799061796601706059653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105074398749062135608079537 78805799061796601706059653)
      ·
        refine ⟨14776087324086862819886185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78805799061796601706059653 14776087324086862819886185)
        ·
          refine ⟨11082065493065147114914639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14776087324086862819886185 11082065493065147114914639)
          ·
            refine ⟨16623098239597720672371959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11082065493065147114914639 16623098239597720672371959)
            ·
              refine ⟨24934647359396581008557939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623098239597720672371959 24934647359396581008557939)
              ·
                refine ⟨37401971039094871512836909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24934647359396581008557939 37401971039094871512836909)
                ·
                  refine ⟨14025739139660576817313841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37401971039094871512836909 14025739139660576817313841)
                  ·
                    refine ⟨10519304354745432612985381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14025739139660576817313841 10519304354745432612985381)
                    ·
                      refine ⟨1972369566514768614934759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10519304354745432612985381 1972369566514768614934759)
                      ·
                        rfl

theorem cell23_3841176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3841176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841176 prefixEnd_3841176 := by exact prefixLift 3841176
  have htrace : WordTrace (prefixWord ++ tailWord_3841176) baseStart_3841176 baseEnd_3841176 := by
    simpa [prefixWord, tailWord_3841176, baseEnd_3841176] using wordTrace_append hprefix tailTrace_3841176
  have hstable : (prefixWord ++ tailWord_3841176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841176).length < 2 ^ (prefixWord ++ tailWord_3841176).sum := by decide
  have hdescent : baseEnd_3841176 < baseStart_3841176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841180 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3841180 : Nat := 118140960795 + 3841180 * 2 ^ 59
def prefixEnd_3841180 : Nat := 4983230072969 + 3 ^ 40 * 3841180 * 2
def baseEnd_3841180 : Nat := 1972371620437386599284741

theorem tailTrace_3841180 : CollatzResearch.WordTrace tailWord_3841180 prefixEnd_3841180 1972371620437386599284741 := by
  unfold tailWord_3841180
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049672112034178080292497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93399562816045570773723329 70049672112034178080292497)
  ·
    refine ⟨52537254084025633560219373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70049672112034178080292497 52537254084025633560219373)
    ·
      refine ⟨19701470281509612585082265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52537254084025633560219373 19701470281509612585082265)
      ·
        refine ⟨14776102711132209438811699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19701470281509612585082265 14776102711132209438811699)
        ·
          refine ⟨22164154066698314158217549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776102711132209438811699 22164154066698314158217549)
          ·
            refine ⟨8311557775011867809331581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22164154066698314158217549 8311557775011867809331581)
            ·
              refine ⟨3116834165629450428499343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8311557775011867809331581 3116834165629450428499343)
              ·
                refine ⟨4675251248444175642749015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116834165629450428499343 4675251248444175642749015)
                ·
                  refine ⟨7012876872666263464123523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675251248444175642749015 7012876872666263464123523)
                  ·
                    refine ⟨10519315308999395196185285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012876872666263464123523 10519315308999395196185285)
                    ·
                      refine ⟨1972371620437386599284741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10519315308999395196185285 1972371620437386599284741)
                      ·
                        rfl

theorem cell23_3841180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3841180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841180 prefixEnd_3841180 := by exact prefixLift 3841180
  have htrace : WordTrace (prefixWord ++ tailWord_3841180) baseStart_3841180 baseEnd_3841180 := by
    simpa [prefixWord, tailWord_3841180, baseEnd_3841180] using wordTrace_append hprefix tailTrace_3841180
  have hstable : (prefixWord ++ tailWord_3841180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841180).length < 2 ^ (prefixWord ++ tailWord_3841180).sum := by decide
  have hdescent : baseEnd_3841180 < baseStart_3841180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841186 : List Nat := [3, 3, 1, 3, 2, 11]
def baseStart_3841186 : Nat := 118140960795 + 3841186 * 2 ^ 59
def prefixEnd_3841186 : Nat := 4983230072969 + 3 ^ 40 * 3841186 * 2
def baseEnd_3841186 : Nat := 8116768318194706073291

theorem tailTrace_3841186 : CollatzResearch.WordTrace tailWord_3841186 prefixEnd_3841186 8116768318194706073291 := by
  unfold tailWord_3841186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35024890765511654796325853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93399708708031079456868941 35024890765511654796325853)
  ·
    refine ⟨13134334037066870548622195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35024890765511654796325853 13134334037066870548622195)
    ·
      refine ⟨19701501055600305822933293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134334037066870548622195 19701501055600305822933293)
      ·
        refine ⟨7388062895850114683599985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19701501055600305822933293 7388062895850114683599985)
        ·
          refine ⟨5541047171887586012699989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7388062895850114683599985 5541047171887586012699989)
          ·
            refine ⟨8116768318194706073291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5541047171887586012699989 8116768318194706073291)
            ·
              rfl

theorem cell23_3841186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 11].length) (baseStart_3841186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841186 prefixEnd_3841186 := by exact prefixLift 3841186
  have htrace : WordTrace (prefixWord ++ tailWord_3841186) baseStart_3841186 baseEnd_3841186 := by
    simpa [prefixWord, tailWord_3841186, baseEnd_3841186] using wordTrace_append hprefix tailTrace_3841186
  have hstable : (prefixWord ++ tailWord_3841186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841186).length < 2 ^ (prefixWord ++ tailWord_3841186).sum := by decide
  have hdescent : baseEnd_3841186 < baseStart_3841186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841199 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 7]
def baseStart_3841199 : Nat := 118140960795 + 3841199 * 2 ^ 59
def prefixEnd_3841199 : Nat := 4983230072969 + 3 ^ 40 * 3841199 * 2
def baseEnd_3841199 : Nat := 657460458856607341649051

theorem tailTrace_3841199 : CollatzResearch.WordTrace tailWord_3841199 prefixEnd_3841199 657460458856607341649051 := by
  unfold tailWord_3841199
  simp only [CollatzResearch.WordTrace]
  refine ⟨140100037210999522405526651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93400024807333014937017767 140100037210999522405526651)
  ·
    refine ⟨210150055816499283608289977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140100037210999522405526651 210150055816499283608289977)
    ·
      refine ⟨157612541862374462706217483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210150055816499283608289977 157612541862374462706217483)
      ·
        refine ⟨236418812793561694059326225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157612541862374462706217483 236418812793561694059326225)
        ·
          refine ⟨177314109595171270544494669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236418812793561694059326225 177314109595171270544494669)
          ·
            refine ⟨66492791098189226454185501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177314109595171270544494669 66492791098189226454185501)
            ·
              refine ⟨24934796661820959920319563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66492791098189226454185501 24934796661820959920319563)
              ·
                refine ⟨37402194992731439880479345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24934796661820959920319563 37402194992731439880479345)
                ·
                  refine ⟨28051646244548579910359509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37402194992731439880479345 28051646244548579910359509)
                  ·
                    refine ⟨657460458856607341649051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28051646244548579910359509 657460458856607341649051)
                    ·
                      rfl

theorem cell23_3841199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_3841199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841199 prefixEnd_3841199 := by exact prefixLift 3841199
  have htrace : WordTrace (prefixWord ++ tailWord_3841199) baseStart_3841199 baseEnd_3841199 := by
    simpa [prefixWord, tailWord_3841199, baseEnd_3841199] using wordTrace_append hprefix tailTrace_3841199
  have hstable : (prefixWord ++ tailWord_3841199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841199).length < 2 ^ (prefixWord ++ tailWord_3841199).sum := by decide
  have hdescent : baseEnd_3841199 < baseStart_3841199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841313 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3841313 : Nat := 118140960795 + 3841313 * 2 ^ 59
def prefixEnd_3841313 : Nat := 4983230072969 + 3 ^ 40 * 3841313 * 2
def baseEnd_3841313 : Nat := 1972439913364434578921629

theorem tailTrace_3841313 : CollatzResearch.WordTrace tailWord_3841313 prefixEnd_3841313 1972439913364434578921629 := by
  unfold tailWord_3841313
  simp only [CollatzResearch.WordTrace]
  refine ⟨140104195132586519875176593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93402796755057679916784395 140104195132586519875176593)
  ·
    refine ⟨105078146349439889906382445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140104195132586519875176593 105078146349439889906382445)
    ·
      refine ⟨39404304881039958714893417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105078146349439889906382445 39404304881039958714893417)
      ·
        refine ⟨29553228660779969036170063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39404304881039958714893417 29553228660779969036170063)
        ·
          refine ⟨44329842991169953554255095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29553228660779969036170063 44329842991169953554255095)
          ·
            refine ⟨66494764486754930331382643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44329842991169953554255095 66494764486754930331382643)
            ·
              refine ⟨99742146730132395497073965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66494764486754930331382643 99742146730132395497073965)
              ·
                refine ⟨37403305023799648311402737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99742146730132395497073965 37403305023799648311402737)
                ·
                  refine ⟨28052478767849736233552053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37403305023799648311402737 28052478767849736233552053)
                  ·
                    refine ⟨2629919884485912771895505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28052478767849736233552053 2629919884485912771895505)
                    ·
                      refine ⟨1972439913364434578921629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629919884485912771895505 1972439913364434578921629)
                      ·
                        rfl

theorem cell23_3841313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3841313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841313 prefixEnd_3841313 := by exact prefixLift 3841313
  have htrace : WordTrace (prefixWord ++ tailWord_3841313) baseStart_3841313 baseEnd_3841313 := by
    simpa [prefixWord, tailWord_3841313, baseEnd_3841313] using wordTrace_append hprefix tailTrace_3841313
  have hstable : (prefixWord ++ tailWord_3841313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841313).length < 2 ^ (prefixWord ++ tailWord_3841313).sum := by decide
  have hdescent : baseEnd_3841313 < baseStart_3841313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841343 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_3841343 : Nat := 118140960795 + 3841343 * 2 ^ 59
def prefixEnd_3841343 : Nat := 4983230072969 + 3 ^ 40 * 3841343 * 2
def baseEnd_3841343 : Nat := 1972455317784069461546491

theorem tailTrace_3841343 : CollatzResearch.WordTrace tailWord_3841343 prefixEnd_3841343 1972455317784069461546491 := by
  unfold tailWord_3841343
  simp only [CollatzResearch.WordTrace]
  refine ⟨140105289322477834998768683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93403526214985223332512455 140105289322477834998768683)
  ·
    refine ⟨210157933983716752498153025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140105289322477834998768683 210157933983716752498153025)
    ·
      refine ⟨157618450487787564373614769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210157933983716752498153025 157618450487787564373614769)
      ·
        refine ⟨118213837865840673280211077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157618450487787564373614769 118213837865840673280211077)
        ·
          refine ⟨22165094599845126240039577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118213837865840673280211077 22165094599845126240039577)
          ·
            refine ⟨16623820949883844680029683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22165094599845126240039577 16623820949883844680029683)
            ·
              refine ⟨24935731424825767020044525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623820949883844680029683 24935731424825767020044525)
              ·
                refine ⟨9350899284309662632516697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24935731424825767020044525 9350899284309662632516697)
                ·
                  refine ⟨7013174463232246974387523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350899284309662632516697 7013174463232246974387523)
                  ·
                    refine ⟨10519761694848370461581285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7013174463232246974387523 10519761694848370461581285)
                    ·
                      refine ⟨1972455317784069461546491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10519761694848370461581285 1972455317784069461546491)
                      ·
                        rfl

theorem cell23_3841343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_3841343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841343 prefixEnd_3841343 := by exact prefixLift 3841343
  have htrace : WordTrace (prefixWord ++ tailWord_3841343) baseStart_3841343 baseEnd_3841343 := by
    simpa [prefixWord, tailWord_3841343, baseEnd_3841343] using wordTrace_append hprefix tailTrace_3841343
  have hstable : (prefixWord ++ tailWord_3841343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841343).length < 2 ^ (prefixWord ++ tailWord_3841343).sum := by decide
  have hdescent : baseEnd_3841343 < baseStart_3841343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841363 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3]
def baseStart_3841363 : Nat := 118140960795 + 3841363 * 2 ^ 59
def prefixEnd_3841363 : Nat := 4983230072969 + 3 ^ 40 * 3841363 * 2
def baseEnd_3841363 : Nat := 1972465587397159383296399

theorem tailTrace_3841363 : CollatzResearch.WordTrace tailWord_3841363 prefixEnd_3841363 1972465587397159383296399 := by
  unfold tailWord_3841363
  simp only [CollatzResearch.WordTrace]
  refine ⟨140106018782405378414496743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93404012521603585609664495 140106018782405378414496743)
  ·
    refine ⟨210159028173608067621745115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140106018782405378414496743 210159028173608067621745115)
    ·
      refine ⟨315238542260412101432617673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210159028173608067621745115 315238542260412101432617673)
      ·
        refine ⟨236428906695309076074463255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315238542260412101432617673 236428906695309076074463255)
        ·
          refine ⟨354643360042963614111694883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236428906695309076074463255 354643360042963614111694883)
          ·
            refine ⟨531965040064445421167542325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354643360042963614111694883 531965040064445421167542325)
            ·
              refine ⟨49871722506041758234457093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 531965040064445421167542325 49871722506041758234457093)
              ·
                refine ⟨9350947969882829668960705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49871722506041758234457093 9350947969882829668960705)
                ·
                  refine ⟨7013210977412122251720529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350947969882829668960705 7013210977412122251720529)
                  ·
                    refine ⟨5259908233059091688790397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013210977412122251720529 5259908233059091688790397)
                    ·
                      refine ⟨1972465587397159383296399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5259908233059091688790397 1972465587397159383296399)
                      ·
                        rfl

theorem cell23_3841363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_3841363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841363 prefixEnd_3841363 := by exact prefixLift 3841363
  have htrace : WordTrace (prefixWord ++ tailWord_3841363) baseStart_3841363 baseEnd_3841363 := by
    simpa [prefixWord, tailWord_3841363, baseEnd_3841363] using wordTrace_append hprefix tailTrace_3841363
  have hstable : (prefixWord ++ tailWord_3841363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841363).length < 2 ^ (prefixWord ++ tailWord_3841363).sum := by decide
  have hdescent : baseEnd_3841363 < baseStart_3841363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841417 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 6]
def baseStart_3841417 : Nat := 118140960795 + 3841417 * 2 ^ 59
def prefixEnd_3841417 : Nat := 4983230072969 + 3 ^ 40 * 3841417 * 2
def baseEnd_3841417 : Nat := 219165923928055796891239

theorem tailTrace_3841417 : CollatzResearch.WordTrace tailWord_3841417 prefixEnd_3841417 219165923928055796891239 := by
  unfold tailWord_3841417
  simp only [CollatzResearch.WordTrace]
  refine ⟨140107988324209745636962505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93405325549473163757975003 140107988324209745636962505)
  ·
    refine ⟨105080991243157309227721879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140107988324209745636962505 105080991243157309227721879)
    ·
      refine ⟨157621486864735963841582819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105080991243157309227721879 157621486864735963841582819)
      ·
        refine ⟨236432230297103945762374229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157621486864735963841582819 236432230297103945762374229)
        ·
          refine ⟨2770690198794186864402823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 236432230297103945762374229 2770690198794186864402823)
          ·
            refine ⟨4156035298191280296604235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770690198794186864402823 4156035298191280296604235)
            ·
              refine ⟨6234052947286920444906353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156035298191280296604235 6234052947286920444906353)
              ·
                refine ⟨4675539710465190333679765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234052947286920444906353 4675539710465190333679765)
                ·
                  refine ⟨219165923928055796891239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4675539710465190333679765 219165923928055796891239)
                  ·
                    rfl

theorem cell23_3841417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 6].length) (baseStart_3841417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841417 prefixEnd_3841417 := by exact prefixLift 3841417
  have htrace : WordTrace (prefixWord ++ tailWord_3841417) baseStart_3841417 baseEnd_3841417 := by
    simpa [prefixWord, tailWord_3841417, baseEnd_3841417] using wordTrace_append hprefix tailTrace_3841417
  have hstable : (prefixWord ++ tailWord_3841417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841417).length < 2 ^ (prefixWord ++ tailWord_3841417).sum := by decide
  have hdescent : baseEnd_3841417 < baseStart_3841417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841420 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_3841420 : Nat := 118140960795 + 3841420 * 2 ^ 59
def prefixEnd_3841420 : Nat := 4983230072969 + 3 ^ 40 * 3841420 * 2
def baseEnd_3841420 : Nat := 1972494855794465660283637

theorem tailTrace_3841420 : CollatzResearch.WordTrace tailWord_3841420 prefixEnd_3841420 1972494855794465660283637 := by
  unfold tailWord_3841420
  simp only [CollatzResearch.WordTrace]
  refine ⟨70054048871599438574660857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93405398495465918099547809 70054048871599438574660857)
  ·
    refine ⟨52540536653699578930995643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70054048871599438574660857 52540536653699578930995643)
    ·
      refine ⟨78810804980549368396493465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52540536653699578930995643 78810804980549368396493465)
      ·
        refine ⟨59108103735412026297370099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78810804980549368396493465 59108103735412026297370099)
        ·
          refine ⟨88662155603118039446055149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59108103735412026297370099 88662155603118039446055149)
          ·
            refine ⟨33248308351169264792270681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88662155603118039446055149 33248308351169264792270681)
            ·
              refine ⟨24936231263376948594203011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33248308351169264792270681 24936231263376948594203011)
              ·
                refine ⟨37404346895065422891304517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24936231263376948594203011 37404346895065422891304517)
                ·
                  refine ⟨7013315042824766792119597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37404346895065422891304517 7013315042824766792119597)
                  ·
                    refine ⟨2629993141059287547044849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7013315042824766792119597 2629993141059287547044849)
                    ·
                      refine ⟨1972494855794465660283637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2629993141059287547044849 1972494855794465660283637)
                      ·
                        rfl

theorem cell23_3841420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_3841420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841420 prefixEnd_3841420 := by exact prefixLift 3841420
  have htrace : WordTrace (prefixWord ++ tailWord_3841420) baseStart_3841420 baseEnd_3841420 := by
    simpa [prefixWord, tailWord_3841420, baseEnd_3841420] using wordTrace_append hprefix tailTrace_3841420
  have hstable : (prefixWord ++ tailWord_3841420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841420).length < 2 ^ (prefixWord ++ tailWord_3841420).sum := by decide
  have hdescent : baseEnd_3841420 < baseStart_3841420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841461 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_3841461 : Nat := 118140960795 + 3841461 * 2 ^ 59
def prefixEnd_3841461 : Nat := 4983230072969 + 3 ^ 40 * 3841461 * 2
def baseEnd_3841461 : Nat := 1972515908501299999870949

theorem tailTrace_3841461 : CollatzResearch.WordTrace tailWord_3841461 prefixEnd_3841461 1972515908501299999870949 := by
  unfold tailWord_3841461
  simp only [CollatzResearch.WordTrace]
  refine ⟨140109593136050341151564237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93406395424033560767709491 140109593136050341151564237)
  ·
    refine ⟨52541097426018877931836589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140109593136050341151564237 52541097426018877931836589)
    ·
      refine ⟨19702911534757079224438721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52541097426018877931836589 19702911534757079224438721)
      ·
        refine ⟨14777183651067809418329041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19702911534757079224438721 14777183651067809418329041)
        ·
          refine ⟨11082887738300857063746781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14777183651067809418329041 11082887738300857063746781)
          ·
            refine ⟨4156082901862821398905043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11082887738300857063746781 4156082901862821398905043)
            ·
              refine ⟨6234124352794232098357565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156082901862821398905043 6234124352794232098357565)
              ·
                refine ⟨2337796632297837036884087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6234124352794232098357565 2337796632297837036884087)
                ·
                  refine ⟨3506694948446755555326131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337796632297837036884087 3506694948446755555326131)
                  ·
                    refine ⟨5260042422670133332989197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3506694948446755555326131 5260042422670133332989197)
                    ·
                      refine ⟨1972515908501299999870949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260042422670133332989197 1972515908501299999870949)
                      ·
                        rfl

theorem cell23_3841461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_3841461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841461 prefixEnd_3841461 := by exact prefixLift 3841461
  have htrace : WordTrace (prefixWord ++ tailWord_3841461) baseStart_3841461 baseEnd_3841461 := by
    simpa [prefixWord, tailWord_3841461, baseEnd_3841461] using wordTrace_append hprefix tailTrace_3841461
  have hstable : (prefixWord ++ tailWord_3841461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841461).length < 2 ^ (prefixWord ++ tailWord_3841461).sum := by decide
  have hdescent : baseEnd_3841461 < baseStart_3841461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841463 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_3841463 : Nat := 118140960795 + 3841463 * 2 ^ 59
def prefixEnd_3841463 : Nat := 4983230072969 + 3 ^ 40 * 3841463 * 2
def baseEnd_3841463 : Nat := 1972516935462608992045939

theorem tailTrace_3841463 : CollatzResearch.WordTrace tailWord_3841463 prefixEnd_3841463 1972516935462608992045939 := by
  unfold tailWord_3841463
  simp only [CollatzResearch.WordTrace]
  refine ⟨140109666082043095493137043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93406444054695396995424695 140109666082043095493137043)
  ·
    refine ⟨210164499123064643239705565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140109666082043095493137043 210164499123064643239705565)
    ·
      refine ⟨78811687171149241214889587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210164499123064643239705565 78811687171149241214889587)
      ·
        refine ⟨118217530756723861822334381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78811687171149241214889587 118217530756723861822334381)
        ·
          refine ⟨44331574033771448183375393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118217530756723861822334381 44331574033771448183375393)
          ·
            refine ⟨33248680525328586137531545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44331574033771448183375393 33248680525328586137531545)
            ·
              refine ⟨24936510393996439603148659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33248680525328586137531545 24936510393996439603148659)
              ·
                refine ⟨37404765590994659404722989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24936510393996439603148659 37404765590994659404722989)
                ·
                  refine ⟨14026787096622997276771121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37404765590994659404722989 14026787096622997276771121)
                  ·
                    refine ⟨10520090322467247957578341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14026787096622997276771121 10520090322467247957578341)
                    ·
                      refine ⟨1972516935462608992045939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10520090322467247957578341 1972516935462608992045939)
                      ·
                        rfl

theorem cell23_3841463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_3841463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841463 prefixEnd_3841463 := by exact prefixLift 3841463
  have htrace : WordTrace (prefixWord ++ tailWord_3841463) baseStart_3841463 baseEnd_3841463 := by
    simpa [prefixWord, tailWord_3841463, baseEnd_3841463] using wordTrace_append hprefix tailTrace_3841463
  have hstable : (prefixWord ++ tailWord_3841463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841463).length < 2 ^ (prefixWord ++ tailWord_3841463).sum := by decide
  have hdescent : baseEnd_3841463 < baseStart_3841463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841470 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3841470 : Nat := 118140960795 + 3841470 * 2 ^ 59
def prefixEnd_3841470 : Nat := 4983230072969 + 3 ^ 40 * 3841470 * 2
def baseEnd_3841470 : Nat := 1972520529827190464658407

theorem tailTrace_3841470 : CollatzResearch.WordTrace tailWord_3841470 prefixEnd_3841470 1972520529827190464658407 := by
  unfold tailWord_3841470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513740174127216961080233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93406614262011823792427909 17513740174127216961080233)
  ·
    refine ⟨13135305130595412720810175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17513740174127216961080233 13135305130595412720810175)
    ·
      refine ⟨19702957695893119081215263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13135305130595412720810175 19702957695893119081215263)
      ·
        refine ⟨29554436543839678621822895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19702957695893119081215263 29554436543839678621822895)
        ·
          refine ⟨44331654815759517932734343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29554436543839678621822895 44331654815759517932734343)
          ·
            refine ⟨66497482223639276899101515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44331654815759517932734343 66497482223639276899101515)
            ·
              refine ⟨99746223335458915348652273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66497482223639276899101515 99746223335458915348652273)
              ·
                refine ⟨74809667501594186511489205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99746223335458915348652273 74809667501594186511489205)
                ·
                  refine ⟨7013406328274454985452113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74809667501594186511489205 7013406328274454985452113)
                  ·
                    refine ⟨5260054746205841239089085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013406328274454985452113 5260054746205841239089085)
                    ·
                      refine ⟨1972520529827190464658407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260054746205841239089085 1972520529827190464658407)
                      ·
                        rfl

theorem cell23_3841470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3841470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841470 prefixEnd_3841470 := by exact prefixLift 3841470
  have htrace : WordTrace (prefixWord ++ tailWord_3841470) baseStart_3841470 baseEnd_3841470 := by
    simpa [prefixWord, tailWord_3841470, baseEnd_3841470] using wordTrace_append hprefix tailTrace_3841470
  have hstable : (prefixWord ++ tailWord_3841470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841470).length < 2 ^ (prefixWord ++ tailWord_3841470).sum := by decide
  have hdescent : baseEnd_3841470 < baseStart_3841470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841484 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_3841484 : Nat := 118140960795 + 3841484 * 2 ^ 59
def prefixEnd_3841484 : Nat := 4983230072969 + 3 ^ 40 * 3841484 * 2
def baseEnd_3841484 : Nat := 1972527718556353409883343

theorem tailTrace_3841484 : CollatzResearch.WordTrace tailWord_3841484 prefixEnd_3841484 1972527718556353409883343 := by
  unfold tailWord_3841484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70055216007483508039825753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93406954676644677386434337 70055216007483508039825753)
  ·
    refine ⟨52541412005612631029869315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70055216007483508039825753 52541412005612631029869315)
    ·
      refine ⟨78812118008418946544803973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52541412005612631029869315 78812118008418946544803973)
      ·
        refine ⟨14777272126578552477150745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78812118008418946544803973 14777272126578552477150745)
        ·
          refine ⟨11082954094933914357863059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14777272126578552477150745 11082954094933914357863059)
          ·
            refine ⟨16624431142400871536794589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11082954094933914357863059 16624431142400871536794589)
            ·
              refine ⟨6234161678400326826297971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16624431142400871536794589 6234161678400326826297971)
              ·
                refine ⟨9351242517600490239446957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234161678400326826297971 9351242517600490239446957)
                ·
                  refine ⟨3506715944100183839792609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9351242517600490239446957 3506715944100183839792609)
                  ·
                    refine ⟨2630036958075137879844457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506715944100183839792609 2630036958075137879844457)
                    ·
                      refine ⟨1972527718556353409883343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630036958075137879844457 1972527718556353409883343)
                      ·
                        rfl

theorem cell23_3841484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_3841484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841484 prefixEnd_3841484 := by exact prefixLift 3841484
  have htrace : WordTrace (prefixWord ++ tailWord_3841484) baseStart_3841484 baseEnd_3841484 := by
    simpa [prefixWord, tailWord_3841484, baseEnd_3841484] using wordTrace_append hprefix tailTrace_3841484
  have hstable : (prefixWord ++ tailWord_3841484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841484).length < 2 ^ (prefixWord ++ tailWord_3841484).sum := by decide
  have hdescent : baseEnd_3841484 < baseStart_3841484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841493 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3841493 : Nat := 118140960795 + 3841493 * 2 ^ 59
def prefixEnd_3841493 : Nat := 4983230072969 + 3 ^ 40 * 3841493 * 2
def baseEnd_3841493 : Nat := 1972532339882243874670801

theorem tailTrace_3841493 : CollatzResearch.WordTrace tailWord_3841493 prefixEnd_3841493 1972532339882243874670801 := by
  unfold tailWord_3841493
  simp only [CollatzResearch.WordTrace]
  refine ⟨140110760271934410616729133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93407173514622940411152755 140110760271934410616729133)
  ·
    refine ⟨52541535101975403981273425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140110760271934410616729133 52541535101975403981273425)
    ·
      refine ⟨39406151326481552985955069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52541535101975403981273425 39406151326481552985955069)
      ·
        refine ⟨14777306747430582369733151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39406151326481552985955069 14777306747430582369733151)
        ·
          refine ⟨22165960121145873554599727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777306747430582369733151 22165960121145873554599727)
          ·
            refine ⟨33248940181718810331899591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22165960121145873554599727 33248940181718810331899591)
            ·
              refine ⟨49873410272578215497849387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33248940181718810331899591 49873410272578215497849387)
              ·
                refine ⟨74810115408867323246774081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49873410272578215497849387 74810115408867323246774081)
                ·
                  refine ⟨56107586556650492435080561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74810115408867323246774081 56107586556650492435080561)
                  ·
                    refine ⟨42080689917487869326310421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56107586556650492435080561 42080689917487869326310421)
                    ·
                      refine ⟨1972532339882243874670801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42080689917487869326310421 1972532339882243874670801)
                      ·
                        rfl

theorem cell23_3841493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3841493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841493 prefixEnd_3841493 := by exact prefixLift 3841493
  have htrace : WordTrace (prefixWord ++ tailWord_3841493) baseStart_3841493 baseEnd_3841493 := by
    simpa [prefixWord, tailWord_3841493, baseEnd_3841493] using wordTrace_append hprefix tailTrace_3841493
  have hstable : (prefixWord ++ tailWord_3841493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841493).length < 2 ^ (prefixWord ++ tailWord_3841493).sum := by decide
  have hdescent : baseEnd_3841493 < baseStart_3841493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841494 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3841494 : Nat := 118140960795 + 3841494 * 2 ^ 59
def prefixEnd_3841494 : Nat := 4983230072969 + 3 ^ 40 * 3841494 * 2
def baseEnd_3841494 : Nat := 657510951120966123586099

theorem tailTrace_3841494 : CollatzResearch.WordTrace tailWord_3841494 prefixEnd_3841494 657510951120966123586099 := by
  unfold tailWord_3841494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756924796558174236719721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93407197829953858525010357 8756924796558174236719721)
  ·
    refine ⟨6567693597418630677539791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8756924796558174236719721 6567693597418630677539791)
    ·
      refine ⟨9851540396127946016309687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567693597418630677539791 9851540396127946016309687)
      ·
        refine ⟨14777310594191919024464531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851540396127946016309687 14777310594191919024464531)
        ·
          refine ⟨22165965891287878536696797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777310594191919024464531 22165965891287878536696797)
          ·
            refine ⟨8312237209232954451261299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22165965891287878536696797 8312237209232954451261299)
            ·
              refine ⟨12468355813849431676891949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312237209232954451261299 12468355813849431676891949)
              ·
                refine ⟨4675633430193536878834481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12468355813849431676891949 4675633430193536878834481)
                ·
                  refine ⟨3506725072645152659125861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4675633430193536878834481 3506725072645152659125861)
                  ·
                    refine ⟨657510951120966123586099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3506725072645152659125861 657510951120966123586099)
                    ·
                      rfl

theorem cell23_3841494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3841494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841494 prefixEnd_3841494 := by exact prefixLift 3841494
  have htrace : WordTrace (prefixWord ++ tailWord_3841494) baseStart_3841494 baseEnd_3841494 := by
    simpa [prefixWord, tailWord_3841494, baseEnd_3841494] using wordTrace_append hprefix tailTrace_3841494
  have hstable : (prefixWord ++ tailWord_3841494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841494).length < 2 ^ (prefixWord ++ tailWord_3841494).sum := by decide
  have hdescent : baseEnd_3841494 < baseStart_3841494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841557 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_3841557 : Nat := 118140960795 + 3841557 * 2 ^ 59
def prefixEnd_3841557 : Nat := 4983230072969 + 3 ^ 40 * 3841557 * 2
def baseEnd_3841557 : Nat := 1972565202644131624270507

theorem tailTrace_3841557 : CollatzResearch.WordTrace tailWord_3841557 prefixEnd_3841557 1972565202644131624270507 := by
  unfold tailWord_3841557
  simp only [CollatzResearch.WordTrace]
  refine ⟨140113094543702549547058925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93408729695801699698039283 140113094543702549547058925)
  ·
    refine ⟨52542410453888456080147097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140113094543702549547058925 52542410453888456080147097)
    ·
      refine ⟨39406807840416342060110323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52542410453888456080147097 39406807840416342060110323)
      ·
        refine ⟨59110211760624513090165485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39406807840416342060110323 59110211760624513090165485)
        ·
          refine ⟨22166329410234192408812057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59110211760624513090165485 22166329410234192408812057)
          ·
            refine ⟨16624747057675644306609043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22166329410234192408812057 16624747057675644306609043)
            ·
              refine ⟨24937120586513466459913565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16624747057675644306609043 24937120586513466459913565)
              ·
                refine ⟨9351420219942549922467587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24937120586513466459913565 9351420219942549922467587)
                ·
                  refine ⟨14027130329913824883701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9351420219942549922467587 14027130329913824883701381)
                  ·
                    refine ⟨2630086936858842165694009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14027130329913824883701381 2630086936858842165694009)
                    ·
                      refine ⟨1972565202644131624270507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630086936858842165694009 1972565202644131624270507)
                      ·
                        rfl

theorem cell23_3841557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_3841557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841557 prefixEnd_3841557 := by exact prefixLift 3841557
  have htrace : WordTrace (prefixWord ++ tailWord_3841557) baseStart_3841557 baseEnd_3841557 := by
    simpa [prefixWord, tailWord_3841557, baseEnd_3841557] using wordTrace_append hprefix tailTrace_3841557
  have hstable : (prefixWord ++ tailWord_3841557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841557).length < 2 ^ (prefixWord ++ tailWord_3841557).sum := by decide
  have hdescent : baseEnd_3841557 < baseStart_3841557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841573 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3841573 : Nat := 118140960795 + 3841573 * 2 ^ 59
def prefixEnd_3841573 : Nat := 4983230072969 + 3 ^ 40 * 3841573 * 2
def baseEnd_3841573 : Nat := 1972573418334603561670433

theorem tailTrace_3841573 : CollatzResearch.WordTrace tailWord_3841573 prefixEnd_3841573 1972573418334603561670433 := by
  unfold tailWord_3841573
  simp only [CollatzResearch.WordTrace]
  refine ⟨140113678111644584279641373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93409118741096389519760915 140113678111644584279641373)
  ·
    refine ⟨52542629291866719104865515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140113678111644584279641373 52542629291866719104865515)
    ·
      refine ⟨78813943937800078657298273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52542629291866719104865515 78813943937800078657298273)
      ·
        refine ⟨59110457953350058992973705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78813943937800078657298273 59110457953350058992973705)
        ·
          refine ⟨44332843465012544244730279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59110457953350058992973705 44332843465012544244730279)
          ·
            refine ⟨66499265197518816367095419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44332843465012544244730279 66499265197518816367095419)
            ·
              refine ⟨99748897796278224550643129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66499265197518816367095419 99748897796278224550643129)
              ·
                refine ⟨74811673347208668412982347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99748897796278224550643129 74811673347208668412982347)
                ·
                  refine ⟨112217510020813002619473521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74811673347208668412982347 112217510020813002619473521)
                  ·
                    refine ⟨84163132515609751964605141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112217510020813002619473521 84163132515609751964605141)
                    ·
                      refine ⟨1972573418334603561670433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84163132515609751964605141 1972573418334603561670433)
                      ·
                        rfl

theorem cell23_3841573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3841573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841573 prefixEnd_3841573 := by exact prefixLift 3841573
  have htrace : WordTrace (prefixWord ++ tailWord_3841573) baseStart_3841573 baseEnd_3841573 := by
    simpa [prefixWord, tailWord_3841573, baseEnd_3841573] using wordTrace_append hprefix tailTrace_3841573
  have hstable : (prefixWord ++ tailWord_3841573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841573).length < 2 ^ (prefixWord ++ tailWord_3841573).sum := by decide
  have hdescent : baseEnd_3841573 < baseStart_3841573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841591 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_3841591 : Nat := 118140960795 + 3841591 * 2 ^ 59
def prefixEnd_3841591 : Nat := 4983230072969 + 3 ^ 40 * 3841591 * 2
def baseEnd_3841591 : Nat := 1972582660986384491245351

theorem tailTrace_3841591 : CollatzResearch.WordTrace tailWord_3841591 prefixEnd_3841591 1972582660986384491245351 := by
  unfold tailWord_3841591
  simp only [CollatzResearch.WordTrace]
  refine ⟨140114334625579373353796627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93409556417052915569197751 140114334625579373353796627)
  ·
    refine ⟨210171501938369060030694941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140114334625579373353796627 210171501938369060030694941)
    ·
      refine ⟨78814313226888397511510603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210171501938369060030694941 78814313226888397511510603)
      ·
        refine ⟨118221469840332596267265905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78814313226888397511510603 118221469840332596267265905)
        ·
          refine ⟨88666102380249447200449429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118221469840332596267265905 88666102380249447200449429)
          ·
            refine ⟨4156223549074192837521067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88666102380249447200449429 4156223549074192837521067)
            ·
              refine ⟨6234335323611289256281601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156223549074192837521067 6234335323611289256281601)
              ·
                refine ⟨4675751492708466942211201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234335323611289256281601 4675751492708466942211201)
                ·
                  refine ⟨3506813619531350206658401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4675751492708466942211201 3506813619531350206658401)
                  ·
                    refine ⟨2630110214648512654993801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506813619531350206658401 2630110214648512654993801)
                    ·
                      refine ⟨1972582660986384491245351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630110214648512654993801 1972582660986384491245351)
                      ·
                        rfl

theorem cell23_3841591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_3841591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841591 prefixEnd_3841591 := by exact prefixLift 3841591
  have htrace : WordTrace (prefixWord ++ tailWord_3841591) baseStart_3841591 baseEnd_3841591 := by
    simpa [prefixWord, tailWord_3841591, baseEnd_3841591] using wordTrace_append hprefix tailTrace_3841591
  have hstable : (prefixWord ++ tailWord_3841591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841591).length < 2 ^ (prefixWord ++ tailWord_3841591).sum := by decide
  have hdescent : baseEnd_3841591 < baseStart_3841591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841597 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 7]
def baseStart_3841597 : Nat := 118140960795 + 3841597 * 2 ^ 59
def prefixEnd_3841597 : Nat := 4983230072969 + 3 ^ 40 * 3841597 * 2
def baseEnd_3841597 : Nat := 219176193541145718641147

theorem tailTrace_3841597 : CollatzResearch.WordTrace tailWord_3841597 prefixEnd_3841597 219176193541145718641147 := by
  unfold tailWord_3841597
  simp only [CollatzResearch.WordTrace]
  refine ⟨140114553463557636378515045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93409702309038424252343363 140114553463557636378515045)
  ·
    refine ⟨26271478774417056820971571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140114553463557636378515045 26271478774417056820971571)
    ·
      refine ⟨39407218161625585231457357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26271478774417056820971571 39407218161625585231457357)
      ·
        refine ⟨14777706810609594461796509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39407218161625585231457357 14777706810609594461796509)
        ·
          refine ⟨5541640053978597923173691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14777706810609594461796509 5541640053978597923173691)
          ·
            refine ⟨8312460080967896884760537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541640053978597923173691 8312460080967896884760537)
            ·
              refine ⟨6234345060725922663570403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312460080967896884760537 6234345060725922663570403)
              ·
                refine ⟨9351517591088883995355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234345060725922663570403 9351517591088883995355605)
                ·
                  refine ⟨219176193541145718641147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9351517591088883995355605 219176193541145718641147)
                  ·
                    rfl

theorem cell23_3841597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_3841597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841597 prefixEnd_3841597 := by exact prefixLift 3841597
  have htrace : WordTrace (prefixWord ++ tailWord_3841597) baseStart_3841597 baseEnd_3841597 := by
    simpa [prefixWord, tailWord_3841597, baseEnd_3841597] using wordTrace_append hprefix tailTrace_3841597
  have hstable : (prefixWord ++ tailWord_3841597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841597).length < 2 ^ (prefixWord ++ tailWord_3841597).sum := by decide
  have hdescent : baseEnd_3841597 < baseStart_3841597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841680 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_3841680 : Nat := 118140960795 + 3841680 * 2 ^ 59
def prefixEnd_3841680 : Nat := 4983230072969 + 3 ^ 40 * 3841680 * 2
def baseEnd_3841680 : Nat := 1972628360764634643032441

theorem tailTrace_3841680 : CollatzResearch.WordTrace tailWord_3841680 prefixEnd_3841680 1972628360764634643032441 := by
  unfold tailWord_3841680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70058790361128470776893247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93411720481504627702524329 70058790361128470776893247)
  ·
    refine ⟨105088185541692706165339871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70058790361128470776893247 105088185541692706165339871)
    ·
      refine ⟨157632278312539059248009807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105088185541692706165339871 157632278312539059248009807)
      ·
        refine ⟨236448417468808588872014711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157632278312539059248009807 236448417468808588872014711)
        ·
          refine ⟨354672626203212883308022067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236448417468808588872014711 354672626203212883308022067)
          ·
            refine ⟨532008939304819324962033101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354672626203212883308022067 532008939304819324962033101)
            ·
              refine ⟨199503352239307246860762413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532008939304819324962033101 199503352239307246860762413)
              ·
                refine ⟨74813757089740217572785905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199503352239307246860762413 74813757089740217572785905)
                ·
                  refine ⟨56110317817305163179589429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74813757089740217572785905 56110317817305163179589429)
                  ·
                    refine ⟨5260342295372359048086509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56110317817305163179589429 5260342295372359048086509)
                    ·
                      refine ⟨1972628360764634643032441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260342295372359048086509 1972628360764634643032441)
                      ·
                        rfl

theorem cell23_3841680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_3841680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841680 prefixEnd_3841680 := by exact prefixLift 3841680
  have htrace : WordTrace (prefixWord ++ tailWord_3841680) baseStart_3841680 baseEnd_3841680 := by
    simpa [prefixWord, tailWord_3841680, baseEnd_3841680] using wordTrace_append hprefix tailTrace_3841680
  have hstable : (prefixWord ++ tailWord_3841680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841680).length < 2 ^ (prefixWord ++ tailWord_3841680).sum := by decide
  have hdescent : baseEnd_3841680 < baseStart_3841680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841748 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3841748 : Nat := 118140960795 + 3841748 * 2 ^ 59
def prefixEnd_3841748 : Nat := 4983230072969 + 3 ^ 40 * 3841748 * 2
def baseEnd_3841748 : Nat := 1972663277449140376982129

theorem tailTrace_3841748 : CollatzResearch.WordTrace tailWord_3841748 prefixEnd_3841748 1972663277449140376982129 := by
  unfold tailWord_3841748
  simp only [CollatzResearch.WordTrace]
  refine ⟨70060030443005294583630949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93413373924007059444841265 70060030443005294583630949)
  ·
    refine ⟨13136255708063492734430803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70060030443005294583630949 13136255708063492734430803)
    ·
      refine ⟨19704383562095239101646205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13136255708063492734430803 19704383562095239101646205)
      ·
        refine ⟨7389143835785714663117327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19704383562095239101646205 7389143835785714663117327)
        ·
          refine ⟨11083715753678571994675991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389143835785714663117327 11083715753678571994675991)
          ·
            refine ⟨16625573630517857992013987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083715753678571994675991 16625573630517857992013987)
            ·
              refine ⟨24938360445776786988020981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16625573630517857992013987 24938360445776786988020981)
              ·
                refine ⟨2337971291791573780126967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24938360445776786988020981 2337971291791573780126967)
                ·
                  refine ⟨3506956937687360670190451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337971291791573780126967 3506956937687360670190451)
                  ·
                    refine ⟨5260435406531041005285677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3506956937687360670190451 5260435406531041005285677)
                    ·
                      refine ⟨1972663277449140376982129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260435406531041005285677 1972663277449140376982129)
                      ·
                        rfl

theorem cell23_3841748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3841748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841748 prefixEnd_3841748 := by exact prefixLift 3841748
  have htrace : WordTrace (prefixWord ++ tailWord_3841748) baseStart_3841748 baseEnd_3841748 := by
    simpa [prefixWord, tailWord_3841748, baseEnd_3841748] using wordTrace_append hprefix tailTrace_3841748
  have hstable : (prefixWord ++ tailWord_3841748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841748).length < 2 ^ (prefixWord ++ tailWord_3841748).sum := by decide
  have hdescent : baseEnd_3841748 < baseStart_3841748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841754 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_3841754 : Nat := 118140960795 + 3841754 * 2 ^ 59
def prefixEnd_3841754 : Nat := 4983230072969 + 3 ^ 40 * 3841754 * 2
def baseEnd_3841754 : Nat := 1972666358333067353507101

theorem tailTrace_3841754 : CollatzResearch.WordTrace tailWord_3841754 prefixEnd_3841754 1972666358333067353507101 := by
  unfold tailWord_3841754
  simp only [CollatzResearch.WordTrace]
  refine ⟨35030069930997213047995079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93413519815992568127986877 35030069930997213047995079)
  ·
    refine ⟨52545104896495819571992619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35030069930997213047995079 52545104896495819571992619)
    ·
      refine ⟨78817657344743729357988929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52545104896495819571992619 78817657344743729357988929)
      ·
        refine ⟨59113243008557797018491697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78817657344743729357988929 59113243008557797018491697)
        ·
          refine ⟨44334932256418347763868773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59113243008557797018491697 44334932256418347763868773)
          ·
            refine ⟨8312799798078440205725395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44334932256418347763868773 8312799798078440205725395)
            ·
              refine ⟨12469199697117660308588093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312799798078440205725395 12469199697117660308588093)
              ·
                refine ⟨4675949886419122615720535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12469199697117660308588093 4675949886419122615720535)
                ·
                  refine ⟨7013924829628683923580803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675949886419122615720535 7013924829628683923580803)
                  ·
                    refine ⟨10520887244443025885371205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7013924829628683923580803 10520887244443025885371205)
                    ·
                      refine ⟨1972666358333067353507101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10520887244443025885371205 1972666358333067353507101)
                      ·
                        rfl

theorem cell23_3841754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_3841754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841754 prefixEnd_3841754 := by exact prefixLift 3841754
  have htrace : WordTrace (prefixWord ++ tailWord_3841754) baseStart_3841754 baseEnd_3841754 := by
    simpa [prefixWord, tailWord_3841754, baseEnd_3841754] using wordTrace_append hprefix tailTrace_3841754
  have hstable : (prefixWord ++ tailWord_3841754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841754).length < 2 ^ (prefixWord ++ tailWord_3841754).sum := by decide
  have hdescent : baseEnd_3841754 < baseStart_3841754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841787 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3]
def baseStart_3841787 : Nat := 118140960795 + 3841787 * 2 ^ 59
def prefixEnd_3841787 : Nat := 4983230072969 + 3 ^ 40 * 3841787 * 2
def baseEnd_3841787 : Nat := 1972683303194665724394449

theorem tailTrace_3841787 : CollatzResearch.WordTrace tailWord_3841787 prefixEnd_3841787 1972683303194665724394449 := by
  unfold tailWord_3841787
  simp only [CollatzResearch.WordTrace]
  refine ⟨140121483332869298827931615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93414322221912865885287743 140121483332869298827931615)
  ·
    refine ⟨210182224999303948241897423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140121483332869298827931615 210182224999303948241897423)
    ·
      refine ⟨315273337498955922362846135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210182224999303948241897423 315273337498955922362846135)
      ·
        refine ⟨472910006248433883544269203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315273337498955922362846135 472910006248433883544269203)
        ·
          refine ⟨709365009372650825316403805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472910006248433883544269203 709365009372650825316403805)
          ·
            refine ⟨266011878514744059493651427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709365009372650825316403805 266011878514744059493651427)
            ·
              refine ⟨399017817772116089240477141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266011878514744059493651427 399017817772116089240477141)
              ·
                refine ⟨9351980104033970841573683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 399017817772116089240477141 9351980104033970841573683)
                ·
                  refine ⟨14027970156050956262360525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9351980104033970841573683 14027970156050956262360525)
                  ·
                    refine ⟨5260488808519108598385197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14027970156050956262360525 5260488808519108598385197)
                    ·
                      refine ⟨1972683303194665724394449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260488808519108598385197 1972683303194665724394449)
                      ·
                        rfl

theorem cell23_3841787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3].length) (baseStart_3841787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841787 prefixEnd_3841787 := by exact prefixLift 3841787
  have htrace : WordTrace (prefixWord ++ tailWord_3841787) baseStart_3841787 baseEnd_3841787 := by
    simpa [prefixWord, tailWord_3841787, baseEnd_3841787] using wordTrace_append hprefix tailTrace_3841787
  have hstable : (prefixWord ++ tailWord_3841787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841787).length < 2 ^ (prefixWord ++ tailWord_3841787).sum := by decide
  have hdescent : baseEnd_3841787 < baseStart_3841787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841804 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_3841804 : Nat := 118140960795 + 3841804 * 2 ^ 59
def prefixEnd_3841804 : Nat := 4983230072969 + 3 ^ 40 * 3841804 * 2
def baseEnd_3841804 : Nat := 1972692032365792157881871

theorem tailTrace_3841804 : CollatzResearch.WordTrace tailWord_3841804 prefixEnd_3841804 1972692032365792157881871 := by
  unfold tailWord_3841804
  simp only [CollatzResearch.WordTrace]
  refine ⟨70061051686903855365650233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93414735582538473820866977 70061051686903855365650233)
  ·
    refine ⟨52545788765177891524237675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70061051686903855365650233 52545788765177891524237675)
    ·
      refine ⟨78818683147766837286356513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52545788765177891524237675 78818683147766837286356513)
      ·
        refine ⟨59114012360825127964767385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78818683147766837286356513 59114012360825127964767385)
        ·
          refine ⟨44335509270618845973575539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59114012360825127964767385 44335509270618845973575539)
          ·
            refine ⟨66503263905928268960363309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44335509270618845973575539 66503263905928268960363309)
            ·
              refine ⟨24938723964723100860136241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66503263905928268960363309 24938723964723100860136241)
              ·
                refine ⟨18704042973542325645102181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24938723964723100860136241 18704042973542325645102181)
                ·
                  refine ⟨3507008057539186058456659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18704042973542325645102181 3507008057539186058456659)
                  ·
                    refine ⟨5260512086308779087684989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507008057539186058456659 5260512086308779087684989)
                    ·
                      refine ⟨1972692032365792157881871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260512086308779087684989 1972692032365792157881871)
                      ·
                        rfl

theorem cell23_3841804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_3841804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841804 prefixEnd_3841804 := by exact prefixLift 3841804
  have htrace : WordTrace (prefixWord ++ tailWord_3841804) baseStart_3841804 baseEnd_3841804 := by
    simpa [prefixWord, tailWord_3841804, baseEnd_3841804] using wordTrace_append hprefix tailTrace_3841804
  have hstable : (prefixWord ++ tailWord_3841804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841804).length < 2 ^ (prefixWord ++ tailWord_3841804).sum := by decide
  have hdescent : baseEnd_3841804 < baseStart_3841804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841847 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_3841847 : Nat := 118140960795 + 3841847 * 2 ^ 59
def prefixEnd_3841847 : Nat := 4983230072969 + 3 ^ 40 * 3841847 * 2
def baseEnd_3841847 : Nat := 1972714112033935489644173

theorem tailTrace_3841847 : CollatzResearch.WordTrace tailWord_3841847 prefixEnd_3841847 1972714112033935489644173 := by
  unfold tailWord_3841847
  simp only [CollatzResearch.WordTrace]
  refine ⟨140123671712651929075115795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93415781141767952716743863 140123671712651929075115795)
  ·
    refine ⟨210185507568977893612673693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140123671712651929075115795 210185507568977893612673693)
    ·
      refine ⟨78819565338366710104752635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210185507568977893612673693 78819565338366710104752635)
      ·
        refine ⟨118229348007550065157128953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78819565338366710104752635 118229348007550065157128953)
        ·
          refine ⟨88672011005662548867846715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118229348007550065157128953 88672011005662548867846715)
          ·
            refine ⟨133008016508493823301770073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88672011005662548867846715 133008016508493823301770073)
            ·
              refine ⟨99756012381370367476327555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133008016508493823301770073 99756012381370367476327555)
              ·
                refine ⟨149634018572055551214491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99756012381370367476327555 149634018572055551214491333)
                ·
                  refine ⟨28056378482260415852717125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149634018572055551214491333 28056378482260415852717125)
                  ·
                    refine ⟨5260570965423827972384461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28056378482260415852717125 5260570965423827972384461)
                    ·
                      refine ⟨1972714112033935489644173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260570965423827972384461 1972714112033935489644173)
                      ·
                        rfl

theorem cell23_3841847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_3841847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841847 prefixEnd_3841847 := by exact prefixLift 3841847
  have htrace : WordTrace (prefixWord ++ tailWord_3841847) baseStart_3841847 baseEnd_3841847 := by
    simpa [prefixWord, tailWord_3841847, baseEnd_3841847] using wordTrace_append hprefix tailTrace_3841847
  have hstable : (prefixWord ++ tailWord_3841847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841847).length < 2 ^ (prefixWord ++ tailWord_3841847).sum := by decide
  have hdescent : baseEnd_3841847 < baseStart_3841847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841848 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_3841848 : Nat := 118140960795 + 3841848 * 2 ^ 59
def prefixEnd_3841848 : Nat := 4983230072969 + 3 ^ 40 * 3841848 * 2
def baseEnd_3841848 : Nat := 1972714625514589985731669

theorem tailTrace_3841848 : CollatzResearch.WordTrace tailWord_3841848 prefixEnd_3841848 1972714625514589985731669 := by
  unfold tailWord_3841848
  simp only [CollatzResearch.WordTrace]
  refine ⟨70061854092824153122951099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93415805457098870830601465 70061854092824153122951099)
  ·
    refine ⟨105092781139236229684426649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70061854092824153122951099 105092781139236229684426649)
    ·
      refine ⟨78819585854427172263319987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105092781139236229684426649 78819585854427172263319987)
      ·
        refine ⟨118229378781640758394979981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78819585854427172263319987 118229378781640758394979981)
        ·
          refine ⟨44336017043115284398117493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118229378781640758394979981 44336017043115284398117493)
          ·
            refine ⟨4156501597792057912323515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44336017043115284398117493 4156501597792057912323515)
            ·
              refine ⟨6234752396688086868485273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156501597792057912323515 6234752396688086868485273)
              ·
                refine ⟨4676064297516065151363955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234752396688086868485273 4676064297516065151363955)
                ·
                  refine ⟨7014096446274097727045933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676064297516065151363955 7014096446274097727045933)
                  ·
                    refine ⟨2630286167352786647642225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7014096446274097727045933 2630286167352786647642225)
                    ·
                      refine ⟨1972714625514589985731669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630286167352786647642225 1972714625514589985731669)
                      ·
                        rfl

theorem cell23_3841848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_3841848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841848 prefixEnd_3841848 := by exact prefixLift 3841848
  have htrace : WordTrace (prefixWord ++ tailWord_3841848) baseStart_3841848 baseEnd_3841848 := by
    simpa [prefixWord, tailWord_3841848, baseEnd_3841848] using wordTrace_append hprefix tailTrace_3841848
  have hstable : (prefixWord ++ tailWord_3841848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841848).length < 2 ^ (prefixWord ++ tailWord_3841848).sum := by decide
  have hdescent : baseEnd_3841848 < baseStart_3841848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841897 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_3841897 : Nat := 118140960795 + 3841897 * 2 ^ 59
def prefixEnd_3841897 : Nat := 4983230072969 + 3 ^ 40 * 3841897 * 2
def baseEnd_3841897 : Nat := 657579928688886764672981

theorem tailTrace_3841897 : CollatzResearch.WordTrace tailWord_3841897 prefixEnd_3841897 657579928688886764672981 := by
  unfold tailWord_3841897
  simp only [CollatzResearch.WordTrace]
  refine ⟨140125495362470787614435945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93416996908313858409623963 140125495362470787614435945)
  ·
    refine ⟨105094121521853090710826959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140125495362470787614435945 105094121521853090710826959)
    ·
      refine ⟨157641182282779636066240439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105094121521853090710826959 157641182282779636066240439)
      ·
        refine ⟨236461773424169454099360659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157641182282779636066240439 236461773424169454099360659)
        ·
          refine ⟨354692660136254181149040989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236461773424169454099360659 354692660136254181149040989)
          ·
            refine ⟨133009747551095317930890371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354692660136254181149040989 133009747551095317930890371)
            ·
              refine ⟨199514621326642976896335557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133009747551095317930890371 199514621326642976896335557)
              ·
                refine ⟨37408991498745558168062917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199514621326642976896335557 37408991498745558168062917)
                ·
                  refine ⟨7014185906014792156511797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37408991498745558168062917 7014185906014792156511797)
                  ·
                    refine ⟨657579928688886764672981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7014185906014792156511797 657579928688886764672981)
                    ·
                      rfl

theorem cell23_3841897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_3841897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841897 prefixEnd_3841897 := by exact prefixLift 3841897
  have htrace : WordTrace (prefixWord ++ tailWord_3841897) baseStart_3841897 baseEnd_3841897 := by
    simpa [prefixWord, tailWord_3841897, baseEnd_3841897] using wordTrace_append hprefix tailTrace_3841897
  have hstable : (prefixWord ++ tailWord_3841897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841897).length < 2 ^ (prefixWord ++ tailWord_3841897).sum := by decide
  have hdescent : baseEnd_3841897 < baseStart_3841897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841904 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2]
def baseStart_3841904 : Nat := 118140960795 + 3841904 * 2 ^ 59
def prefixEnd_3841904 : Nat := 4983230072969 + 3 ^ 40 * 3841904 * 2
def baseEnd_3841904 : Nat := 1972743380431241766631411

theorem tailTrace_3841904 : CollatzResearch.WordTrace tailWord_3841904 prefixEnd_3841904 1972743380431241766631411 := by
  unfold tailWord_3841904
  simp only [CollatzResearch.WordTrace]
  refine ⟨70062875336722713904970383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93417167115630285206627177 70062875336722713904970383)
  ·
    refine ⟨105094313005084070857455575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70062875336722713904970383 105094313005084070857455575)
    ·
      refine ⟨157641469507626106286183363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105094313005084070857455575 157641469507626106286183363)
      ·
        refine ⟨236462204261439159429275045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157641469507626106286183363 236462204261439159429275045)
        ·
          refine ⟨44336663299019842392989071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236462204261439159429275045 44336663299019842392989071)
          ·
            refine ⟨66504994948529763589483607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44336663299019842392989071 66504994948529763589483607)
            ·
              refine ⟨99757492422794645384225411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66504994948529763589483607 99757492422794645384225411)
              ·
                refine ⟨149636238634191968076338117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99757492422794645384225411 149636238634191968076338117)
                ·
                  refine ⟨28056794743910994014313397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149636238634191968076338117 28056794743910994014313397)
                  ·
                    refine ⟨2630324507241655688841881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28056794743910994014313397 2630324507241655688841881)
                    ·
                      refine ⟨1972743380431241766631411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630324507241655688841881 1972743380431241766631411)
                      ·
                        rfl

theorem cell23_3841904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2].length) (baseStart_3841904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841904 prefixEnd_3841904 := by exact prefixLift 3841904
  have htrace : WordTrace (prefixWord ++ tailWord_3841904) baseStart_3841904 baseEnd_3841904 := by
    simpa [prefixWord, tailWord_3841904, baseEnd_3841904] using wordTrace_append hprefix tailTrace_3841904
  have hstable : (prefixWord ++ tailWord_3841904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841904).length < 2 ^ (prefixWord ++ tailWord_3841904).sum := by decide
  have hdescent : baseEnd_3841904 < baseStart_3841904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841914 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_3841914 : Nat := 118140960795 + 3841914 * 2 ^ 59
def prefixEnd_3841914 : Nat := 4983230072969 + 3 ^ 40 * 3841914 * 2
def baseEnd_3841914 : Nat := 657582838412595575835455

theorem tailTrace_3841914 : CollatzResearch.WordTrace tailWord_3841914 prefixEnd_3841914 657582838412595575835455 := by
  unfold tailWord_3841914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35031528850852299879451199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93417410268939466345203197 35031528850852299879451199)
  ·
    refine ⟨52547293276278449819176799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35031528850852299879451199 52547293276278449819176799)
    ·
      refine ⟨78820939914417674728765199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52547293276278449819176799 78820939914417674728765199)
      ·
        refine ⟨118231409871626512093147799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78820939914417674728765199 118231409871626512093147799)
        ·
          refine ⟨177347114807439768139721699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118231409871626512093147799 177347114807439768139721699)
          ·
            refine ⟨266020672211159652209582549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177347114807439768139721699 266020672211159652209582549)
            ·
              refine ⟨6234859504949054348662091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266020672211159652209582549 6234859504949054348662091)
              ·
                refine ⟨9352289257423581522993137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234859504949054348662091 9352289257423581522993137)
                ·
                  refine ⟨7014216943067686142244853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9352289257423581522993137 7014216943067686142244853)
                  ·
                    refine ⟨657582838412595575835455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7014216943067686142244853 657582838412595575835455)
                    ·
                      rfl

theorem cell23_3841914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_3841914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841914 prefixEnd_3841914 := by exact prefixLift 3841914
  have htrace : WordTrace (prefixWord ++ tailWord_3841914) baseStart_3841914 baseEnd_3841914 := by
    simpa [prefixWord, tailWord_3841914, baseEnd_3841914] using wordTrace_append hprefix tailTrace_3841914
  have hstable : (prefixWord ++ tailWord_3841914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841914).length < 2 ^ (prefixWord ++ tailWord_3841914).sum := by decide
  have hdescent : baseEnd_3841914 < baseStart_3841914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841918 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3841918 : Nat := 118140960795 + 3841918 * 2 ^ 59
def prefixEnd_3841918 : Nat := 4983230072969 + 3 ^ 40 * 3841918 * 2
def baseEnd_3841918 : Nat := 219194507684489412428483

theorem tailTrace_3841918 : CollatzResearch.WordTrace tailWord_3841918 prefixEnd_3841918 219194507684489412428483 := by
  unfold tailWord_3841918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515782661924338525118801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93417507530263138800633605 17515782661924338525118801)
  ·
    refine ⟨13136836996443253893839101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17515782661924338525118801 13136836996443253893839101)
    ·
      refine ⟨4926313873666220210189663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13136836996443253893839101 4926313873666220210189663)
      ·
        refine ⟨7389470810499330315284495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926313873666220210189663 7389470810499330315284495)
        ·
          refine ⟨11084206215748995472926743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389470810499330315284495 11084206215748995472926743)
          ·
            refine ⟨16626309323623493209390115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11084206215748995472926743 16626309323623493209390115)
            ·
              refine ⟨24939463985435239814085173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16626309323623493209390115 24939463985435239814085173)
              ·
                refine ⟨2338074748634553732570485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24939463985435239814085173 2338074748634553732570485)
                ·
                  refine ⟨219194507684489412428483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2338074748634553732570485 219194507684489412428483)
                  ·
                    rfl

theorem cell23_3841918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3841918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841918 prefixEnd_3841918 := by exact prefixLift 3841918
  have htrace : WordTrace (prefixWord ++ tailWord_3841918) baseStart_3841918 baseEnd_3841918 := by
    simpa [prefixWord, tailWord_3841918, baseEnd_3841918] using wordTrace_append hprefix tailTrace_3841918
  have hstable : (prefixWord ++ tailWord_3841918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841918).length < 2 ^ (prefixWord ++ tailWord_3841918).sum := by decide
  have hdescent : baseEnd_3841918 < baseStart_3841918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3841937 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_3841937 : Nat := 118140960795 + 3841937 * 2 ^ 59
def prefixEnd_3841937 : Nat := 4983230072969 + 3 ^ 40 * 3841937 * 2
def baseEnd_3841937 : Nat := 1972760325292840137518759

theorem tailTrace_3841937 : CollatzResearch.WordTrace tailWord_3841937 prefixEnd_3841937 1972760325292840137518759 := by
  unfold tailWord_3841937
  simp only [CollatzResearch.WordTrace]
  refine ⟨140126954282325874445892065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93417969521550582963928043 140126954282325874445892065)
  ·
    refine ⟨105095215711744405834419049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140126954282325874445892065 105095215711744405834419049)
    ·
      refine ⟨78821411783808304375814287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105095215711744405834419049 78821411783808304375814287)
      ·
        refine ⟨118232117675712456563721431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78821411783808304375814287 118232117675712456563721431)
        ·
          refine ⟨177348176513568684845582147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118232117675712456563721431 177348176513568684845582147)
          ·
            refine ⟨266022264770353027268373221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177348176513568684845582147 266022264770353027268373221)
            ·
              refine ⟨49879174644441192612819979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266022264770353027268373221 49879174644441192612819979)
              ·
                refine ⟨74818761966661788919229969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49879174644441192612819979 74818761966661788919229969)
                ·
                  refine ⟨56114071474996341689422477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74818761966661788919229969 56114071474996341689422477)
                  ·
                    refine ⟨21042776803123628133533429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56114071474996341689422477 21042776803123628133533429)
                    ·
                      refine ⟨1972760325292840137518759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21042776803123628133533429 1972760325292840137518759)
                      ·
                        rfl

theorem cell23_3841937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_3841937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3841937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3841937 prefixEnd_3841937 := by exact prefixLift 3841937
  have htrace : WordTrace (prefixWord ++ tailWord_3841937) baseStart_3841937 baseEnd_3841937 := by
    simpa [prefixWord, tailWord_3841937, baseEnd_3841937] using wordTrace_append hprefix tailTrace_3841937
  have hstable : (prefixWord ++ tailWord_3841937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3841937).length < 2 ^ (prefixWord ++ tailWord_3841937).sum := by decide
  have hdescent : baseEnd_3841937 < baseStart_3841937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3841937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842001 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_3842001 : Nat := 118140960795 + 3842001 * 2 ^ 59
def prefixEnd_3842001 : Nat := 4983230072969 + 3 ^ 40 * 3842001 * 2
def baseEnd_3842001 : Nat := 1972793188054727887118465

theorem tailTrace_3842001 : CollatzResearch.WordTrace tailWord_3842001 prefixEnd_3842001 1972793188054727887118465 := by
  unfold tailWord_3842001
  simp only [CollatzResearch.WordTrace]
  refine ⟨140129288554094013376221857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93419525702729342250814571 140129288554094013376221857)
  ·
    refine ⟨105096966415570510032166393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140129288554094013376221857 105096966415570510032166393)
    ·
      refine ⟨78822724811677882524124795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105096966415570510032166393 78822724811677882524124795)
      ·
        refine ⟨118234087217516823786187193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78822724811677882524124795 118234087217516823786187193)
        ·
          refine ⟨88675565413137617839640395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118234087217516823786187193 88675565413137617839640395)
          ·
            refine ⟨133013348119706426759460593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88675565413137617839640395 133013348119706426759460593)
            ·
              refine ⟨99760011089779820069595445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133013348119706426759460593 99760011089779820069595445)
              ·
                refine ⟨9352501039666858131524573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99760011089779820069595445 9352501039666858131524573)
                ·
                  refine ⟨3507187889875071799321715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9352501039666858131524573 3507187889875071799321715)
                  ·
                    refine ⟨5260781834812607698982573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507187889875071799321715 5260781834812607698982573)
                    ·
                      refine ⟨1972793188054727887118465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260781834812607698982573 1972793188054727887118465)
                      ·
                        rfl

theorem cell23_3842001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_3842001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842001 prefixEnd_3842001 := by exact prefixLift 3842001
  have htrace : WordTrace (prefixWord ++ tailWord_3842001) baseStart_3842001 baseEnd_3842001 := by
    simpa [prefixWord, tailWord_3842001, baseEnd_3842001] using wordTrace_append hprefix tailTrace_3842001
  have hstable : (prefixWord ++ tailWord_3842001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842001).length < 2 ^ (prefixWord ++ tailWord_3842001).sum := by decide
  have hdescent : baseEnd_3842001 < baseStart_3842001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842108 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3842108 : Nat := 118140960795 + 3842108 * 2 ^ 59
def prefixEnd_3842108 : Nat := 4983230072969 + 3 ^ 40 * 3842108 * 2
def baseEnd_3842108 : Nat := 1972848130484758968480473

theorem tailTrace_3842108 : CollatzResearch.WordTrace tailWord_3842108 prefixEnd_3842108 1972848130484758968480473 := by
  unfold tailWord_3842108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70066595582353185325183489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93422127443137580433577985 70066595582353185325183489)
  ·
    refine ⟨52549946686764888993887617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70066595582353185325183489 52549946686764888993887617)
    ·
      refine ⟨39412460015073666745415713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52549946686764888993887617 39412460015073666745415713)
      ·
        refine ⟨29559345011305250059061785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39412460015073666745415713 29559345011305250059061785)
        ·
          refine ⟨22169508758478937544296339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29559345011305250059061785 22169508758478937544296339)
          ·
            refine ⟨33254263137718406316444509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22169508758478937544296339 33254263137718406316444509)
            ·
              refine ⟨12470348676644402368666691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33254263137718406316444509 12470348676644402368666691)
              ·
                refine ⟨18705523014966603553000037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12470348676644402368666691 18705523014966603553000037)
                ·
                  refine ⟨3507285565306238166187507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18705523014966603553000037 3507285565306238166187507)
                  ·
                    refine ⟨5260928347959357249281261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507285565306238166187507 5260928347959357249281261)
                    ·
                      refine ⟨1972848130484758968480473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5260928347959357249281261 1972848130484758968480473)
                      ·
                        rfl

theorem cell23_3842108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3842108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842108 prefixEnd_3842108 := by exact prefixLift 3842108
  have htrace : WordTrace (prefixWord ++ tailWord_3842108) baseStart_3842108 baseEnd_3842108 := by
    simpa [prefixWord, tailWord_3842108, baseEnd_3842108] using wordTrace_append hprefix tailTrace_3842108
  have hstable : (prefixWord ++ tailWord_3842108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842108).length < 2 ^ (prefixWord ++ tailWord_3842108).sum := by decide
  have hdescent : baseEnd_3842108 < baseStart_3842108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842148 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_3842148 : Nat := 118140960795 + 3842148 * 2 ^ 59
def prefixEnd_3842148 : Nat := 4983230072969 + 3 ^ 40 * 3842148 * 2
def baseEnd_3842148 : Nat := 1972868669710938811980289

theorem tailTrace_3842148 : CollatzResearch.WordTrace tailWord_3842148 prefixEnd_3842148 1972868669710938811980289 := by
  unfold tailWord_3842148
  simp only [CollatzResearch.WordTrace]
  refine ⟨70067325042280728740911549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93423100056374304987882065 70067325042280728740911549)
  ·
    refine ⟨26275246890855273277841831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70067325042280728740911549 26275246890855273277841831)
    ·
      refine ⟨39412870336282909916762747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26275246890855273277841831 39412870336282909916762747)
      ·
        refine ⟨59119305504424364875144121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39412870336282909916762747 59119305504424364875144121)
        ·
          refine ⟨44339479128318273656358091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59119305504424364875144121 44339479128318273656358091)
          ·
            refine ⟨66509218692477410484537137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44339479128318273656358091 66509218692477410484537137)
            ·
              refine ⟨49881914019358057863402853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66509218692477410484537137 49881914019358057863402853)
              ·
                refine ⟨9352858878629635849388035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49881914019358057863402853 9352858878629635849388035)
                ·
                  refine ⟨14029288317944453774082053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9352858878629635849388035 14029288317944453774082053)
                  ·
                    refine ⟨2630491559614585082640385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14029288317944453774082053 2630491559614585082640385)
                    ·
                      refine ⟨1972868669710938811980289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630491559614585082640385 1972868669710938811980289)
                      ·
                        rfl

theorem cell23_3842148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_3842148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842148 prefixEnd_3842148 := by exact prefixLift 3842148
  have htrace : WordTrace (prefixWord ++ tailWord_3842148) baseStart_3842148 baseEnd_3842148 := by
    simpa [prefixWord, tailWord_3842148, baseEnd_3842148] using wordTrace_append hprefix tailTrace_3842148
  have hstable : (prefixWord ++ tailWord_3842148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842148).length < 2 ^ (prefixWord ++ tailWord_3842148).sum := by decide
  have hdescent : baseEnd_3842148 < baseStart_3842148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842151 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3842151 : Nat := 118140960795 + 3842151 * 2 ^ 59
def prefixEnd_3842151 : Nat := 4983230072969 + 3 ^ 40 * 3842151 * 2
def baseEnd_3842151 : Nat := 1972870210152902300242775

theorem tailTrace_3842151 : CollatzResearch.WordTrace tailWord_3842151 prefixEnd_3842151 1972870210152902300242775 := by
  unfold tailWord_3842151
  simp only [CollatzResearch.WordTrace]
  refine ⟨140134759503550588994182307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93423173002367059329454871 140134759503550588994182307)
  ·
    refine ⟨210202139255325883491273461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140134759503550588994182307 210202139255325883491273461)
    ·
      refine ⟨19706450555186801577306887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210202139255325883491273461 19706450555186801577306887)
      ·
        refine ⟨29559675832780202365960331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19706450555186801577306887 29559675832780202365960331)
        ·
          refine ⟨44339513749170303548940497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29559675832780202365960331 44339513749170303548940497)
          ·
            refine ⟨33254635311877727661705373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44339513749170303548940497 33254635311877727661705373)
            ·
              refine ⟨12470488241954147873139515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33254635311877727661705373 12470488241954147873139515)
              ·
                refine ⟨18705732362931221809709273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12470488241954147873139515 18705732362931221809709273)
                ·
                  refine ⟨14029299272198416357281955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18705732362931221809709273 14029299272198416357281955)
                  ·
                    refine ⟨21043948908297624535922933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14029299272198416357281955 21043948908297624535922933)
                    ·
                      refine ⟨1972870210152902300242775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21043948908297624535922933 1972870210152902300242775)
                      ·
                        rfl

theorem cell23_3842151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3842151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842151 prefixEnd_3842151 := by exact prefixLift 3842151
  have htrace : WordTrace (prefixWord ++ tailWord_3842151) baseStart_3842151 baseEnd_3842151 := by
    simpa [prefixWord, tailWord_3842151, baseEnd_3842151] using wordTrace_append hprefix tailTrace_3842151
  have hstable : (prefixWord ++ tailWord_3842151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842151).length < 2 ^ (prefixWord ++ tailWord_3842151).sum := by decide
  have hdescent : baseEnd_3842151 < baseStart_3842151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842252 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_3842252 : Nat := 118140960795 + 3842252 * 2 ^ 59
def prefixEnd_3842252 : Nat := 4983230072969 + 3 ^ 40 * 3842252 * 2
def baseEnd_3842252 : Nat := 657640690566335468359937

theorem tailTrace_3842252 : CollatzResearch.WordTrace tailWord_3842252 prefixEnd_3842252 657640690566335468359937 := by
  unfold tailWord_3842252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70069221638092341621804505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93425628850789788829072673 70069221638092341621804505)
  ·
    refine ⟨52551916228569256216353379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70069221638092341621804505 52551916228569256216353379)
    ·
      refine ⟨78827874342853884324530069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52551916228569256216353379 78827874342853884324530069)
      ·
        refine ⟨3695056609821275827712347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78827874342853884324530069 3695056609821275827712347)
        ·
          refine ⟨5542584914731913741568521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695056609821275827712347 5542584914731913741568521)
          ·
            refine ⟨4156938686048935306176391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542584914731913741568521 4156938686048935306176391)
            ·
              refine ⟨6235408029073402959264587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156938686048935306176391 6235408029073402959264587)
              ·
                refine ⟨9353112043610104438896881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6235408029073402959264587 9353112043610104438896881)
                ·
                  refine ⟨7014834032707578329172661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9353112043610104438896881 7014834032707578329172661)
                  ·
                    refine ⟨657640690566335468359937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7014834032707578329172661 657640690566335468359937)
                    ·
                      rfl

theorem cell23_3842252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_3842252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842252 prefixEnd_3842252 := by exact prefixLift 3842252
  have htrace : WordTrace (prefixWord ++ tailWord_3842252) baseStart_3842252 baseEnd_3842252 := by
    simpa [prefixWord, tailWord_3842252, baseEnd_3842252] using wordTrace_append hprefix tailTrace_3842252
  have hstable : (prefixWord ++ tailWord_3842252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842252).length < 2 ^ (prefixWord ++ tailWord_3842252).sum := by decide
  have hdescent : baseEnd_3842252 < baseStart_3842252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842265 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 1, 4]
def baseStart_3842265 : Nat := 118140960795 + 3842265 * 2 ^ 59
def prefixEnd_3842265 : Nat := 4983230072969 + 3 ^ 40 * 3842265 * 2
def baseEnd_3842265 : Nat := 657642915649171618072417

theorem tailTrace_3842265 : CollatzResearch.WordTrace tailWord_3842265 prefixEnd_3842265 657642915649171618072417 := by
  unfold tailWord_3842265
  simp only [CollatzResearch.WordTrace]
  refine ⟨140138917425137586463832249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93425944950091724309221499 140138917425137586463832249)
  ·
    refine ⟨105104188068853189847874187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140138917425137586463832249 105104188068853189847874187)
    ·
      refine ⟨157656282103279784771811281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105104188068853189847874187 157656282103279784771811281)
      ·
        refine ⟨118242211577459838578858461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157656282103279784771811281 118242211577459838578858461)
        ·
          refine ⟨44340829341547439467071923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118242211577459838578858461 44340829341547439467071923)
          ·
            refine ⟨66511244012321159200607885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44340829341547439467071923 66511244012321159200607885)
            ·
              refine ⟨24941716504620434700227957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66511244012321159200607885 24941716504620434700227957)
              ·
                refine ⟨2338285922308165753146371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24941716504620434700227957 2338285922308165753146371)
                ·
                  refine ⟨3507428883462248629719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338285922308165753146371 3507428883462248629719557)
                  ·
                    refine ⟨657642915649171618072417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3507428883462248629719557 657642915649171618072417)
                    ·
                      rfl

theorem cell23_3842265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 4].length) (baseStart_3842265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842265 prefixEnd_3842265 := by exact prefixLift 3842265
  have htrace : WordTrace (prefixWord ++ tailWord_3842265) baseStart_3842265 baseEnd_3842265 := by
    simpa [prefixWord, tailWord_3842265, baseEnd_3842265] using wordTrace_append hprefix tailTrace_3842265
  have hstable : (prefixWord ++ tailWord_3842265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842265).length < 2 ^ (prefixWord ++ tailWord_3842265).sum := by decide
  have hdescent : baseEnd_3842265 < baseStart_3842265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842301 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3842301 : Nat := 118140960795 + 3842301 * 2 ^ 59
def prefixEnd_3842301 : Nat := 4983230072969 + 3 ^ 40 * 3842301 * 2
def baseEnd_3842301 : Nat := 1972947232251076713367085

theorem tailTrace_3842301 : CollatzResearch.WordTrace tailWord_3842301 prefixEnd_3842301 1972947232251076713367085 := by
  unfold tailWord_3842301
  simp only [CollatzResearch.WordTrace]
  refine ⟨140140230453007164612142757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93426820302004776408095171 140140230453007164612142757)
  ·
    refine ⟨26276293209938843364776767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140140230453007164612142757 26276293209938843364776767)
    ·
      refine ⟨39414439814908265047165151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26276293209938843364776767 39414439814908265047165151)
      ·
        refine ⟨59121659722362397570747727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39414439814908265047165151 59121659722362397570747727)
        ·
          refine ⟨88682489583543596356121591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59121659722362397570747727 88682489583543596356121591)
          ·
            refine ⟨133023734375315394534182387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88682489583543596356121591 133023734375315394534182387)
            ·
              refine ⟨199535601562973091801273581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133023734375315394534182387 199535601562973091801273581)
              ·
                refine ⟨74825850586114909425477593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199535601562973091801273581 74825850586114909425477593)
                ·
                  refine ⟨56119387939586182069108195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74825850586114909425477593 56119387939586182069108195)
                  ·
                    refine ⟨84179081909379273103662293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56119387939586182069108195 84179081909379273103662293)
                    ·
                      refine ⟨1972947232251076713367085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84179081909379273103662293 1972947232251076713367085)
                      ·
                        rfl

theorem cell23_3842301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3842301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842301 prefixEnd_3842301 := by exact prefixLift 3842301
  have htrace : WordTrace (prefixWord ++ tailWord_3842301) baseStart_3842301 baseEnd_3842301 := by
    simpa [prefixWord, tailWord_3842301, baseEnd_3842301] using wordTrace_append hprefix tailTrace_3842301
  have hstable : (prefixWord ++ tailWord_3842301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842301).length < 2 ^ (prefixWord ++ tailWord_3842301).sum := by decide
  have hdescent : baseEnd_3842301 < baseStart_3842301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842305 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_3842305 : Nat := 118140960795 + 3842305 * 2 ^ 59
def prefixEnd_3842305 : Nat := 4983230072969 + 3 ^ 40 * 3842305 * 2
def baseEnd_3842305 : Nat := 1972949286173694697717067

theorem tailTrace_3842305 : CollatzResearch.WordTrace tailWord_3842305 prefixEnd_3842305 1972949286173694697717067 := by
  unfold tailWord_3842305
  simp only [CollatzResearch.WordTrace]
  refine ⟨140140376344992673295288369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93426917563328448863525579 140140376344992673295288369)
  ·
    refine ⟨105105282258744504971466277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140140376344992673295288369 105105282258744504971466277)
    ·
      refine ⟨19707240423514594682149927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105105282258744504971466277 19707240423514594682149927)
      ·
        refine ⟨29560860635271892023224891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19707240423514594682149927 29560860635271892023224891)
        ·
          refine ⟨44341290952907838034837337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29560860635271892023224891 44341290952907838034837337)
          ·
            refine ⟨33255968214680878526128003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44341290952907838034837337 33255968214680878526128003)
            ·
              refine ⟨49883952322021317789192005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33255968214680878526128003 49883952322021317789192005)
              ·
                refine ⟨9353241060378997085473501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49883952322021317789192005 9353241060378997085473501)
                ·
                  refine ⟨3507465397642123907052563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9353241060378997085473501 3507465397642123907052563)
                  ·
                    refine ⟨5261198096463185860578845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507465397642123907052563 5261198096463185860578845)
                    ·
                      refine ⟨1972949286173694697717067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5261198096463185860578845 1972949286173694697717067)
                      ·
                        rfl

theorem cell23_3842305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_3842305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842305 prefixEnd_3842305 := by exact prefixLift 3842305
  have htrace : WordTrace (prefixWord ++ tailWord_3842305) baseStart_3842305 baseEnd_3842305 := by
    simpa [prefixWord, tailWord_3842305, baseEnd_3842305] using wordTrace_append hprefix tailTrace_3842305
  have hstable : (prefixWord ++ tailWord_3842305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842305).length < 2 ^ (prefixWord ++ tailWord_3842305).sum := by decide
  have hdescent : baseEnd_3842305 < baseStart_3842305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842315 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 2, 3, 2]
def baseStart_3842315 : Nat := 118140960795 + 3842315 * 2 ^ 59
def prefixEnd_3842315 : Nat := 4983230072969 + 3 ^ 40 * 3842315 * 2
def baseEnd_3842315 : Nat := 1972954420980239658592021

theorem tailTrace_3842315 : CollatzResearch.WordTrace tailWord_3842315 prefixEnd_3842315 1972954420980239658592021 := by
  unfold tailWord_3842315
  simp only [CollatzResearch.WordTrace]
  refine ⟨140140741074956445003152399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93427160716637630002101599 140140741074956445003152399)
  ·
    refine ⟨210211111612434667504728599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140140741074956445003152399 210211111612434667504728599)
    ·
      refine ⟨315316667418652001257092899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210211111612434667504728599 315316667418652001257092899)
      ·
        refine ⟨472975001127978001885639349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315316667418652001257092899 472975001127978001885639349)
        ·
          refine ⟨44341406355747937676778689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 472975001127978001885639349 44341406355747937676778689)
          ·
            refine ⟨33256054766810953257584017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44341406355747937676778689 33256054766810953257584017)
            ·
              refine ⟨24942041075108214943188013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33256054766810953257584017 24942041075108214943188013)
              ·
                refine ⟨9353265403165580603695505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24942041075108214943188013 9353265403165580603695505)
                ·
                  refine ⟨7014949052374185452771629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9353265403165580603695505 7014949052374185452771629)
                  ·
                    refine ⟨2630605894640319544789361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7014949052374185452771629 2630605894640319544789361)
                    ·
                      refine ⟨1972954420980239658592021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630605894640319544789361 1972954420980239658592021)
                      ·
                        rfl

theorem cell23_3842315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3, 2].length) (baseStart_3842315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842315 prefixEnd_3842315 := by exact prefixLift 3842315
  have htrace : WordTrace (prefixWord ++ tailWord_3842315) baseStart_3842315 baseEnd_3842315 := by
    simpa [prefixWord, tailWord_3842315, baseEnd_3842315] using wordTrace_append hprefix tailTrace_3842315
  have hstable : (prefixWord ++ tailWord_3842315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842315).length < 2 ^ (prefixWord ++ tailWord_3842315).sum := by decide
  have hdescent : baseEnd_3842315 < baseStart_3842315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842339 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 1, 1, 3]
def baseStart_3842339 : Nat := 118140960795 + 3842339 * 2 ^ 59
def prefixEnd_3842339 : Nat := 4983230072969 + 3 ^ 40 * 3842339 * 2
def baseEnd_3842339 : Nat := 1972966744515947564691911

theorem tailTrace_3842339 : CollatzResearch.WordTrace tailWord_3842339 prefixEnd_3842339 1972966744515947564691911 := by
  unfold tailWord_3842339
  simp only [CollatzResearch.WordTrace]
  refine ⟨140141616426869497102026071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93427744284579664734684047 140141616426869497102026071)
  ·
    refine ⟨210212424640304245653039107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140141616426869497102026071 210212424640304245653039107)
    ·
      refine ⟨315318636960456368479558661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210212424640304245653039107 315318636960456368479558661)
      ·
        refine ⟨59122244430085569089917249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315318636960456368479558661 59122244430085569089917249)
        ·
          refine ⟨44341683322564176817437937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59122244430085569089917249 44341683322564176817437937)
          ·
            refine ⟨33256262491923132613078453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44341683322564176817437937 33256262491923132613078453)
            ·
              refine ⟨3117774608617793682476105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33256262491923132613078453 3117774608617793682476105)
              ·
                refine ⟨2338330956463345261857079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3117774608617793682476105 2338330956463345261857079)
                ·
                  refine ⟨3507496434695017892785619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338330956463345261857079 3507496434695017892785619)
                  ·
                    refine ⟨5261244652042526839178429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507496434695017892785619 5261244652042526839178429)
                    ·
                      refine ⟨1972966744515947564691911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5261244652042526839178429 1972966744515947564691911)
                      ·
                        rfl

theorem cell23_3842339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_3842339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842339 prefixEnd_3842339 := by exact prefixLift 3842339
  have htrace : WordTrace (prefixWord ++ tailWord_3842339) baseStart_3842339 baseEnd_3842339 := by
    simpa [prefixWord, tailWord_3842339, baseEnd_3842339] using wordTrace_append hprefix tailTrace_3842339
  have hstable : (prefixWord ++ tailWord_3842339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842339).length < 2 ^ (prefixWord ++ tailWord_3842339).sum := by decide
  have hdescent : baseEnd_3842339 < baseStart_3842339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842348 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_3842348 : Nat := 118140960795 + 3842348 * 2 ^ 59
def prefixEnd_3842348 : Nat := 4983230072969 + 3 ^ 40 * 3842348 * 2
def baseEnd_3842348 : Nat := 1972971365841838029479369

theorem tailTrace_3842348 : CollatzResearch.WordTrace tailWord_3842348 prefixEnd_3842348 1972971365841838029479369 := by
  unfold tailWord_3842348
  simp only [CollatzResearch.WordTrace]
  refine ⟨70070972341918445819551849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93427963122557927759402465 70070972341918445819551849)
  ·
    refine ⟨52553229256438834364663887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70070972341918445819551849 52553229256438834364663887)
    ·
      refine ⟨78829843884658251546995831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52553229256438834364663887 78829843884658251546995831)
      ·
        refine ⟨118244765826987377320493747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78829843884658251546995831 118244765826987377320493747)
        ·
          refine ⟨177367148740481065980740621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118244765826987377320493747 177367148740481065980740621)
          ·
            refine ⟨66512680777680399742777733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177367148740481065980740621 66512680777680399742777733)
            ·
              refine ⟨12471127645815074951770825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66512680777680399742777733 12471127645815074951770825)
              ·
                refine ⟨9353345734361306213828119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12471127645815074951770825 9353345734361306213828119)
                ·
                  refine ⟨14030018601541959320742179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353345734361306213828119 14030018601541959320742179)
                  ·
                    refine ⟨21045027902312938981113269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14030018601541959320742179 21045027902312938981113269)
                    ·
                      refine ⟨1972971365841838029479369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21045027902312938981113269 1972971365841838029479369)
                      ·
                        rfl

theorem cell23_3842348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_3842348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842348 prefixEnd_3842348 := by exact prefixLift 3842348
  have htrace : WordTrace (prefixWord ++ tailWord_3842348) baseStart_3842348 baseEnd_3842348 := by
    simpa [prefixWord, tailWord_3842348, baseEnd_3842348] using wordTrace_append hprefix tailTrace_3842348
  have hstable : (prefixWord ++ tailWord_3842348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842348).length < 2 ^ (prefixWord ++ tailWord_3842348).sum := by decide
  have hdescent : baseEnd_3842348 < baseStart_3842348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842351 : List Nat := [1, 1, 2, 1, 2, 1, 5, 10]
def baseStart_3842351 : Nat := 118140960795 + 3842351 * 2 ^ 59
def prefixEnd_3842351 : Nat := 4983230072969 + 3 ^ 40 * 3842351 * 2
def baseEnd_3842351 : Nat := 73073070603103759916365

theorem tailTrace_3842351 : CollatzResearch.WordTrace tailWord_3842351 prefixEnd_3842351 73073070603103759916365 := by
  unfold tailWord_3842351
  simp only [CollatzResearch.WordTrace]
  refine ⟨140142054102826023151462907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93428036068550682100975271 140142054102826023151462907)
  ·
    refine ⟨210213081154239034727194361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140142054102826023151462907 210213081154239034727194361)
    ·
      refine ⟨157659810865679276045395771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210213081154239034727194361 157659810865679276045395771)
      ·
        refine ⟨236489716298518914068093657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157659810865679276045395771 236489716298518914068093657)
        ·
          refine ⟨177367287223889185551070243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236489716298518914068093657 177367287223889185551070243)
          ·
            refine ⟨266050930835833778326605365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177367287223889185551070243 266050930835833778326605365)
            ·
              refine ⟨24942274765859416718119253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266050930835833778326605365 24942274765859416718119253)
              ·
                refine ⟨73073070603103759916365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24942274765859416718119253 73073070603103759916365)
                ·
                  rfl

theorem cell23_3842351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 10].length) (baseStart_3842351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842351 prefixEnd_3842351 := by exact prefixLift 3842351
  have htrace : WordTrace (prefixWord ++ tailWord_3842351) baseStart_3842351 baseEnd_3842351 := by
    simpa [prefixWord, tailWord_3842351, baseEnd_3842351] using wordTrace_append hprefix tailTrace_3842351
  have hstable : (prefixWord ++ tailWord_3842351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842351).length < 2 ^ (prefixWord ++ tailWord_3842351).sum := by decide
  have hdescent : baseEnd_3842351 < baseStart_3842351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842355 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 2, 4]
def baseStart_3842355 : Nat := 118140960795 + 3842355 * 2 ^ 59
def prefixEnd_3842355 : Nat := 4983230072969 + 3 ^ 40 * 3842355 * 2
def baseEnd_3842355 : Nat := 657658320068806500697279

theorem tailTrace_3842355 : CollatzResearch.WordTrace tailWord_3842355 prefixEnd_3842355 657658320068806500697279 := by
  unfold tailWord_3842355
  simp only [CollatzResearch.WordTrace]
  refine ⟨140142199994811531834608519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93428133329874354556405679 140142199994811531834608519)
  ·
    refine ⟨210213299992217297751912779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140142199994811531834608519 210213299992217297751912779)
    ·
      refine ⟨315319949988325946627869169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210213299992217297751912779 315319949988325946627869169)
      ·
        refine ⟨236489962491244459970901877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315319949988325946627869169 236489962491244459970901877)
        ·
          refine ⟨22170933983554168122272051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236489962491244459970901877 22170933983554168122272051)
          ·
            refine ⟨33256400975331252183408077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22170933983554168122272051 33256400975331252183408077)
            ·
              refine ⟨12471150365749219568778029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33256400975331252183408077 12471150365749219568778029)
              ·
                refine ⟨4676681387155957338291761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12471150365749219568778029 4676681387155957338291761)
                ·
                  refine ⟨3507511040366968003718821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4676681387155957338291761 3507511040366968003718821)
                  ·
                    refine ⟨657658320068806500697279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3507511040366968003718821 657658320068806500697279)
                    ·
                      rfl

theorem cell23_3842355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 4].length) (baseStart_3842355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842355 prefixEnd_3842355 := by exact prefixLift 3842355
  have htrace : WordTrace (prefixWord ++ tailWord_3842355) baseStart_3842355 baseEnd_3842355 := by
    simpa [prefixWord, tailWord_3842355, baseEnd_3842355] using wordTrace_append hprefix tailTrace_3842355
  have hstable : (prefixWord ++ tailWord_3842355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842355).length < 2 ^ (prefixWord ++ tailWord_3842355).sum := by decide
  have hdescent : baseEnd_3842355 < baseStart_3842355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842362 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_3842362 : Nat := 118140960795 + 3842362 * 2 ^ 59
def prefixEnd_3842362 : Nat := 4983230072969 + 3 ^ 40 * 3842362 * 2
def baseEnd_3842362 : Nat := 1972978554571000974704305

theorem tailTrace_3842362 : CollatzResearch.WordTrace tailWord_3842362 prefixEnd_3842362 1972978554571000974704305 := by
  unfold tailWord_3842362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35035613826446543007528335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93428303537190781353408893 35035613826446543007528335)
  ·
    refine ⟨52553420739669814511292503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35035613826446543007528335 52553420739669814511292503)
    ·
      refine ⟨78830131109504721766938755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52553420739669814511292503 78830131109504721766938755)
      ·
        refine ⟨118245196664257082650408133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78830131109504721766938755 118245196664257082650408133)
        ·
          refine ⟨22170974374548202996951525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118245196664257082650408133 22170974374548202996951525)
          ·
            refine ⟨4157057695227788061928411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22170974374548202996951525 4157057695227788061928411)
            ·
              refine ⟨6235586542841682092892617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157057695227788061928411 6235586542841682092892617)
              ·
                refine ⟨4676689907131261569669463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6235586542841682092892617 4676689907131261569669463)
                ·
                  refine ⟨7015034860696892354504195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676689907131261569669463 7015034860696892354504195)
                  ·
                    refine ⟨10522552291045338531756293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7015034860696892354504195 10522552291045338531756293)
                    ·
                      refine ⟨1972978554571000974704305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10522552291045338531756293 1972978554571000974704305)
                      ·
                        rfl

theorem cell23_3842362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_3842362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842362 prefixEnd_3842362 := by exact prefixLift 3842362
  have htrace : WordTrace (prefixWord ++ tailWord_3842362) baseStart_3842362 baseEnd_3842362 := by
    simpa [prefixWord, tailWord_3842362, baseEnd_3842362] using wordTrace_append hprefix tailTrace_3842362
  have hstable : (prefixWord ++ tailWord_3842362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842362).length < 2 ^ (prefixWord ++ tailWord_3842362).sum := by decide
  have hdescent : baseEnd_3842362 < baseStart_3842362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842372 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3842372 : Nat := 118140960795 + 3842372 * 2 ^ 59
def prefixEnd_3842372 : Nat := 4983230072969 + 3 ^ 40 * 3842372 * 2
def baseEnd_3842372 : Nat := 657661229792515311859753

theorem tailTrace_3842372 : CollatzResearch.WordTrace tailWord_3842372 prefixEnd_3842372 657661229792515311859753 := by
  unfold tailWord_3842372
  simp only [CollatzResearch.WordTrace]
  refine ⟨70071410017874971868988685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93428546690499962491984913 70071410017874971868988685)
  ·
    refine ⟨26276778756703114450870757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70071410017874971868988685 26276778756703114450870757)
    ·
      refine ⟨4926896016881833959538267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26276778756703114450870757 4926896016881833959538267)
      ·
        refine ⟨7390344025322750939307401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926896016881833959538267 7390344025322750939307401)
        ·
          refine ⟨5542758018992063204480551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7390344025322750939307401 5542758018992063204480551)
          ·
            refine ⟨8314137028488094806720827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542758018992063204480551 8314137028488094806720827)
            ·
              refine ⟨12471205542732142210081241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314137028488094806720827 12471205542732142210081241)
              ·
                refine ⟨9353404157049106657560931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12471205542732142210081241 9353404157049106657560931)
                ·
                  refine ⟨14030106235573659986341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353404157049106657560931 14030106235573659986341397)
                  ·
                    refine ⟨657661229792515311859753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14030106235573659986341397 657661229792515311859753)
                    ·
                      rfl

theorem cell23_3842372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3842372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842372 prefixEnd_3842372 := by exact prefixLift 3842372
  have htrace : WordTrace (prefixWord ++ tailWord_3842372) baseStart_3842372 baseEnd_3842372 := by
    simpa [prefixWord, tailWord_3842372, baseEnd_3842372] using wordTrace_append hprefix tailTrace_3842372
  have hstable : (prefixWord ++ tailWord_3842372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842372).length < 2 ^ (prefixWord ++ tailWord_3842372).sum := by decide
  have hdescent : baseEnd_3842372 < baseStart_3842372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842412 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_3842412 : Nat := 118140960795 + 3842412 * 2 ^ 59
def prefixEnd_3842412 : Nat := 4983230072969 + 3 ^ 40 * 3842412 * 2
def baseEnd_3842412 : Nat := 1973004228603725779079075

theorem tailTrace_3842412 : CollatzResearch.WordTrace tailWord_3842412 prefixEnd_3842412 1973004228603725779079075 := by
  unfold tailWord_3842412
  simp only [CollatzResearch.WordTrace]
  refine ⟨70072139477802515284716745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93429519303736687046288993 70072139477802515284716745)
  ·
    refine ⟨52554104608351886463537559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70072139477802515284716745 52554104608351886463537559)
    ·
      refine ⟨78831156912527829695306339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52554104608351886463537559 78831156912527829695306339)
      ·
        refine ⟨118246735368791744542959509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78831156912527829695306339 118246735368791744542959509)
        ·
          refine ⟨5542815720412113025451227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118246735368791744542959509 5542815720412113025451227)
          ·
            refine ⟨8314223580618169538176841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542815720412113025451227 8314223580618169538176841)
            ·
              refine ⟨6235667685463627153632631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314223580618169538176841 6235667685463627153632631)
              ·
                refine ⟨9353501528195440730448947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6235667685463627153632631 9353501528195440730448947)
                ·
                  refine ⟨14030252292293161095673421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9353501528195440730448947 14030252292293161095673421)
                  ·
                    refine ⟨5261344609609935410877533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14030252292293161095673421 5261344609609935410877533)
                    ·
                      refine ⟨1973004228603725779079075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5261344609609935410877533 1973004228603725779079075)
                      ·
                        rfl

theorem cell23_3842412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_3842412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842412 prefixEnd_3842412 := by exact prefixLift 3842412
  have htrace : WordTrace (prefixWord ++ tailWord_3842412) baseStart_3842412 baseEnd_3842412 := by
    simpa [prefixWord, tailWord_3842412, baseEnd_3842412] using wordTrace_append hprefix tailTrace_3842412
  have hstable : (prefixWord ++ tailWord_3842412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842412).length < 2 ^ (prefixWord ++ tailWord_3842412).sum := by decide
  have hdescent : baseEnd_3842412 < baseStart_3842412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842446 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3842446 : Nat := 118140960795 + 3842446 * 2 ^ 59
def prefixEnd_3842446 : Nat := 4983230072969 + 3 ^ 40 * 3842446 * 2
def baseEnd_3842446 : Nat := 1973021686945978646053919

theorem tailTrace_3842446 : CollatzResearch.WordTrace tailWord_3842446 prefixEnd_3842446 1973021686945978646053919 := by
  unfold tailWord_3842446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518189879685231797021399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93430346024987902917447461 17518189879685231797021399)
  ·
    refine ⟨26277284819527847695532099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17518189879685231797021399 26277284819527847695532099)
    ·
      refine ⟨39415927229291771543298149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26277284819527847695532099 39415927229291771543298149)
      ·
        refine ⟨7390486355492207164368403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39415927229291771543298149 7390486355492207164368403)
        ·
          refine ⟨11085729533238310746552605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390486355492207164368403 11085729533238310746552605)
          ·
            refine ⟨4157148574964366529957227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11085729533238310746552605 4157148574964366529957227)
            ·
              refine ⟨6235722862446549794935841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157148574964366529957227 6235722862446549794935841)
              ·
                refine ⟨4676792146834912346201881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6235722862446549794935841 4676792146834912346201881)
                ·
                  refine ⟨3507594110126184259651411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4676792146834912346201881 3507594110126184259651411)
                  ·
                    refine ⟨5261391165189276389477117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507594110126184259651411 5261391165189276389477117)
                    ·
                      refine ⟨1973021686945978646053919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5261391165189276389477117 1973021686945978646053919)
                      ·
                        rfl

theorem cell23_3842446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3842446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842446 prefixEnd_3842446 := by exact prefixLift 3842446
  have htrace : WordTrace (prefixWord ++ tailWord_3842446) baseStart_3842446 baseEnd_3842446 := by
    simpa [prefixWord, tailWord_3842446, baseEnd_3842446] using wordTrace_append hprefix tailTrace_3842446
  have hstable : (prefixWord ++ tailWord_3842446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842446).length < 2 ^ (prefixWord ++ tailWord_3842446).sum := by decide
  have hdescent : baseEnd_3842446 < baseStart_3842446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842462 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3842462 : Nat := 118140960795 + 3842462 * 2 ^ 59
def prefixEnd_3842462 : Nat := 4983230072969 + 3 ^ 40 * 3842462 * 2
def baseEnd_3842462 : Nat := 657676634212150194484615

theorem tailTrace_3842462 : CollatzResearch.WordTrace tailWord_3842462 prefixEnd_3842462 657676634212150194484615 := by
  unfold tailWord_3842462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518262825677986138594205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93430735070282592739169093 17518262825677986138594205)
  ·
    refine ⟨6569348559629244801972827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17518262825677986138594205 6569348559629244801972827)
    ·
      refine ⟨9854022839443867202959241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6569348559629244801972827 9854022839443867202959241)
      ·
        refine ⟨7390517129582900402219431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9854022839443867202959241 7390517129582900402219431)
        ·
          refine ⟨11085775694374350603329147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390517129582900402219431 11085775694374350603329147)
          ·
            refine ⟨16628663541561525904993721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11085775694374350603329147 16628663541561525904993721)
            ·
              refine ⟨12471497656171144428745291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16628663541561525904993721 12471497656171144428745291)
              ·
                refine ⟨18707246484256716643117937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471497656171144428745291 18707246484256716643117937)
                ·
                  refine ⟨14030434863192537482338453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18707246484256716643117937 14030434863192537482338453)
                  ·
                    refine ⟨657676634212150194484615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14030434863192537482338453 657676634212150194484615)
                    ·
                      rfl

theorem cell23_3842462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3842462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842462 prefixEnd_3842462 := by exact prefixLift 3842462
  have htrace : WordTrace (prefixWord ++ tailWord_3842462) baseStart_3842462 baseEnd_3842462 := by
    simpa [prefixWord, tailWord_3842462, baseEnd_3842462] using wordTrace_append hprefix tailTrace_3842462
  have hstable : (prefixWord ++ tailWord_3842462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842462).length < 2 ^ (prefixWord ++ tailWord_3842462).sum := by decide
  have hdescent : baseEnd_3842462 < baseStart_3842462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842495 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 7, 2]
def baseStart_3842495 : Nat := 118140960795 + 3842495 * 2 ^ 59
def prefixEnd_3842495 : Nat := 4983230072969 + 3 ^ 40 * 3842495 * 2
def baseEnd_3842495 : Nat := 1973046847498048954341193

theorem tailTrace_3842495 : CollatzResearch.WordTrace tailWord_3842495 prefixEnd_3842495 1973046847498048954341193 := by
  unfold tailWord_3842495
  simp only [CollatzResearch.WordTrace]
  refine ⟨140147306214304335744704939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93431537476202890496469959 140147306214304335744704939)
  ·
    refine ⟨210220959321456503617057409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140147306214304335744704939 210220959321456503617057409)
    ·
      refine ⟨157665719491092377712793057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210220959321456503617057409 157665719491092377712793057)
      ·
        refine ⟨118249289618319283284594793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157665719491092377712793057 118249289618319283284594793)
        ·
          refine ⟨88686967213739462463446095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118249289618319283284594793 88686967213739462463446095)
          ·
            refine ⟨133030450820609193695169143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88686967213739462463446095 133030450820609193695169143)
            ·
              refine ⟨199545676230913790542753715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133030450820609193695169143 199545676230913790542753715)
              ·
                refine ⟨299318514346370685814130573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199545676230913790542753715 299318514346370685814130573)
                ·
                  refine ⟨112244442879889007180298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299318514346370685814130573 112244442879889007180298965)
                  ·
                    refine ⟨2630729129997398605788257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 112244442879889007180298965 2630729129997398605788257)
                    ·
                      refine ⟨1973046847498048954341193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630729129997398605788257 1973046847498048954341193)
                      ·
                        rfl

theorem cell23_3842495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_3842495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842495 prefixEnd_3842495 := by exact prefixLift 3842495
  have htrace : WordTrace (prefixWord ++ tailWord_3842495) baseStart_3842495 baseEnd_3842495 := by
    simpa [prefixWord, tailWord_3842495, baseEnd_3842495] using wordTrace_append hprefix tailTrace_3842495
  have hstable : (prefixWord ++ tailWord_3842495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842495).length < 2 ^ (prefixWord ++ tailWord_3842495).sum := by decide
  have hdescent : baseEnd_3842495 < baseStart_3842495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842542 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3842542 : Nat := 118140960795 + 3842542 * 2 ^ 59
def prefixEnd_3842542 : Nat := 4983230072969 + 3 ^ 40 * 3842542 * 2
def baseEnd_3842542 : Nat := 1973070981088810270453477

theorem tailTrace_3842542 : CollatzResearch.WordTrace tailWord_3842542 prefixEnd_3842542 1973070981088810270453477 := by
  unfold tailWord_3842542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518627555641757846458235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93432680296756041847777253 17518627555641757846458235)
  ·
    refine ⟨26277941333462636769687353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17518627555641757846458235 26277941333462636769687353)
    ·
      refine ⟨19708456000096977577265515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26277941333462636769687353 19708456000096977577265515)
      ·
        refine ⟨29562684000145466365898273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19708456000096977577265515 29562684000145466365898273)
        ·
          refine ⟨22172013000109099774423705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29562684000145466365898273 22172013000109099774423705)
          ·
            refine ⟨16629009750081824830817779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22172013000109099774423705 16629009750081824830817779)
            ·
              refine ⟨24943514625122737246226669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629009750081824830817779 24943514625122737246226669)
              ·
                refine ⟨9353817984421026467335001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24943514625122737246226669 9353817984421026467335001)
                ·
                  refine ⟨7015363488315769850501251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9353817984421026467335001 7015363488315769850501251)
                  ·
                    refine ⟨10523045232473654775751877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7015363488315769850501251 10523045232473654775751877)
                    ·
                      refine ⟨1973070981088810270453477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10523045232473654775751877 1973070981088810270453477)
                      ·
                        rfl

theorem cell23_3842542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3842542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842542 prefixEnd_3842542 := by exact prefixLift 3842542
  have htrace : WordTrace (prefixWord ++ tailWord_3842542) baseStart_3842542 baseEnd_3842542 := by
    simpa [prefixWord, tailWord_3842542, baseEnd_3842542] using wordTrace_append hprefix tailTrace_3842542
  have hstable : (prefixWord ++ tailWord_3842542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842542).length < 2 ^ (prefixWord ++ tailWord_3842542).sum := by decide
  have hdescent : baseEnd_3842542 < baseStart_3842542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842565 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 6]
def baseStart_3842565 : Nat := 118140960795 + 3842565 * 2 ^ 59
def prefixEnd_3842565 : Nat := 4983230072969 + 3 ^ 40 * 3842565 * 2
def baseEnd_3842565 : Nat := 219231421238207075607319

theorem tailTrace_3842565 : CollatzResearch.WordTrace tailWord_3842565 prefixEnd_3842565 219231421238207075607319 := by
  unfold tailWord_3842565
  simp only [CollatzResearch.WordTrace]
  refine ⟨140149859324050737699753149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93433239549367158466502099 140149859324050737699753149)
  ·
    refine ⟨52556197246519026637407431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140149859324050737699753149 52556197246519026637407431)
    ·
      refine ⟨78834295869778539956111147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52556197246519026637407431 78834295869778539956111147)
      ·
        refine ⟨118251443804667809934166721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78834295869778539956111147 118251443804667809934166721)
        ·
          refine ⟨88688582853500857450625041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118251443804667809934166721 88688582853500857450625041)
          ·
            refine ⟨66516437140125643087968781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88688582853500857450625041 66516437140125643087968781)
            ·
              refine ⟨24943663927547116157988293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66516437140125643087968781 24943663927547116157988293)
              ·
                refine ⟨4676936986415084279622805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24943663927547116157988293 4676936986415084279622805)
                ·
                  refine ⟨219231421238207075607319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4676936986415084279622805 219231421238207075607319)
                  ·
                    rfl

theorem cell23_3842565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_3842565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842565 prefixEnd_3842565 := by exact prefixLift 3842565
  have htrace : WordTrace (prefixWord ++ tailWord_3842565) baseStart_3842565 baseEnd_3842565 := by
    simpa [prefixWord, tailWord_3842565, baseEnd_3842565] using wordTrace_append hprefix tailTrace_3842565
  have hstable : (prefixWord ++ tailWord_3842565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842565).length < 2 ^ (prefixWord ++ tailWord_3842565).sum := by decide
  have hdescent : baseEnd_3842565 < baseStart_3842565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842566 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3842566 : Nat := 118140960795 + 3842566 * 2 ^ 59
def prefixEnd_3842566 : Nat := 4983230072969 + 3 ^ 40 * 3842566 * 2
def baseEnd_3842566 : Nat := 1973083304624518176553367

theorem tailTrace_3842566 : CollatzResearch.WordTrace tailWord_3842566 prefixEnd_3842566 1973083304624518176553367 := by
  unfold tailWord_3842566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379684243657722339704361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93433263864698076580359701 4379684243657722339704361)
  ·
    refine ⟨3284763182743291754778271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4379684243657722339704361 3284763182743291754778271)
    ·
      refine ⟨4927144774114937632167407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284763182743291754778271 4927144774114937632167407)
      ·
        refine ⟨7390717161172406448251111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927144774114937632167407 7390717161172406448251111)
        ·
          refine ⟨11086075741758609672376667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390717161172406448251111 11086075741758609672376667)
          ·
            refine ⟨16629113612637914508565001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086075741758609672376667 16629113612637914508565001)
            ·
              refine ⟨12471835209478435881423751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16629113612637914508565001 12471835209478435881423751)
              ·
                refine ⟨18707752814217653822135627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12471835209478435881423751 18707752814217653822135627)
                ·
                  refine ⟨28061629221326480733203441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18707752814217653822135627 28061629221326480733203441)
                  ·
                    refine ⟨21046221915994860549902581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28061629221326480733203441 21046221915994860549902581)
                    ·
                      refine ⟨1973083304624518176553367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21046221915994860549902581 1973083304624518176553367)
                      ·
                        rfl

theorem cell23_3842566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3842566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842566 prefixEnd_3842566 := by exact prefixLift 3842566
  have htrace : WordTrace (prefixWord ++ tailWord_3842566) baseStart_3842566 baseEnd_3842566 := by
    simpa [prefixWord, tailWord_3842566, baseEnd_3842566] using wordTrace_append hprefix tailTrace_3842566
  have hstable : (prefixWord ++ tailWord_3842566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842566).length < 2 ^ (prefixWord ++ tailWord_3842566).sum := by decide
  have hdescent : baseEnd_3842566 < baseStart_3842566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842635 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_3842635 : Nat := 118140960795 + 3842635 * 2 ^ 59
def prefixEnd_3842635 : Nat := 4983230072969 + 3 ^ 40 * 3842635 * 2
def baseEnd_3842635 : Nat := 1973118734789678406590549

theorem tailTrace_3842635 : CollatzResearch.WordTrace tailWord_3842635 prefixEnd_3842635 1973118734789678406590549 := by
  unfold tailWord_3842635
  simp only [CollatzResearch.WordTrace]
  refine ⟨140152412433797139654801359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93434941622531426436534239 140152412433797139654801359)
  ·
    refine ⟨210228618650695709482202039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140152412433797139654801359 210228618650695709482202039)
    ·
      refine ⟨315342927976043564223303059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210228618650695709482202039 315342927976043564223303059)
      ·
        refine ⟨473014391964065346334954589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315342927976043564223303059 473014391964065346334954589)
        ·
          refine ⟨177380396986524504875607971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473014391964065346334954589 177380396986524504875607971)
          ·
            refine ⟨266070595479786757313411957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177380396986524504875607971 266070595479786757313411957)
            ·
              refine ⟨24944118326230008498132371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266070595479786757313411957 24944118326230008498132371)
              ·
                refine ⟨37416177489345012747198557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24944118326230008498132371 37416177489345012747198557)
                ·
                  refine ⟨14031066558504379780199459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37416177489345012747198557 14031066558504379780199459)
                  ·
                    refine ⟨21046599837756569670299189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14031066558504379780199459 21046599837756569670299189)
                    ·
                      refine ⟨1973118734789678406590549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21046599837756569670299189 1973118734789678406590549)
                      ·
                        rfl

theorem cell23_3842635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_3842635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842635 prefixEnd_3842635 := by exact prefixLift 3842635
  have htrace : WordTrace (prefixWord ++ tailWord_3842635) baseStart_3842635 baseEnd_3842635 := by
    simpa [prefixWord, tailWord_3842635, baseEnd_3842635] using wordTrace_append hprefix tailTrace_3842635
  have hstable : (prefixWord ++ tailWord_3842635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842635).length < 2 ^ (prefixWord ++ tailWord_3842635).sum := by decide
  have hdescent : baseEnd_3842635 < baseStart_3842635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842654 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3842654 : Nat := 118140960795 + 3842654 * 2 ^ 59
def prefixEnd_3842654 : Nat := 4983230072969 + 3 ^ 40 * 3842654 * 2
def baseEnd_3842654 : Nat := 657709496974037944084321

theorem tailTrace_3842654 : CollatzResearch.WordTrace tailWord_3842654 prefixEnd_3842654 657709496974037944084321 := by
  unfold tailWord_3842654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519138177591038237467877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93435403613818870599828677 17519138177591038237467877)
  ·
    refine ⟨3284838408298319669525227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17519138177591038237467877 3284838408298319669525227)
    ·
      refine ⟨4927257612447479504287841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284838408298319669525227 4927257612447479504287841)
      ·
        refine ⟨3695443209335609628215881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927257612447479504287841 3695443209335609628215881)
        ·
          refine ⟨2771582407001707221161911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3695443209335609628215881 2771582407001707221161911)
          ·
            refine ⟨4157373610502560831742867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771582407001707221161911 4157373610502560831742867)
            ·
              refine ⟨6236060415753841247614301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157373610502560831742867 6236060415753841247614301)
              ·
                refine ⟨2338522655907690467855363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6236060415753841247614301 2338522655907690467855363)
                ·
                  refine ⟨3507783983861535701783045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338522655907690467855363 3507783983861535701783045)
                  ·
                    refine ⟨657709496974037944084321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3507783983861535701783045 657709496974037944084321)
                    ·
                      rfl

theorem cell23_3842654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3842654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842654 prefixEnd_3842654 := by exact prefixLift 3842654
  have htrace : WordTrace (prefixWord ++ tailWord_3842654) baseStart_3842654 baseEnd_3842654 := by
    simpa [prefixWord, tailWord_3842654, baseEnd_3842654] using wordTrace_append hprefix tailTrace_3842654
  have hstable : (prefixWord ++ tailWord_3842654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842654).length < 2 ^ (prefixWord ++ tailWord_3842654).sum := by decide
  have hdescent : baseEnd_3842654 < baseStart_3842654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842669 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3842669 : Nat := 118140960795 + 3842669 * 2 ^ 59
def prefixEnd_3842669 : Nat := 4983230072969 + 3 ^ 40 * 3842669 * 2
def baseEnd_3842669 : Nat := 1973136193131931273565393

theorem tailTrace_3842669 : CollatzResearch.WordTrace tailWord_3842669 prefixEnd_3842669 1973136193131931273565393 := by
  unfold tailWord_3842669
  simp only [CollatzResearch.WordTrace]
  refine ⟨140153652515673963461539061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93435768343782642307692707 140153652515673963461539061)
  ·
    refine ⟨13139404923344434074519287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140153652515673963461539061 13139404923344434074519287)
    ·
      refine ⟨19709107385016651111778931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13139404923344434074519287 19709107385016651111778931)
      ·
        refine ⟨29563661077524976667668397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19709107385016651111778931 29563661077524976667668397)
        ·
          refine ⟨11086372904071866250375649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29563661077524976667668397 11086372904071866250375649)
          ·
            refine ⟨8314779678053899687781737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11086372904071866250375649 8314779678053899687781737)
            ·
              refine ⟨6236084758540424765836303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314779678053899687781737 6236084758540424765836303)
              ·
                refine ⟨9354127137810637148754455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236084758540424765836303 9354127137810637148754455)
                ·
                  refine ⟨14031190706715955723131683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9354127137810637148754455 14031190706715955723131683)
                  ·
                    refine ⟨21046786060073933584697525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14031190706715955723131683 21046786060073933584697525)
                    ·
                      refine ⟨1973136193131931273565393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21046786060073933584697525 1973136193131931273565393)
                      ·
                        rfl

theorem cell23_3842669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3842669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842669 prefixEnd_3842669 := by exact prefixLift 3842669
  have htrace : WordTrace (prefixWord ++ tailWord_3842669) baseStart_3842669 baseEnd_3842669 := by
    simpa [prefixWord, tailWord_3842669, baseEnd_3842669] using wordTrace_append hprefix tailTrace_3842669
  have hstable : (prefixWord ++ tailWord_3842669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842669).length < 2 ^ (prefixWord ++ tailWord_3842669).sum := by decide
  have hdescent : baseEnd_3842669 < baseStart_3842669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842672 : List Nat := [2, 1, 1, 1, 7, 2, 9]
def baseStart_3842672 : Nat := 118140960795 + 3842672 * 2 ^ 59
def prefixEnd_3842672 : Nat := 4983230072969 + 3 ^ 40 * 3842672 * 2
def baseEnd_3842672 : Nat := 24359725105850552615159

theorem tailTrace_3842672 : CollatzResearch.WordTrace tailWord_3842672 prefixEnd_3842672 24359725105850552615159 := by
  unfold tailWord_3842672
  simp only [CollatzResearch.WordTrace]
  refine ⟨70076880967331547486949135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93435841289775396649265513 70076880967331547486949135)
  ·
    refine ⟨105115321450997321230423703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70076880967331547486949135 105115321450997321230423703)
    ·
      refine ⟨157672982176495981845635555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105115321450997321230423703 157672982176495981845635555)
      ·
        refine ⟨236509473264743972768453333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157672982176495981845635555 236509473264743972768453333)
        ·
          refine ⟨5543190779642436861760625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 236509473264743972768453333 5543190779642436861760625)
          ·
            refine ⟨4157393084731827646320469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543190779642436861760625 4157393084731827646320469)
            ·
              refine ⟨24359725105850552615159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4157393084731827646320469 24359725105850552615159)
              ·
                rfl

theorem cell23_3842672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 9].length) (baseStart_3842672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842672 prefixEnd_3842672 := by exact prefixLift 3842672
  have htrace : WordTrace (prefixWord ++ tailWord_3842672) baseStart_3842672 baseEnd_3842672 := by
    simpa [prefixWord, tailWord_3842672, baseEnd_3842672] using wordTrace_append hprefix tailTrace_3842672
  have hstable : (prefixWord ++ tailWord_3842672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842672).length < 2 ^ (prefixWord ++ tailWord_3842672).sum := by decide
  have hdescent : baseEnd_3842672 < baseStart_3842672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842733 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_3842733 : Nat := 118140960795 + 3842733 * 2 ^ 59
def prefixEnd_3842733 : Nat := 4983230072969 + 3 ^ 40 * 3842733 * 2
def baseEnd_3842733 : Nat := 1973169055893819023165099

theorem tailTrace_3842733 : CollatzResearch.WordTrace tailWord_3842733 prefixEnd_3842733 1973169055893819023165099 := by
  unfold tailWord_3842733
  simp only [CollatzResearch.WordTrace]
  refine ⟨140155986787442102391868853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93437324524961401594579235 140155986787442102391868853)
  ·
    refine ⟨13139623761322697099237705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140155986787442102391868853 13139623761322697099237705)
    ·
      refine ⟨9854717820992022824428279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13139623761322697099237705 9854717820992022824428279)
      ·
        refine ⟨14782076731488034236642419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9854717820992022824428279 14782076731488034236642419)
        ·
          refine ⟨22173115097232051354963629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14782076731488034236642419 22173115097232051354963629)
          ·
            refine ⟨8314918161462019258111361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22173115097232051354963629 8314918161462019258111361)
            ·
              refine ⟨6236188621096514443583521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8314918161462019258111361 6236188621096514443583521)
              ·
                refine ⟨4677141465822385832687641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236188621096514443583521 4677141465822385832687641)
                ·
                  refine ⟨3507856099366789374515731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677141465822385832687641 3507856099366789374515731)
                  ·
                    refine ⟨5261784149050184061773597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507856099366789374515731 5261784149050184061773597)
                    ·
                      refine ⟨1973169055893819023165099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5261784149050184061773597 1973169055893819023165099)
                      ·
                        rfl

theorem cell23_3842733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_3842733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842733 prefixEnd_3842733 := by exact prefixLift 3842733
  have htrace : WordTrace (prefixWord ++ tailWord_3842733) baseStart_3842733 baseEnd_3842733 := by
    simpa [prefixWord, tailWord_3842733, baseEnd_3842733] using wordTrace_append hprefix tailTrace_3842733
  have hstable : (prefixWord ++ tailWord_3842733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842733).length < 2 ^ (prefixWord ++ tailWord_3842733).sum := by decide
  have hdescent : baseEnd_3842733 < baseStart_3842733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842734 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3842734 : Nat := 118140960795 + 3842734 * 2 ^ 59
def prefixEnd_3842734 : Nat := 4983230072969 + 3 ^ 40 * 3842734 * 2
def baseEnd_3842734 : Nat := 1973169569374473519252595

theorem tailTrace_3842734 : CollatzResearch.WordTrace tailWord_3842734 prefixEnd_3842734 1973169569374473519252595 := by
  unfold tailWord_3842734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519502907554809945331907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93437348840292319708436837 17519502907554809945331907)
  ·
    refine ⟨26279254361332214917997861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17519502907554809945331907 26279254361332214917997861)
    ·
      refine ⟨4927360192749790297124599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26279254361332214917997861 4927360192749790297124599)
      ·
        refine ⟨7391040289124685445686899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927360192749790297124599 7391040289124685445686899)
        ·
          refine ⟨11086560433687028168530349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391040289124685445686899 11086560433687028168530349)
          ·
            refine ⟨4157460162632635563198881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11086560433687028168530349 4157460162632635563198881)
            ·
              refine ⟨3118095121974476672399161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157460162632635563198881 3118095121974476672399161)
              ·
                refine ⟨2338571341480857504299371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118095121974476672399161 2338571341480857504299371)
                ·
                  refine ⟨3507857012221286256449057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338571341480857504299371 3507857012221286256449057)
                  ·
                    refine ⟨2630892759165964692336793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3507857012221286256449057 2630892759165964692336793)
                    ·
                      refine ⟨1973169569374473519252595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630892759165964692336793 1973169569374473519252595)
                      ·
                        rfl

theorem cell23_3842734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3842734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842734 prefixEnd_3842734 := by exact prefixLift 3842734
  have htrace : WordTrace (prefixWord ++ tailWord_3842734) baseStart_3842734 baseEnd_3842734 := by
    simpa [prefixWord, tailWord_3842734, baseEnd_3842734] using wordTrace_append hprefix tailTrace_3842734
  have hstable : (prefixWord ++ tailWord_3842734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842734).length < 2 ^ (prefixWord ++ tailWord_3842734).sum := by decide
  have hdescent : baseEnd_3842734 < baseStart_3842734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842752 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_3842752 : Nat := 118140960795 + 3842752 * 2 ^ 59
def prefixEnd_3842752 : Nat := 4983230072969 + 3 ^ 40 * 3842752 * 2
def baseEnd_3842752 : Nat := 1973178812026254448827511

theorem tailTrace_3842752 : CollatzResearch.WordTrace tailWord_3842752 prefixEnd_3842752 1973178812026254448827511 := by
  unfold tailWord_3842752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70078339887186634318405255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93437786516248845757873673 70078339887186634318405255)
  ·
    refine ⟨105117509830779951477607883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70078339887186634318405255 105117509830779951477607883)
    ·
      refine ⟨157676264746169927216411825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105117509830779951477607883 157676264746169927216411825)
      ·
        refine ⟨118257198559627445412308869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157676264746169927216411825 118257198559627445412308869)
        ·
          refine ⟨22173224729930146014807913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118257198559627445412308869 22173224729930146014807913)
          ·
            refine ⟨16629918547447609511105935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22173224729930146014807913 16629918547447609511105935)
            ·
              refine ⟨24944877821171414266658903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629918547447609511105935 24944877821171414266658903)
              ·
                refine ⟨37417316731757121399988355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24944877821171414266658903 37417316731757121399988355)
                ·
                  refine ⟨56125975097635682099982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37417316731757121399988355 56125975097635682099982533)
                  ·
                    refine ⟨10523620330806690393746725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56125975097635682099982533 10523620330806690393746725)
                    ·
                      refine ⟨1973178812026254448827511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10523620330806690393746725 1973178812026254448827511)
                      ·
                        rfl

theorem cell23_3842752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_3842752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842752 prefixEnd_3842752 := by exact prefixLift 3842752
  have htrace : WordTrace (prefixWord ++ tailWord_3842752) baseStart_3842752 baseEnd_3842752 := by
    simpa [prefixWord, tailWord_3842752, baseEnd_3842752] using wordTrace_append hprefix tailTrace_3842752
  have hstable : (prefixWord ++ tailWord_3842752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842752).length < 2 ^ (prefixWord ++ tailWord_3842752).sum := by decide
  have hdescent : baseEnd_3842752 < baseStart_3842752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842756 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3842756 : Nat := 118140960795 + 3842756 * 2 ^ 59
def prefixEnd_3842756 : Nat := 4983230072969 + 3 ^ 40 * 3842756 * 2
def baseEnd_3842756 : Nat := 1973180865948872433177493

theorem tailTrace_3842756 : CollatzResearch.WordTrace tailWord_3842756 prefixEnd_3842756 1973180865948872433177493 := by
  unfold tailWord_3842756
  simp only [CollatzResearch.WordTrace]
  refine ⟨70078412833179388659978061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93437883777572518213304081 70078412833179388659978061)
  ·
    refine ⟨26279404812442270747491773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70078412833179388659978061 26279404812442270747491773)
    ·
      refine ⟨9854776804665851530309415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26279404812442270747491773 9854776804665851530309415)
      ·
        refine ⟨14782165206998777295464123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9854776804665851530309415 14782165206998777295464123)
        ·
          refine ⟨22173247810498165943196185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14782165206998777295464123 22173247810498165943196185)
          ·
            refine ⟨16629935857873624457397139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22173247810498165943196185 16629935857873624457397139)
            ·
              refine ⟨24944903786810436686095709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629935857873624457397139 24944903786810436686095709)
              ·
                refine ⟨9354338920053913757285891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24944903786810436686095709 9354338920053913757285891)
                ·
                  refine ⟨14031508380080870635928837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9354338920053913757285891 14031508380080870635928837)
                  ·
                    refine ⟨2630907821265163244236657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14031508380080870635928837 2630907821265163244236657)
                    ·
                      refine ⟨1973180865948872433177493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2630907821265163244236657 1973180865948872433177493)
                      ·
                        rfl

theorem cell23_3842756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3842756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842756 prefixEnd_3842756 := by exact prefixLift 3842756
  have htrace : WordTrace (prefixWord ++ tailWord_3842756) baseStart_3842756 baseEnd_3842756 := by
    simpa [prefixWord, tailWord_3842756, baseEnd_3842756] using wordTrace_append hprefix tailTrace_3842756
  have hstable : (prefixWord ++ tailWord_3842756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842756).length < 2 ^ (prefixWord ++ tailWord_3842756).sum := by decide
  have hdescent : baseEnd_3842756 < baseStart_3842756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842762 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_3842762 : Nat := 118140960795 + 3842762 * 2 ^ 59
def prefixEnd_3842762 : Nat := 4983230072969 + 3 ^ 40 * 3842762 * 2
def baseEnd_3842762 : Nat := 219242660759199934411385

theorem tailTrace_3842762 : CollatzResearch.WordTrace tailWord_3842762 prefixEnd_3842762 219242660759199934411385 := by
  unfold tailWord_3842762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35039261126084260086168635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93438029669558026896449693 35039261126084260086168635)
  ·
    refine ⟨52558891689126390129252953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35039261126084260086168635 52558891689126390129252953)
    ·
      refine ⟨39419168766844792596939715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52558891689126390129252953 39419168766844792596939715)
      ·
        refine ⟨59128753150267188895409573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39419168766844792596939715 59128753150267188895409573)
        ·
          refine ⟨11086641215675097917889295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59128753150267188895409573 11086641215675097917889295)
          ·
            refine ⟨16629961823512646876833943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086641215675097917889295 16629961823512646876833943)
            ·
              refine ⟨24944942735268970315250915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16629961823512646876833943 24944942735268970315250915)
              ·
                refine ⟨37417414102903455472876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24944942735268970315250915 37417414102903455472876373)
                ·
                  refine ⟨219242660759199934411385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37417414102903455472876373 219242660759199934411385)
                  ·
                    rfl

theorem cell23_3842762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_3842762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842762 prefixEnd_3842762 := by exact prefixLift 3842762
  have htrace : WordTrace (prefixWord ++ tailWord_3842762) baseStart_3842762 baseEnd_3842762 := by
    simpa [prefixWord, tailWord_3842762, baseEnd_3842762] using wordTrace_append hprefix tailTrace_3842762
  have hstable : (prefixWord ++ tailWord_3842762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842762).length < 2 ^ (prefixWord ++ tailWord_3842762).sum := by decide
  have hdescent : baseEnd_3842762 < baseStart_3842762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842789 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3842789 : Nat := 118140960795 + 3842789 * 2 ^ 59
def prefixEnd_3842789 : Nat := 4983230072969 + 3 ^ 40 * 3842789 * 2
def baseEnd_3842789 : Nat := 1973197810810470804064841

theorem tailTrace_3842789 : CollatzResearch.WordTrace tailWord_3842789 prefixEnd_3842789 1973197810810470804064841 := by
  unfold tailWord_3842789
  simp only [CollatzResearch.WordTrace]
  refine ⟨140158029275239223955907421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93438686183492815970604947 140158029275239223955907421)
  ·
    refine ⟨52559260978214708983465283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140158029275239223955907421 52559260978214708983465283)
    ·
      refine ⟨78838891467322063475197925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52559260978214708983465283 78838891467322063475197925)
      ·
        refine ⟨14782292150122886901599611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78838891467322063475197925 14782292150122886901599611)
        ·
          refine ⟨22173438225184330352399417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14782292150122886901599611 22173438225184330352399417)
          ·
            refine ⟨16630078668888247764299563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22173438225184330352399417 16630078668888247764299563)
            ·
              refine ⟨24945118003332371646449345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16630078668888247764299563 24945118003332371646449345)
              ·
                refine ⟨18708838502499278734837009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24945118003332371646449345 18708838502499278734837009)
                ·
                  refine ⟨14031628876874459051127757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18708838502499278734837009 14031628876874459051127757)
                  ·
                    refine ⟨5261860828827922144172909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14031628876874459051127757 5261860828827922144172909)
                    ·
                      refine ⟨1973197810810470804064841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5261860828827922144172909 1973197810810470804064841)
                      ·
                        rfl

theorem cell23_3842789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3842789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842789 prefixEnd_3842789 := by exact prefixLift 3842789
  have htrace : WordTrace (prefixWord ++ tailWord_3842789) baseStart_3842789 baseEnd_3842789 := by
    simpa [prefixWord, tailWord_3842789, baseEnd_3842789] using wordTrace_append hprefix tailTrace_3842789
  have hstable : (prefixWord ++ tailWord_3842789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842789).length < 2 ^ (prefixWord ++ tailWord_3842789).sum := by decide
  have hdescent : baseEnd_3842789 < baseStart_3842789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842899 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 1, 5]
def baseStart_3842899 : Nat := 118140960795 + 3842899 * 2 ^ 59
def prefixEnd_3842899 : Nat := 4983230072969 + 3 ^ 40 * 3842899 * 2
def baseEnd_3842899 : Nat := 657751431227488457896445

theorem tailTrace_3842899 : CollatzResearch.WordTrace tailWord_3842899 prefixEnd_3842899 657751431227488457896445 := by
  unfold tailWord_3842899
  simp only [CollatzResearch.WordTrace]
  refine ⟨140162041304840712742411751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93441360869893808494941167 140162041304840712742411751)
  ·
    refine ⟨210243061957261069113617627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140162041304840712742411751 210243061957261069113617627)
    ·
      refine ⟨315364592935891603670426441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210243061957261069113617627 315364592935891603670426441)
      ·
        refine ⟨236523444701918702752819831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315364592935891603670426441 236523444701918702752819831)
        ·
          refine ⟨354785167052878054129229747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236523444701918702752819831 354785167052878054129229747)
          ·
            refine ⟨532177750579317081193844621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354785167052878054129229747 532177750579317081193844621)
            ·
              refine ⟨199566656467243905447691733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532177750579317081193844621 199566656467243905447691733)
              ·
                refine ⟨4677343510951029033930275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199566656467243905447691733 4677343510951029033930275)
                ·
                  refine ⟨7016015266426543550895413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677343510951029033930275 7016015266426543550895413)
                  ·
                    refine ⟨657751431227488457896445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7016015266426543550895413 657751431227488457896445)
                    ·
                      rfl

theorem cell23_3842899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 5].length) (baseStart_3842899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842899 prefixEnd_3842899 := by exact prefixLift 3842899
  have htrace : WordTrace (prefixWord ++ tailWord_3842899) baseStart_3842899 baseEnd_3842899 := by
    simpa [prefixWord, tailWord_3842899, baseEnd_3842899] using wordTrace_append hprefix tailTrace_3842899
  have hstable : (prefixWord ++ tailWord_3842899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842899).length < 2 ^ (prefixWord ++ tailWord_3842899).sum := by decide
  have hdescent : baseEnd_3842899 < baseStart_3842899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842929 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_3842929 : Nat := 118140960795 + 3842929 * 2 ^ 59
def prefixEnd_3842929 : Nat := 4983230072969 + 3 ^ 40 * 3842929 * 2
def baseEnd_3842929 : Nat := 657756566034033418771399

theorem tailTrace_3842929 : CollatzResearch.WordTrace tailWord_3842929 prefixEnd_3842929 657756566034033418771399 := by
  unfold tailWord_3842929
  simp only [CollatzResearch.WordTrace]
  refine ⟨140163135494732027866003841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93442090329821351910669227 140163135494732027866003841)
  ·
    refine ⟨105122351621049020899502881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140163135494732027866003841 105122351621049020899502881)
    ·
      refine ⟨78841763715786765674627161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105122351621049020899502881 78841763715786765674627161)
      ·
        refine ⟨59131322786840074255970371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78841763715786765674627161 59131322786840074255970371)
        ·
          refine ⟨88696984180260111383955557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59131322786840074255970371 88696984180260111383955557)
          ·
            refine ⟨16630684533798770884491667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88696984180260111383955557 16630684533798770884491667)
            ·
              refine ⟨24946026800698156326737501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16630684533798770884491667 24946026800698156326737501)
              ·
                refine ⟨9354760050261808622526563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24946026800698156326737501 9354760050261808622526563)
                ·
                  refine ⟨14032140075392712933789845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9354760050261808622526563 14032140075392712933789845)
                  ·
                    refine ⟨657756566034033418771399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14032140075392712933789845 657756566034033418771399)
                    ·
                      rfl

theorem cell23_3842929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_3842929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842929 prefixEnd_3842929 := by exact prefixLift 3842929
  have htrace : WordTrace (prefixWord ++ tailWord_3842929) baseStart_3842929 baseEnd_3842929 := by
    simpa [prefixWord, tailWord_3842929, baseEnd_3842929] using wordTrace_append hprefix tailTrace_3842929
  have hstable : (prefixWord ++ tailWord_3842929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842929).length < 2 ^ (prefixWord ++ tailWord_3842929).sum := by decide
  have hdescent : baseEnd_3842929 < baseStart_3842929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842953 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 1, 1, 4]
def baseStart_3842953 : Nat := 118140960795 + 3842953 * 2 ^ 59
def prefixEnd_3842953 : Nat := 4983230072969 + 3 ^ 40 * 3842953 * 2
def baseEnd_3842953 : Nat := 1973282021637808162414087

theorem tailTrace_3842953 : CollatzResearch.WordTrace tailWord_3842953 prefixEnd_3842953 1973282021637808162414087 := by
  unfold tailWord_3842953
  simp only [CollatzResearch.WordTrace]
  refine ⟨140164010846645079964877513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93442673897763386643251675 140164010846645079964877513)
  ·
    refine ⟨105123008134983809973658135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140164010846645079964877513 105123008134983809973658135)
    ·
      refine ⟨157684512202475714960487203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105123008134983809973658135 157684512202475714960487203)
      ·
        refine ⟨236526768303713572440730805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157684512202475714960487203 236526768303713572440730805)
        ·
          refine ⟨22174384528473147416318513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236526768303713572440730805 22174384528473147416318513)
          ·
            refine ⟨16630788396354860562238885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22174384528473147416318513 16630788396354860562238885)
            ·
              refine ⟨3118272824316536355419791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16630788396354860562238885 3118272824316536355419791)
              ·
                refine ⟨4677409236474804533129687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118272824316536355419791 4677409236474804533129687)
                ·
                  refine ⟨7016113854712206799694531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677409236474804533129687 7016113854712206799694531)
                  ·
                    refine ⟨10524170782068310199541797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7016113854712206799694531 10524170782068310199541797)
                    ·
                      refine ⟨1973282021637808162414087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10524170782068310199541797 1973282021637808162414087)
                      ·
                        rfl

theorem cell23_3842953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 1, 4].length) (baseStart_3842953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842953 prefixEnd_3842953 := by exact prefixLift 3842953
  have htrace : WordTrace (prefixWord ++ tailWord_3842953) baseStart_3842953 baseEnd_3842953 := by
    simpa [prefixWord, tailWord_3842953, baseEnd_3842953] using wordTrace_append hprefix tailTrace_3842953
  have hstable : (prefixWord ++ tailWord_3842953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842953).length < 2 ^ (prefixWord ++ tailWord_3842953).sum := by decide
  have hdescent : baseEnd_3842953 < baseStart_3842953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842993 : List Nat := [1, 2, 2, 4, 3, 2, 2, 7]
def baseStart_3842993 : Nat := 118140960795 + 3842993 * 2 ^ 59
def prefixEnd_3842993 : Nat := 4983230072969 + 3 ^ 40 * 3842993 * 2
def baseEnd_3842993 : Nat := 73085280031999555774589

theorem tailTrace_3842993 : CollatzResearch.WordTrace tailWord_3842993 prefixEnd_3842993 73085280031999555774589 := by
  unfold tailWord_3842993
  simp only [CollatzResearch.WordTrace]
  refine ⟨140165469766500166796333633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93443646511000111197555755 140165469766500166796333633)
  ·
    refine ⟨105124102324875125097250225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140165469766500166796333633 105124102324875125097250225)
    ·
      refine ⟨78843076743656343822937669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105124102324875125097250225 78843076743656343822937669)
      ·
        refine ⟨14783076889435564466800813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78843076743656343822937669 14783076889435564466800813)
        ·
          refine ⟨5543653833538336675050305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14783076889435564466800813 5543653833538336675050305)
          ·
            refine ⟨4157740375153752506287729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543653833538336675050305 4157740375153752506287729)
            ·
              refine ⟨3118305281365314379715797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157740375153752506287729 3118305281365314379715797)
              ·
                refine ⟨73085280031999555774589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3118305281365314379715797 73085280031999555774589)
                ·
                  rfl

theorem cell23_3842993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 7].length) (baseStart_3842993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842993 prefixEnd_3842993 := by exact prefixLift 3842993
  have htrace : WordTrace (prefixWord ++ tailWord_3842993) baseStart_3842993 baseEnd_3842993 := by
    simpa [prefixWord, tailWord_3842993, baseEnd_3842993] using wordTrace_append hprefix tailTrace_3842993
  have hstable : (prefixWord ++ tailWord_3842993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842993).length < 2 ^ (prefixWord ++ tailWord_3842993).sum := by decide
  have hdescent : baseEnd_3842993 < baseStart_3842993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842998 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3842998 : Nat := 118140960795 + 3842998 * 2 ^ 59
def prefixEnd_3842998 : Nat := 4983230072969 + 3 ^ 40 * 3842998 * 2
def baseEnd_3842998 : Nat := 1973305128267260486351381

theorem tailTrace_3842998 : CollatzResearch.WordTrace tailWord_3842998 prefixEnd_3842998 1973305128267260486351381 := by
  unfold tailWord_3842998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760353258217628290641603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93443768087654701766843765 8760353258217628290641603)
  ·
    refine ⟨13140529887326442435962405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760353258217628290641603 13140529887326442435962405)
    ·
      refine ⟨2463849353873707956742951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13140529887326442435962405 2463849353873707956742951)
      ·
        refine ⟨3695774030810561935114427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463849353873707956742951 3695774030810561935114427)
        ·
          refine ⟨5543661046215842902671641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695774030810561935114427 5543661046215842902671641)
          ·
            refine ⟨4157745784661882177003731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543661046215842902671641 4157745784661882177003731)
            ·
              refine ⟨6236618676992823265505597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157745784661882177003731 6236618676992823265505597)
              ·
                refine ⟨2338732003872308724564599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6236618676992823265505597 2338732003872308724564599)
                ·
                  refine ⟨3508098005808463086846899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338732003872308724564599 3508098005808463086846899)
                  ·
                    refine ⟨5262147008712694630270349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508098005808463086846899 5262147008712694630270349)
                    ·
                      refine ⟨1973305128267260486351381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262147008712694630270349 1973305128267260486351381)
                      ·
                        rfl

theorem cell23_3842998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3842998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842998 prefixEnd_3842998 := by exact prefixLift 3842998
  have htrace : WordTrace (prefixWord ++ tailWord_3842998) baseStart_3842998 baseEnd_3842998 := by
    simpa [prefixWord, tailWord_3842998, baseEnd_3842998] using wordTrace_append hprefix tailTrace_3842998
  have hstable : (prefixWord ++ tailWord_3842998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842998).length < 2 ^ (prefixWord ++ tailWord_3842998).sum := by decide
  have hdescent : baseEnd_3842998 < baseStart_3842998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3842999 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_3842999 : Nat := 118140960795 + 3842999 * 2 ^ 59
def prefixEnd_3842999 : Nat := 4983230072969 + 3 ^ 40 * 3842999 * 2
def baseEnd_3842999 : Nat := 1973305641747914982438875

theorem tailTrace_3842999 : CollatzResearch.WordTrace tailWord_3842999 prefixEnd_3842999 1973305641747914982438875 := by
  unfold tailWord_3842999
  simp only [CollatzResearch.WordTrace]
  refine ⟨140165688604478429821052051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93443792402985619880701367 140165688604478429821052051)
  ·
    refine ⟨210248532906717644731578077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140165688604478429821052051 210248532906717644731578077)
    ·
      refine ⟨78843199840019116774341779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210248532906717644731578077 78843199840019116774341779)
      ·
        refine ⟨118264799760028675161512669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78843199840019116774341779 118264799760028675161512669)
        ·
          refine ⟨44349299910010753185567251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118264799760028675161512669 44349299910010753185567251)
          ·
            refine ⟨66523949865016129778350877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44349299910010753185567251 66523949865016129778350877)
            ·
              refine ⟨24946481199381048666881579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66523949865016129778350877 24946481199381048666881579)
              ·
                refine ⟨37419721799071573000322369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24946481199381048666881579 37419721799071573000322369)
                ·
                  refine ⟨28064791349303679750241777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37419721799071573000322369 28064791349303679750241777)
                  ·
                    refine ⟨21048593511977759812681333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28064791349303679750241777 21048593511977759812681333)
                    ·
                      refine ⟨1973305641747914982438875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21048593511977759812681333 1973305641747914982438875)
                      ·
                        rfl

theorem cell23_3842999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_3842999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3842999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3842999 prefixEnd_3842999 := by exact prefixLift 3842999
  have htrace : WordTrace (prefixWord ++ tailWord_3842999) baseStart_3842999 baseEnd_3842999 := by
    simpa [prefixWord, tailWord_3842999, baseEnd_3842999] using wordTrace_append hprefix tailTrace_3842999
  have hstable : (prefixWord ++ tailWord_3842999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3842999).length < 2 ^ (prefixWord ++ tailWord_3842999).sum := by decide
  have hdescent : baseEnd_3842999 < baseStart_3842999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3842999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843037 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3843037 : Nat := 118140960795 + 3843037 * 2 ^ 59
def prefixEnd_3843037 : Nat := 4983230072969 + 3 ^ 40 * 3843037 * 2
def baseEnd_3843037 : Nat := 1973325154012785833763701

theorem tailTrace_3843037 : CollatzResearch.WordTrace tailWord_3843037 prefixEnd_3843037 1973325154012785833763701 := by
  unfold tailWord_3843037
  simp only [CollatzResearch.WordTrace]
  refine ⟨140167074578340762310935365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93444716385560508207290243 140167074578340762310935365)
  ·
    refine ⟨26281326483438892933300381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140167074578340762310935365 26281326483438892933300381)
    ·
      refine ⟨9855497431289584849987643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26281326483438892933300381 9855497431289584849987643)
      ·
        refine ⟨14783246146934377274981465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9855497431289584849987643 14783246146934377274981465)
        ·
          refine ⟨11087434610200782956236099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14783246146934377274981465 11087434610200782956236099)
          ·
            refine ⟨16631151915301174434354149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087434610200782956236099 16631151915301174434354149)
            ·
              refine ⟨3118340984118970206441403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16631151915301174434354149 3118340984118970206441403)
              ·
                refine ⟨4677511476178455309662105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118340984118970206441403 4677511476178455309662105)
                ·
                  refine ⟨3508133607133841482246579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677511476178455309662105 3508133607133841482246579)
                  ·
                    refine ⟨5262200410700762223369869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508133607133841482246579 5262200410700762223369869)
                    ·
                      refine ⟨1973325154012785833763701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262200410700762223369869 1973325154012785833763701)
                      ·
                        rfl

theorem cell23_3843037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3843037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843037 prefixEnd_3843037 := by exact prefixLift 3843037
  have htrace : WordTrace (prefixWord ++ tailWord_3843037) baseStart_3843037 baseEnd_3843037 := by
    simpa [prefixWord, tailWord_3843037, baseEnd_3843037] using wordTrace_append hprefix tailTrace_3843037
  have hstable : (prefixWord ++ tailWord_3843037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843037).length < 2 ^ (prefixWord ++ tailWord_3843037).sum := by decide
  have hdescent : baseEnd_3843037 < baseStart_3843037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843043 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3843043 : Nat := 118140960795 + 3843043 * 2 ^ 59
def prefixEnd_3843043 : Nat := 4983230072969 + 3 ^ 40 * 3843043 * 2
def baseEnd_3843043 : Nat := 1973328234896712810288673

theorem tailTrace_3843043 : CollatzResearch.WordTrace tailWord_3843043 prefixEnd_3843043 1973328234896712810288673 := by
  unfold tailWord_3843043
  simp only [CollatzResearch.WordTrace]
  refine ⟨140167293416319025335653783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93444862277546016890435855 140167293416319025335653783)
  ·
    refine ⟨210250940124478538003480675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140167293416319025335653783 210250940124478538003480675)
    ·
      refine ⟨315376410186717807005221013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210250940124478538003480675 315376410186717807005221013)
      ·
        refine ⟨14783269227502397203369735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 315376410186717807005221013 14783269227502397203369735)
        ·
          refine ⟨22174903841253595805054603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14783269227502397203369735 22174903841253595805054603)
          ·
            refine ⟨33262355761880393707581905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22174903841253595805054603 33262355761880393707581905)
            ·
              refine ⟨24946766821410295280686429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33262355761880393707581905 24946766821410295280686429)
              ·
                refine ⟨9355037558028860730257411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24946766821410295280686429 9355037558028860730257411)
                ·
                  refine ⟨14032556337043291095386117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355037558028860730257411 14032556337043291095386117)
                  ·
                    refine ⟨2631104313195617080384897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14032556337043291095386117 2631104313195617080384897)
                    ·
                      refine ⟨1973328234896712810288673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631104313195617080384897 1973328234896712810288673)
                      ·
                        rfl

theorem cell23_3843043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3843043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843043 prefixEnd_3843043 := by exact prefixLift 3843043
  have htrace : WordTrace (prefixWord ++ tailWord_3843043) baseStart_3843043 baseEnd_3843043 := by
    simpa [prefixWord, tailWord_3843043, baseEnd_3843043] using wordTrace_append hprefix tailTrace_3843043
  have hstable : (prefixWord ++ tailWord_3843043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843043).length < 2 ^ (prefixWord ++ tailWord_3843043).sum := by decide
  have hdescent : baseEnd_3843043 < baseStart_3843043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843047 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3843047 : Nat := 118140960795 + 3843047 * 2 ^ 59
def prefixEnd_3843047 : Nat := 4983230072969 + 3 ^ 40 * 3843047 * 2
def baseEnd_3843047 : Nat := 1973330288819330794638655

theorem tailTrace_3843047 : CollatzResearch.WordTrace tailWord_3843047 prefixEnd_3843047 1973330288819330794638655 := by
  unfold tailWord_3843047
  simp only [CollatzResearch.WordTrace]
  refine ⟨140167439308304534018799395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93444959538869689345866263 140167439308304534018799395)
  ·
    refine ⟨210251158962456801028199093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140167439308304534018799395 210251158962456801028199093)
    ·
      refine ⟨19711046152730325096393665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210251158962456801028199093 19711046152730325096393665)
      ·
        refine ⟨14783284614547743822295249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19711046152730325096393665 14783284614547743822295249)
        ·
          refine ⟨11087463460910807866721437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14783284614547743822295249 11087463460910807866721437)
          ·
            refine ⟨4157798797841552950020539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11087463460910807866721437 4157798797841552950020539)
            ·
              refine ⟨6236698196762329425030809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157798797841552950020539 6236698196762329425030809)
              ·
                refine ⟨4677523647571747068773107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236698196762329425030809 4677523647571747068773107)
                ·
                  refine ⟨7016285471357620603159661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677523647571747068773107 7016285471357620603159661)
                  ·
                    refine ⟨2631107051759107726184873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7016285471357620603159661 2631107051759107726184873)
                    ·
                      refine ⟨1973330288819330794638655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631107051759107726184873 1973330288819330794638655)
                      ·
                        rfl

theorem cell23_3843047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3843047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843047 prefixEnd_3843047 := by exact prefixLift 3843047
  have htrace : WordTrace (prefixWord ++ tailWord_3843047) baseStart_3843047 baseEnd_3843047 := by
    simpa [prefixWord, tailWord_3843047, baseEnd_3843047] using wordTrace_append hprefix tailTrace_3843047
  have hstable : (prefixWord ++ tailWord_3843047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843047).length < 2 ^ (prefixWord ++ tailWord_3843047).sum := by decide
  have hdescent : baseEnd_3843047 < baseStart_3843047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843083 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 5]
def baseStart_3843083 : Nat := 118140960795 + 3843083 * 2 ^ 59
def prefixEnd_3843083 : Nat := 4983230072969 + 3 ^ 40 * 3843083 * 2
def baseEnd_3843083 : Nat := 219260974902543628198721

theorem tailTrace_3843083 : CollatzResearch.WordTrace tailWord_3843083 prefixEnd_3843083 219260974902543628198721 := by
  unfold tailWord_3843083
  simp only [CollatzResearch.WordTrace]
  refine ⟨140168752336174112167109903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93445834890782741444739935 140168752336174112167109903)
  ·
    refine ⟨210253128504261168250664855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140168752336174112167109903 210253128504261168250664855)
    ·
      refine ⟨315379692756391752375997283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210253128504261168250664855 315379692756391752375997283)
      ·
        refine ⟨473069539134587628563995925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315379692756391752375997283 473069539134587628563995925)
        ·
          refine ⟨22175134646933795088937309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 473069539134587628563995925 22175134646933795088937309)
          ·
            refine ⟨8315675492600173158351491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22175134646933795088937309 8315675492600173158351491)
            ·
              refine ⟨12473513238900259737527237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315675492600173158351491 12473513238900259737527237)
              ·
                refine ⟨2338783732293798700786357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12473513238900259737527237 2338783732293798700786357)
                ·
                  refine ⟨219260974902543628198721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2338783732293798700786357 219260974902543628198721)
                  ·
                    rfl

theorem cell23_3843083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 5].length) (baseStart_3843083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843083 prefixEnd_3843083 := by exact prefixLift 3843083
  have htrace : WordTrace (prefixWord ++ tailWord_3843083) baseStart_3843083 baseEnd_3843083 := by
    simpa [prefixWord, tailWord_3843083, baseEnd_3843083] using wordTrace_append hprefix tailTrace_3843083
  have hstable : (prefixWord ++ tailWord_3843083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843083).length < 2 ^ (prefixWord ++ tailWord_3843083).sum := by decide
  have hdescent : baseEnd_3843083 < baseStart_3843083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843093 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3843093 : Nat := 118140960795 + 3843093 * 2 ^ 59
def prefixEnd_3843093 : Nat := 4983230072969 + 3 ^ 40 * 3843093 * 2
def baseEnd_3843093 : Nat := 1973353908929437614663443

theorem tailTrace_3843093 : CollatzResearch.WordTrace tailWord_3843093 prefixEnd_3843093 1973353908929437614663443 := by
  unfold tailWord_3843093
  simp only [CollatzResearch.WordTrace]
  refine ⟨140169117066137883874973933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93446078044091922583315955 140169117066137883874973933)
  ·
    refine ⟨52563418899801706453115225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140169117066137883874973933 52563418899801706453115225)
    ·
      refine ⟨39422564174851279839836419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52563418899801706453115225 39422564174851279839836419)
      ·
        refine ⟨59133846262276919759754629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39422564174851279839836419 59133846262276919759754629)
        ·
          refine ⟨11087596174176922454953993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59133846262276919759754629 11087596174176922454953993)
          ·
            refine ⟨8315697130632691841215495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11087596174176922454953993 8315697130632691841215495)
            ·
              refine ⟨12473545695949037761823243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315697130632691841215495 12473545695949037761823243)
              ·
                refine ⟨18710318543923556642734865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12473545695949037761823243 18710318543923556642734865)
                ·
                  refine ⟨14032738907942667482051149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18710318543923556642734865 14032738907942667482051149)
                  ·
                    refine ⟨5262277090478500305769181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14032738907942667482051149 5262277090478500305769181)
                    ·
                      refine ⟨1973353908929437614663443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262277090478500305769181 1973353908929437614663443)
                      ·
                        rfl

theorem cell23_3843093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3843093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843093 prefixEnd_3843093 := by exact prefixLift 3843093
  have htrace : WordTrace (prefixWord ++ tailWord_3843093) baseStart_3843093 baseEnd_3843093 := by
    simpa [prefixWord, tailWord_3843093, baseEnd_3843093] using wordTrace_append hprefix tailTrace_3843093
  have hstable : (prefixWord ++ tailWord_3843093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843093).length < 2 ^ (prefixWord ++ tailWord_3843093).sum := by decide
  have hdescent : baseEnd_3843093 < baseStart_3843093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843116 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_3843116 : Nat := 118140960795 + 3843116 * 2 ^ 59
def prefixEnd_3843116 : Nat := 4983230072969 + 3 ^ 40 * 3843116 * 2
def baseEnd_3843116 : Nat := 1973365718984491024675837

theorem tailTrace_3843116 : CollatzResearch.WordTrace tailWord_3843116 prefixEnd_3843116 1973365718984491024675837 := by
  unfold tailWord_3843116
  simp only [CollatzResearch.WordTrace]
  refine ⟨70084977972527279401530601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93446637296703039202040801 70084977972527279401530601)
  ·
    refine ⟨52563733479395459551147951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70084977972527279401530601 52563733479395459551147951)
    ·
      refine ⟨78845600219093189326721927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52563733479395459551147951 78845600219093189326721927)
      ·
        refine ⟨118268400328639783990082891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78845600219093189326721927 118268400328639783990082891)
        ·
          refine ⟨177402600492959675985124337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118268400328639783990082891 177402600492959675985124337)
          ·
            refine ⟨133051950369719756988843253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177402600492959675985124337 133051950369719756988843253)
            ·
              refine ⟨12473620347161227217704055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133051950369719756988843253 12473620347161227217704055)
              ·
                refine ⟨18710430520741840826556083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12473620347161227217704055 18710430520741840826556083)
                ·
                  refine ⟨28065645781112761239834125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18710430520741840826556083 28065645781112761239834125)
                  ·
                    refine ⟨10524617167917285464937797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28065645781112761239834125 10524617167917285464937797)
                    ·
                      refine ⟨1973365718984491024675837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10524617167917285464937797 1973365718984491024675837)
                      ·
                        rfl

theorem cell23_3843116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_3843116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843116 prefixEnd_3843116 := by exact prefixLift 3843116
  have htrace : WordTrace (prefixWord ++ tailWord_3843116) baseStart_3843116 baseEnd_3843116 := by
    simpa [prefixWord, tailWord_3843116, baseEnd_3843116] using wordTrace_append hprefix tailTrace_3843116
  have hstable : (prefixWord ++ tailWord_3843116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843116).length < 2 ^ (prefixWord ++ tailWord_3843116).sum := by decide
  have hdescent : baseEnd_3843116 < baseStart_3843116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843143 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 3, 4]
def baseStart_3843143 : Nat := 118140960795 + 3843143 * 2 ^ 59
def prefixEnd_3843143 : Nat := 4983230072969 + 3 ^ 40 * 3843143 * 2
def baseEnd_3843143 : Nat := 657793194320720806346071

theorem tailTrace_3843143 : CollatzResearch.WordTrace tailWord_3843143 prefixEnd_3843143 657793194320720806346071 := by
  unfold tailWord_3843143
  simp only [CollatzResearch.WordTrace]
  refine ⟨140170940715956742414294083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93447293810637828276196055 140170940715956742414294083)
  ·
    refine ⟨210256411073935113621441125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140170940715956742414294083 210256411073935113621441125)
    ·
      refine ⟨39423077076362833804020211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210256411073935113621441125 39423077076362833804020211)
      ·
        refine ⟨59134615614544250706030317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39423077076362833804020211 59134615614544250706030317)
        ·
          refine ⟨22175480855454094014761369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59134615614544250706030317 22175480855454094014761369)
          ·
            refine ⟨16631610641590570511071027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22175480855454094014761369 16631610641590570511071027)
            ·
              refine ⟨24947415962385855766606541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16631610641590570511071027 24947415962385855766606541)
              ·
                refine ⟨9355280985894695912477453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24947415962385855766606541 9355280985894695912477453)
                ·
                  refine ⟨3508230369710510967179045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9355280985894695912477453 3508230369710510967179045)
                  ·
                    refine ⟨657793194320720806346071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508230369710510967179045 657793194320720806346071)
                    ·
                      rfl

theorem cell23_3843143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_3843143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843143 prefixEnd_3843143 := by exact prefixLift 3843143
  have htrace : WordTrace (prefixWord ++ tailWord_3843143) baseStart_3843143 baseEnd_3843143 := by
    simpa [prefixWord, tailWord_3843143, baseEnd_3843143] using wordTrace_append hprefix tailTrace_3843143
  have hstable : (prefixWord ++ tailWord_3843143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843143).length < 2 ^ (prefixWord ++ tailWord_3843143).sum := by decide
  have hdescent : baseEnd_3843143 < baseStart_3843143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843170 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3843170 : Nat := 118140960795 + 3843170 * 2 ^ 59
def prefixEnd_3843170 : Nat := 4983230072969 + 3 ^ 40 * 3843170 * 2
def baseEnd_3843170 : Nat := 1973393446939833813400589

theorem tailTrace_3843170 : CollatzResearch.WordTrace tailWord_3843170 prefixEnd_3843170 1973393446939833813400589 := by
  unfold tailWord_3843170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35042981371714731506381741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93447950324572617350351309 35042981371714731506381741)
  ·
    refine ⟨13141118014393024314893153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35042981371714731506381741 13141118014393024314893153)
    ·
      refine ⟨9855838510794768236169865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13141118014393024314893153 9855838510794768236169865)
      ·
        refine ⟨7391878883096076177127399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855838510794768236169865 7391878883096076177127399)
        ·
          refine ⟨11087818324644114265691099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391878883096076177127399 11087818324644114265691099)
          ·
            refine ⟨16631727486966171398536649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087818324644114265691099 16631727486966171398536649)
            ·
              refine ⟨12473795615224628548902487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16631727486966171398536649 12473795615224628548902487)
              ·
                refine ⟨18710693422836942823353731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12473795615224628548902487 18710693422836942823353731)
                ·
                  refine ⟨28066040134255414235030597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18710693422836942823353731 28066040134255414235030597)
                  ·
                    refine ⟨5262382525172890169068237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28066040134255414235030597 5262382525172890169068237)
                    ·
                      refine ⟨1973393446939833813400589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262382525172890169068237 1973393446939833813400589)
                      ·
                        rfl

theorem cell23_3843170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3843170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843170 prefixEnd_3843170 := by exact prefixLift 3843170
  have htrace : WordTrace (prefixWord ++ tailWord_3843170) baseStart_3843170 baseEnd_3843170 := by
    simpa [prefixWord, tailWord_3843170, baseEnd_3843170] using wordTrace_append hprefix tailTrace_3843170
  have hstable : (prefixWord ++ tailWord_3843170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843170).length < 2 ^ (prefixWord ++ tailWord_3843170).sum := by decide
  have hdescent : baseEnd_3843170 < baseStart_3843170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843177 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 1, 4]
def baseStart_3843177 : Nat := 118140960795 + 3843177 * 2 ^ 59
def prefixEnd_3843177 : Nat := 4983230072969 + 3 ^ 40 * 3843177 * 2
def baseEnd_3843177 : Nat := 657799013768138428671019

theorem tailTrace_3843177 : CollatzResearch.WordTrace tailWord_3843177 prefixEnd_3843177 657799013768138428671019 := by
  unfold tailWord_3843177
  simp only [CollatzResearch.WordTrace]
  refine ⟨140172180797833566221031785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93448120531889044147354523 140172180797833566221031785)
  ·
    refine ⟨105129135598375174665773839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140172180797833566221031785 105129135598375174665773839)
    ·
      refine ⟨157693703397562761998660759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105129135598375174665773839 157693703397562761998660759)
      ·
        refine ⟨236540555096344142997991139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157693703397562761998660759 236540555096344142997991139)
        ·
          refine ⟨354810832644516214496986709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236540555096344142997991139 354810832644516214496986709)
          ·
            refine ⟨4157939445052924388636563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 354810832644516214496986709 4157939445052924388636563)
            ·
              refine ⟨6236909167579386582954845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157939445052924388636563 6236909167579386582954845)
              ·
                refine ⟨2338840937842269968608067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6236909167579386582954845 2338840937842269968608067)
                ·
                  refine ⟨3508261406763404952912101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338840937842269968608067 3508261406763404952912101)
                  ·
                    refine ⟨657799013768138428671019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508261406763404952912101 657799013768138428671019)
                    ·
                      rfl

theorem cell23_3843177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 4].length) (baseStart_3843177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843177 prefixEnd_3843177 := by exact prefixLift 3843177
  have htrace : WordTrace (prefixWord ++ tailWord_3843177) baseStart_3843177 baseEnd_3843177 := by
    simpa [prefixWord, tailWord_3843177, baseEnd_3843177] using wordTrace_append hprefix tailTrace_3843177
  have hstable : (prefixWord ++ tailWord_3843177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843177).length < 2 ^ (prefixWord ++ tailWord_3843177).sum := by decide
  have hdescent : baseEnd_3843177 < baseStart_3843177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843200 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3]
def baseStart_3843200 : Nat := 118140960795 + 3843200 * 2 ^ 59
def prefixEnd_3843200 : Nat := 4983230072969 + 3 ^ 40 * 3843200 * 2
def baseEnd_3843200 : Nat := 1973408851359468696025451

theorem tailTrace_3843200 : CollatzResearch.WordTrace tailWord_3843200 prefixEnd_3843200 1973408851359468696025451 := by
  unfold tailWord_3843200
  simp only [CollatzResearch.WordTrace]
  refine ⟨70086509838375120574559527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93448679784500160766079369 70086509838375120574559527)
  ·
    refine ⟨105129764757562680861839291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70086509838375120574559527 105129764757562680861839291)
    ·
      refine ⟨157694647136344021292758937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105129764757562680861839291 157694647136344021292758937)
      ·
        refine ⟨118270985352258015969569203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157694647136344021292758937 118270985352258015969569203)
        ·
          refine ⟨177406478028387023954353805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118270985352258015969569203 177406478028387023954353805)
          ·
            refine ⟨66527429260645133982882677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177406478028387023954353805 66527429260645133982882677)
            ·
              refine ⟨6236946493185481310895251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66527429260645133982882677 6236946493185481310895251)
              ·
                refine ⟨9355419739778221966342877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236946493185481310895251 9355419739778221966342877)
                ·
                  refine ⟨3508282402416833237378579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9355419739778221966342877 3508282402416833237378579)
                  ·
                    refine ⟨5262423603625249856067869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508282402416833237378579 5262423603625249856067869)
                    ·
                      refine ⟨1973408851359468696025451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262423603625249856067869 1973408851359468696025451)
                      ·
                        rfl

theorem cell23_3843200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_3843200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843200 prefixEnd_3843200 := by exact prefixLift 3843200
  have htrace : WordTrace (prefixWord ++ tailWord_3843200) baseStart_3843200 baseEnd_3843200 := by
    simpa [prefixWord, tailWord_3843200, baseEnd_3843200] using wordTrace_append hprefix tailTrace_3843200
  have hstable : (prefixWord ++ tailWord_3843200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843200).length < 2 ^ (prefixWord ++ tailWord_3843200).sum := by decide
  have hdescent : baseEnd_3843200 < baseStart_3843200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843210 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_3843210 : Nat := 118140960795 + 3843210 * 2 ^ 59
def prefixEnd_3843210 : Nat := 4983230072969 + 3 ^ 40 * 3843210 * 2
def baseEnd_3843210 : Nat := 1973413986166013656900405

theorem tailTrace_3843210 : CollatzResearch.WordTrace tailWord_3843210 prefixEnd_3843210 1973413986166013656900405 := by
  unfold tailWord_3843210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043346101678503214245771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93448922937809341904655389 35043346101678503214245771)
  ·
    refine ⟨52565019152517754821368657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35043346101678503214245771 52565019152517754821368657)
    ·
      refine ⟨39423764364388316116026493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52565019152517754821368657 39423764364388316116026493)
      ·
        refine ⟨14783911636645618543509935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39423764364388316116026493 14783911636645618543509935)
        ·
          refine ⟨22175867454968427815264903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14783911636645618543509935 22175867454968427815264903)
          ·
            refine ⟨33263801182452641722897355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22175867454968427815264903 33263801182452641722897355)
            ·
              refine ⟨49895701773678962584346033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33263801182452641722897355 49895701773678962584346033)
              ·
                refine ⟨37421776330259221938259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49895701773678962584346033 37421776330259221938259525)
                ·
                  refine ⟨7016583061923604113423661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37421776330259221938259525 7016583061923604113423661)
                  ·
                    refine ⟨2631218648221351542533873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7016583061923604113423661 2631218648221351542533873)
                    ·
                      refine ⟨1973413986166013656900405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631218648221351542533873 1973413986166013656900405)
                      ·
                        rfl

theorem cell23_3843210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_3843210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843210 prefixEnd_3843210 := by exact prefixLift 3843210
  have htrace : WordTrace (prefixWord ++ tailWord_3843210) baseStart_3843210 baseEnd_3843210 := by
    simpa [prefixWord, tailWord_3843210, baseEnd_3843210] using wordTrace_append hprefix tailTrace_3843210
  have hstable : (prefixWord ++ tailWord_3843210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843210).length < 2 ^ (prefixWord ++ tailWord_3843210).sum := by decide
  have hdescent : baseEnd_3843210 < baseStart_3843210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843233 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3843233 : Nat := 118140960795 + 3843233 * 2 ^ 59
def prefixEnd_3843233 : Nat := 4983230072969 + 3 ^ 40 * 3843233 * 2
def baseEnd_3843233 : Nat := 657808598740355688970933

theorem tailTrace_3843233 : CollatzResearch.WordTrace tailWord_3843233 prefixEnd_3843233 657808598740355688970933 := by
  unfold tailWord_3843233
  simp only [CollatzResearch.WordTrace]
  refine ⟨140174223285630687785070353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93449482190420458523380235 140174223285630687785070353)
  ·
    refine ⟨105130667464223015838802765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140174223285630687785070353 105130667464223015838802765)
    ·
      refine ⟨39424000299083630939551037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105130667464223015838802765 39424000299083630939551037)
      ·
        refine ⟨14784000112156361602331639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39424000299083630939551037 14784000112156361602331639)
        ·
          refine ⟨22176000168234542403497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784000112156361602331639 22176000168234542403497459)
          ·
            refine ⟨33264000252351813605246189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22176000168234542403497459 33264000252351813605246189)
            ·
              refine ⟨12474000094631930101967321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33264000252351813605246189 12474000094631930101967321)
              ·
                refine ⟨9355500070973947576475491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474000094631930101967321 9355500070973947576475491)
                ·
                  refine ⟨14033250106460921364713237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355500070973947576475491 14033250106460921364713237)
                  ·
                    refine ⟨657808598740355688970933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14033250106460921364713237 657808598740355688970933)
                    ·
                      rfl

theorem cell23_3843233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3843233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843233 prefixEnd_3843233 := by exact prefixLift 3843233
  have htrace : WordTrace (prefixWord ++ tailWord_3843233) baseStart_3843233 baseEnd_3843233 := by
    simpa [prefixWord, tailWord_3843233, baseEnd_3843233] using wordTrace_append hprefix tailTrace_3843233
  have hstable : (prefixWord ++ tailWord_3843233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843233).length < 2 ^ (prefixWord ++ tailWord_3843233).sum := by decide
  have hdescent : baseEnd_3843233 < baseStart_3843233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843250 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3843250 : Nat := 118140960795 + 3843250 * 2 ^ 59
def prefixEnd_3843250 : Nat := 4983230072969 + 3 ^ 40 * 3843250 * 2
def baseEnd_3843250 : Nat := 657811508464064500133407

theorem tailTrace_3843250 : CollatzResearch.WordTrace tailWord_3843250 prefixEnd_3843250 657811508464064500133407 := by
  unfold tailWord_3843250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043710831642274922109801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93449895551046066458959469 35043710831642274922109801)
  ·
    refine ⟨26282783123731706191582351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35043710831642274922109801 26282783123731706191582351)
    ·
      refine ⟨39424174685597559287373527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26282783123731706191582351 39424174685597559287373527)
      ·
        refine ⟨59136262028396338931060291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39424174685597559287373527 59136262028396338931060291)
        ·
          refine ⟨88704393042594508396590437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59136262028396338931060291 88704393042594508396590437)
          ·
            refine ⟨16632073695486470324360707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88704393042594508396590437 16632073695486470324360707)
            ·
              refine ⟨24948110543229705486541061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632073695486470324360707 24948110543229705486541061)
              ·
                refine ⟨4677770726855569778726449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24948110543229705486541061 4677770726855569778726449)
                ·
                  refine ⟨3508328045141677334044837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677770726855569778726449 3508328045141677334044837)
                  ·
                    refine ⟨657811508464064500133407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508328045141677334044837 657811508464064500133407)
                    ·
                      rfl

theorem cell23_3843250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3843250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843250 prefixEnd_3843250 := by exact prefixLift 3843250
  have htrace : WordTrace (prefixWord ++ tailWord_3843250) baseStart_3843250 baseEnd_3843250 := by
    simpa [prefixWord, tailWord_3843250, baseEnd_3843250] using wordTrace_append hprefix tailTrace_3843250
  have hstable : (prefixWord ++ tailWord_3843250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843250).length < 2 ^ (prefixWord ++ tailWord_3843250).sum := by decide
  have hdescent : baseEnd_3843250 < baseStart_3843250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843256 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_3843256 : Nat := 118140960795 + 3843256 * 2 ^ 59
def prefixEnd_3843256 : Nat := 4983230072969 + 3 ^ 40 * 3843256 * 2
def baseEnd_3843256 : Nat := 1973437606276120476925193

theorem tailTrace_3843256 : CollatzResearch.WordTrace tailWord_3843256 prefixEnd_3843256 1973437606276120476925193 := by
  unfold tailWord_3843256
  simp only [CollatzResearch.WordTrace]
  refine ⟨70087531082273681356578811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93450041443031575142105081 70087531082273681356578811)
  ·
    refine ⟨105131296623410522034868217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70087531082273681356578811 105131296623410522034868217)
    ·
      refine ⟨78848472467557891526151163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105131296623410522034868217 78848472467557891526151163)
      ·
        refine ⟨118272708701336837289226745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78848472467557891526151163 118272708701336837289226745)
        ·
          refine ⟨88704531526002627966920059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118272708701336837289226745 88704531526002627966920059)
          ·
            refine ⟨133056797289003941950380089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88704531526002627966920059 133056797289003941950380089)
            ·
              refine ⟨99792597966752956462785067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133056797289003941950380089 99792597966752956462785067)
              ·
                refine ⟨149688896950129434694177601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99792597966752956462785067 149688896950129434694177601)
                ·
                  refine ⟨112266672712597076020633201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149688896950129434694177601 112266672712597076020633201)
                  ·
                    refine ⟨84200004534447807015474901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112266672712597076020633201 84200004534447807015474901)
                    ·
                      refine ⟨1973437606276120476925193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84200004534447807015474901 1973437606276120476925193)
                      ·
                        rfl

theorem cell23_3843256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_3843256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843256 prefixEnd_3843256 := by exact prefixLift 3843256
  have htrace : WordTrace (prefixWord ++ tailWord_3843256) baseStart_3843256 baseEnd_3843256 := by
    simpa [prefixWord, tailWord_3843256, baseEnd_3843256] using wordTrace_append hprefix tailTrace_3843256
  have hstable : (prefixWord ++ tailWord_3843256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843256).length < 2 ^ (prefixWord ++ tailWord_3843256).sum := by decide
  have hdescent : baseEnd_3843256 < baseStart_3843256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843260 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3843260 : Nat := 118140960795 + 3843260 * 2 ^ 59
def prefixEnd_3843260 : Nat := 4983230072969 + 3 ^ 40 * 3843260 * 2
def baseEnd_3843260 : Nat := 1973439660198738461275175

theorem tailTrace_3843260 : CollatzResearch.WordTrace tailWord_3843260 prefixEnd_3843260 1973439660198738461275175 := by
  unfold tailWord_3843260
  simp only [CollatzResearch.WordTrace]
  refine ⟨70087604028266435698151617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93450138704355247597535489 70087604028266435698151617)
  ·
    refine ⟨52565703021199826773613713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70087604028266435698151617 52565703021199826773613713)
    ·
      refine ⟨39424277265899870080210285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52565703021199826773613713 39424277265899870080210285)
      ·
        refine ⟨14784103974712451280078857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39424277265899870080210285 14784103974712451280078857)
        ·
          refine ⟨11088077981034338460059143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14784103974712451280078857 11088077981034338460059143)
          ·
            refine ⟨16632116971551507690088715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088077981034338460059143 16632116971551507690088715)
            ·
              refine ⟨24948175457327261535133073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632116971551507690088715 24948175457327261535133073)
              ·
                refine ⟨18711131592995446151349805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24948175457327261535133073 18711131592995446151349805)
                ·
                  refine ⟨7016674347373292306756177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18711131592995446151349805 7016674347373292306756177)
                  ·
                    refine ⟨5262505760529969230067133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7016674347373292306756177 5262505760529969230067133)
                    ·
                      refine ⟨1973439660198738461275175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262505760529969230067133 1973439660198738461275175)
                      ·
                        rfl

theorem cell23_3843260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3843260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843260 prefixEnd_3843260 := by exact prefixLift 3843260
  have htrace : WordTrace (prefixWord ++ tailWord_3843260) baseStart_3843260 baseEnd_3843260 := by
    simpa [prefixWord, tailWord_3843260, baseEnd_3843260] using wordTrace_append hprefix tailTrace_3843260
  have hstable : (prefixWord ++ tailWord_3843260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843260).length < 2 ^ (prefixWord ++ tailWord_3843260).sum := by decide
  have hdescent : baseEnd_3843260 < baseStart_3843260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843290 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_3843290 : Nat := 118140960795 + 3843290 * 2 ^ 59
def prefixEnd_3843290 : Nat := 4983230072969 + 3 ^ 40 * 3843290 * 2
def baseEnd_3843290 : Nat := 1973455064618373343900037

theorem tailTrace_3843290 : CollatzResearch.WordTrace tailWord_3843290 prefixEnd_3843290 1973455064618373343900037 := by
  unfold tailWord_3843290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35044075561606046629973831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93450868164282791013263549 35044075561606046629973831)
  ·
    refine ⟨52566113342409069944960747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35044075561606046629973831 52566113342409069944960747)
    ·
      refine ⟨78849170013613604917441121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52566113342409069944960747 78849170013613604917441121)
      ·
        refine ⟨59136877510210203688080841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78849170013613604917441121 59136877510210203688080841)
        ·
          refine ⟨44352658132657652766060631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59136877510210203688080841 44352658132657652766060631)
          ·
            refine ⟨66528987198986479149090947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44352658132657652766060631 66528987198986479149090947)
            ·
              refine ⟨99793480798479718723636421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66528987198986479149090947 99793480798479718723636421)
              ·
                refine ⟨18711277649714947260681829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99793480798479718723636421 18711277649714947260681829)
                ·
                  refine ⟨3508364559321552611377843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18711277649714947260681829 3508364559321552611377843)
                  ·
                    refine ⟨5262546838982328917066765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508364559321552611377843 5262546838982328917066765)
                    ·
                      refine ⟨1973455064618373343900037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262546838982328917066765 1973455064618373343900037)
                      ·
                        rfl

theorem cell23_3843290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_3843290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843290 prefixEnd_3843290 := by exact prefixLift 3843290
  have htrace : WordTrace (prefixWord ++ tailWord_3843290) baseStart_3843290 baseEnd_3843290 := by
    simpa [prefixWord, tailWord_3843290, baseEnd_3843290] using wordTrace_append hprefix tailTrace_3843290
  have hstable : (prefixWord ++ tailWord_3843290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843290).length < 2 ^ (prefixWord ++ tailWord_3843290).sum := by decide
  have hdescent : baseEnd_3843290 < baseStart_3843290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843307 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 3]
def baseStart_3843307 : Nat := 118140960795 + 3843307 * 2 ^ 59
def prefixEnd_3843307 : Nat := 4983230072969 + 3 ^ 40 * 3843307 * 2
def baseEnd_3843307 : Nat := 1973463793789499777387459

theorem tailTrace_3843307 : CollatzResearch.WordTrace tailWord_3843307 prefixEnd_3843307 1973463793789499777387459 := by
  unfold tailWord_3843307
  simp only [CollatzResearch.WordTrace]
  refine ⟨140176922287362598423264175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93451281524908398948842783 140176922287362598423264175)
  ·
    refine ⟨210265383431043897634896263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140176922287362598423264175 210265383431043897634896263)
    ·
      refine ⟨315398075146565846452344395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210265383431043897634896263 315398075146565846452344395)
      ·
        refine ⟨473097112719848769678516593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315398075146565846452344395 473097112719848769678516593)
        ·
          refine ⟨354822834539886577258887445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473097112719848769678516593 354822834539886577258887445)
          ·
            refine ⟨16632320369057183309010349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 354822834539886577258887445 16632320369057183309010349)
            ·
              refine ⟨6237120138396443740878881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16632320369057183309010349 6237120138396443740878881)
              ·
                refine ⟨4677840103797332805659161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6237120138396443740878881 4677840103797332805659161)
                ·
                  refine ⟨3508380077847999604244371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677840103797332805659161 3508380077847999604244371)
                  ·
                    refine ⟨5262570116771999406366557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508380077847999604244371 5262570116771999406366557)
                    ·
                      refine ⟨1973463793789499777387459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262570116771999406366557 1973463793789499777387459)
                      ·
                        rfl

theorem cell23_3843307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 3].length) (baseStart_3843307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843307 prefixEnd_3843307 := by exact prefixLift 3843307
  have htrace : WordTrace (prefixWord ++ tailWord_3843307) baseStart_3843307 baseEnd_3843307 := by
    simpa [prefixWord, tailWord_3843307, baseEnd_3843307] using wordTrace_append hprefix tailTrace_3843307
  have hstable : (prefixWord ++ tailWord_3843307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843307).length < 2 ^ (prefixWord ++ tailWord_3843307).sum := by decide
  have hdescent : baseEnd_3843307 < baseStart_3843307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843324 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_3843324 : Nat := 118140960795 + 3843324 * 2 ^ 59
def prefixEnd_3843324 : Nat := 4983230072969 + 3 ^ 40 * 3843324 * 2
def baseEnd_3843324 : Nat := 1973472522960626210874881

theorem tailTrace_3843324 : CollatzResearch.WordTrace tailWord_3843324 prefixEnd_3843324 1973472522960626210874881 := by
  unfold tailWord_3843324
  simp only [CollatzResearch.WordTrace]
  refine ⟨70088771164150505163316513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93451694885534006884422017 70088771164150505163316513)
  ·
    refine ⟨52566578373112878872487385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70088771164150505163316513 52566578373112878872487385)
    ·
      refine ⟨39424933779834659154365539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52566578373112878872487385 39424933779834659154365539)
      ·
        refine ⟨59137400669751988731548309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39424933779834659154365539 59137400669751988731548309)
        ·
          refine ⟨2772065656394624471791327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59137400669751988731548309 2772065656394624471791327)
          ·
            refine ⟨4158098484591936707686991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772065656394624471791327 4158098484591936707686991)
            ·
              refine ⟨6237147726887905061530487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158098484591936707686991 6237147726887905061530487)
              ·
                refine ⟨9355721590331857592295731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237147726887905061530487 9355721590331857592295731)
                ·
                  refine ⟨14033582385497786388443597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355721590331857592295731 14033582385497786388443597)
                  ·
                    refine ⟨5262593394561669895666349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14033582385497786388443597 5262593394561669895666349)
                    ·
                      refine ⟨1973472522960626210874881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262593394561669895666349 1973472522960626210874881)
                      ·
                        rfl

theorem cell23_3843324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_3843324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843324 prefixEnd_3843324 := by exact prefixLift 3843324
  have htrace : WordTrace (prefixWord ++ tailWord_3843324) baseStart_3843324 baseEnd_3843324 := by
    simpa [prefixWord, tailWord_3843324, baseEnd_3843324] using wordTrace_append hprefix tailTrace_3843324
  have hstable : (prefixWord ++ tailWord_3843324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843324).length < 2 ^ (prefixWord ++ tailWord_3843324).sum := by decide
  have hdescent : baseEnd_3843324 < baseStart_3843324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843333 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3843333 : Nat := 118140960795 + 3843333 * 2 ^ 59
def prefixEnd_3843333 : Nat := 4983230072969 + 3 ^ 40 * 3843333 * 2
def baseEnd_3843333 : Nat := 1973477144286516675662339

theorem tailTrace_3843333 : CollatzResearch.WordTrace tailWord_3843333 prefixEnd_3843333 1973477144286516675662339 := by
  unfold tailWord_3843333
  simp only [CollatzResearch.WordTrace]
  refine ⟨140177870585268404863710653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93451913723512269909140435 140177870585268404863710653)
  ·
    refine ⟨52566701469475651823891495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140177870585268404863710653 52566701469475651823891495)
    ·
      refine ⟨78850052204213477735837243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52566701469475651823891495 78850052204213477735837243)
      ·
        refine ⟨118275078306320216603755865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78850052204213477735837243 118275078306320216603755865)
        ·
          refine ⟨88706308729740162452816899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118275078306320216603755865 88706308729740162452816899)
          ·
            refine ⟨133059463094610243679225349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88706308729740162452816899 133059463094610243679225349)
            ·
              refine ⟨24948649330239420689854753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133059463094610243679225349 24948649330239420689854753)
              ·
                refine ⟨18711486997679565517391065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24948649330239420689854753 18711486997679565517391065)
                ·
                  refine ⟨14033615248259674138043299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18711486997679565517391065 14033615248259674138043299)
                  ·
                    refine ⟨21050422872389511207064949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14033615248259674138043299 21050422872389511207064949)
                    ·
                      refine ⟨1973477144286516675662339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21050422872389511207064949 1973477144286516675662339)
                      ·
                        rfl

theorem cell23_3843333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3843333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843333 prefixEnd_3843333 := by exact prefixLift 3843333
  have htrace : WordTrace (prefixWord ++ tailWord_3843333) baseStart_3843333 baseEnd_3843333 := by
    simpa [prefixWord, tailWord_3843333, baseEnd_3843333] using wordTrace_append hprefix tailTrace_3843333
  have hstable : (prefixWord ++ tailWord_3843333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843333).length < 2 ^ (prefixWord ++ tailWord_3843333).sum := by decide
  have hdescent : baseEnd_3843333 < baseStart_3843333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843364 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_3843364 : Nat := 118140960795 + 3843364 * 2 ^ 59
def prefixEnd_3843364 : Nat := 4983230072969 + 3 ^ 40 * 3843364 * 2
def baseEnd_3843364 : Nat := 1973493062186806054374697

theorem tailTrace_3843364 : CollatzResearch.WordTrace tailWord_3843364 prefixEnd_3843364 1973493062186806054374697 := by
  unfold tailWord_3843364
  simp only [CollatzResearch.WordTrace]
  refine ⟨70089500624078048579044573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93452667498770731438726097 70089500624078048579044573)
  ·
    refine ⟨26283562734029268217141715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70089500624078048579044573 26283562734029268217141715)
    ·
      refine ⟨39425344101043902325712573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26283562734029268217141715 39425344101043902325712573)
      ·
        refine ⟨14784504037891463372142215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39425344101043902325712573 14784504037891463372142215)
        ·
          refine ⟨22176756056837195058213323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784504037891463372142215 22176756056837195058213323)
          ·
            refine ⟨33265134085255792587319985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22176756056837195058213323 33265134085255792587319985)
            ·
              refine ⟨24948850563941844440489989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33265134085255792587319985 24948850563941844440489989)
              ·
                refine ⟨4677909480739095832591873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24948850563941844440489989 4677909480739095832591873)
                ·
                  refine ⟨3508432110554321874443905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677909480739095832591873 3508432110554321874443905)
                  ·
                    refine ⟨2631324082915741405832929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3508432110554321874443905 2631324082915741405832929)
                    ·
                      refine ⟨1973493062186806054374697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631324082915741405832929 1973493062186806054374697)
                      ·
                        rfl

theorem cell23_3843364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_3843364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843364 prefixEnd_3843364 := by exact prefixLift 3843364
  have htrace : WordTrace (prefixWord ++ tailWord_3843364) baseStart_3843364 baseEnd_3843364 := by
    simpa [prefixWord, tailWord_3843364, baseEnd_3843364] using wordTrace_append hprefix tailTrace_3843364
  have hstable : (prefixWord ++ tailWord_3843364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843364).length < 2 ^ (prefixWord ++ tailWord_3843364).sum := by decide
  have hdescent : baseEnd_3843364 < baseStart_3843364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843381 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_3843381 : Nat := 118140960795 + 3843381 * 2 ^ 59
def prefixEnd_3843381 : Nat := 4983230072969 + 3 ^ 40 * 3843381 * 2
def baseEnd_3843381 : Nat := 1973501791357932487862119

theorem tailTrace_3843381 : CollatzResearch.WordTrace tailWord_3843381 prefixEnd_3843381 1973501791357932487862119 := by
  unfold tailWord_3843381
  simp only [CollatzResearch.WordTrace]
  refine ⟨140179621289094509061457997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93453080859396339374305331 140179621289094509061457997)
  ·
    refine ⟨52567357983410440898046749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140179621289094509061457997 52567357983410440898046749)
    ·
      refine ⟨19712759243778915336767531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52567357983410440898046749 19712759243778915336767531)
      ·
        refine ⟨29569138865668373005151297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19712759243778915336767531 29569138865668373005151297)
        ·
          refine ⟨22176854149251279753863473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29569138865668373005151297 22176854149251279753863473)
          ·
            refine ⟨16632640611938459815397605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22176854149251279753863473 16632640611938459815397605)
            ·
              refine ⟨3118620114738461215387051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16632640611938459815397605 3118620114738461215387051)
              ·
                refine ⟨4677930172107691823080577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118620114738461215387051 4677930172107691823080577)
                ·
                  refine ⟨3508447629080768867310433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677930172107691823080577 3508447629080768867310433)
                  ·
                    refine ⟨2631335721810576650482825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3508447629080768867310433 2631335721810576650482825)
                    ·
                      refine ⟨1973501791357932487862119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631335721810576650482825 1973501791357932487862119)
                      ·
                        rfl

theorem cell23_3843381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_3843381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843381 prefixEnd_3843381 := by exact prefixLift 3843381
  have htrace : WordTrace (prefixWord ++ tailWord_3843381) baseStart_3843381 baseEnd_3843381 := by
    simpa [prefixWord, tailWord_3843381, baseEnd_3843381] using wordTrace_append hprefix tailTrace_3843381
  have hstable : (prefixWord ++ tailWord_3843381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843381).length < 2 ^ (prefixWord ++ tailWord_3843381).sum := by decide
  have hdescent : baseEnd_3843381 < baseStart_3843381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843398 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3843398 : Nat := 118140960795 + 3843398 * 2 ^ 59
def prefixEnd_3843398 : Nat := 4983230072969 + 3 ^ 40 * 3843398 * 2
def baseEnd_3843398 : Nat := 1973510520529058921349541

theorem tailTrace_3843398 : CollatzResearch.WordTrace tailWord_3843398 prefixEnd_3843398 1973510520529058921349541 := by
  unfold tailWord_3843398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380632541563528780150839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93453494220021947309884565 4380632541563528780150839)
  ·
    refine ⟨6570948812345293170226259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380632541563528780150839 6570948812345293170226259)
    ·
      refine ⟨9856423218517939755339389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570948812345293170226259 9856423218517939755339389)
      ·
        refine ⟨3696158706944227408252271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9856423218517939755339389 3696158706944227408252271)
        ·
          refine ⟨5544238060416341112378407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696158706944227408252271 5544238060416341112378407)
          ·
            refine ⟨8316357090624511668567611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544238060416341112378407 8316357090624511668567611)
            ·
              refine ⟨12474535635936767502851417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316357090624511668567611 12474535635936767502851417)
              ·
                refine ⟨9355901726952575627138563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474535635936767502851417 9355901726952575627138563)
                ·
                  refine ⟨14033852590428863440707845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355901726952575627138563 14033852590428863440707845)
                  ·
                    refine ⟨2631347360705411895132721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14033852590428863440707845 2631347360705411895132721)
                    ·
                      refine ⟨1973510520529058921349541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631347360705411895132721 1973510520529058921349541)
                      ·
                        rfl

theorem cell23_3843398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3843398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843398 prefixEnd_3843398 := by exact prefixLift 3843398
  have htrace : WordTrace (prefixWord ++ tailWord_3843398) baseStart_3843398 baseEnd_3843398 := by
    simpa [prefixWord, tailWord_3843398, baseEnd_3843398] using wordTrace_append hprefix tailTrace_3843398
  have hstable : (prefixWord ++ tailWord_3843398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843398).length < 2 ^ (prefixWord ++ tailWord_3843398).sum := by decide
  have hdescent : baseEnd_3843398 < baseStart_3843398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843403 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_3843403 : Nat := 118140960795 + 3843403 * 2 ^ 59
def prefixEnd_3843403 : Nat := 4983230072969 + 3 ^ 40 * 3843403 * 2
def baseEnd_3843403 : Nat := 1973513087932331401787017

theorem tailTrace_3843403 : CollatzResearch.WordTrace tailWord_3843403 prefixEnd_3843403 1973513087932331401787017 := by
  unfold tailWord_3843403
  simp only [CollatzResearch.WordTrace]
  refine ⟨140180423695014806818758863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93453615796676537879172575 140180423695014806818758863)
  ·
    refine ⟨210270635542522210228138295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140180423695014806818758863 210270635542522210228138295)
    ·
      refine ⟨315405953313783315342207443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210270635542522210228138295 315405953313783315342207443)
      ·
        refine ⟨473108929970674973013311165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315405953313783315342207443 473108929970674973013311165)
        ·
          refine ⟨177415848739003114879991687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473108929970674973013311165 177415848739003114879991687)
          ·
            refine ⟨266123773108504672319987531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177415848739003114879991687 266123773108504672319987531)
            ·
              refine ⟨399185659662757008479981297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266123773108504672319987531 399185659662757008479981297)
              ·
                refine ⟨299389244747067756359985973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399185659662757008479981297 299389244747067756359985973)
                ·
                  refine ⟨28067741695037602158748685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299389244747067756359985973 28067741695037602158748685)
                  ·
                    refine ⟨10525403135639100809530757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28067741695037602158748685 10525403135639100809530757)
                    ·
                      refine ⟨1973513087932331401787017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10525403135639100809530757 1973513087932331401787017)
                      ·
                        rfl

theorem cell23_3843403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_3843403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843403 prefixEnd_3843403 := by exact prefixLift 3843403
  have htrace : WordTrace (prefixWord ++ tailWord_3843403) baseStart_3843403 baseEnd_3843403 := by
    simpa [prefixWord, tailWord_3843403, baseEnd_3843403] using wordTrace_append hprefix tailTrace_3843403
  have hstable : (prefixWord ++ tailWord_3843403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843403).length < 2 ^ (prefixWord ++ tailWord_3843403).sum := by decide
  have hdescent : baseEnd_3843403 < baseStart_3843403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843423 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3843423 : Nat := 118140960795 + 3843423 * 2 ^ 59
def prefixEnd_3843423 : Nat := 4983230072969 + 3 ^ 40 * 3843423 * 2
def baseEnd_3843423 : Nat := 1973523357545421323536925

theorem tailTrace_3843423 : CollatzResearch.WordTrace tailWord_3843423 prefixEnd_3843423 1973523357545421323536925 := by
  unfold tailWord_3843423
  simp only [CollatzResearch.WordTrace]
  refine ⟨140181153154942350234486923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93454102103294900156324615 140181153154942350234486923)
  ·
    refine ⟨210271729732413525351730385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140181153154942350234486923 210271729732413525351730385)
    ·
      refine ⟨157703797299310144013797789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210271729732413525351730385 157703797299310144013797789)
      ·
        refine ⟨59138923987241304005174171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157703797299310144013797789 59138923987241304005174171)
        ·
          refine ⟨88708385980861956007761257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59138923987241304005174171 88708385980861956007761257)
          ·
            refine ⟨66531289485646467005820943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88708385980861956007761257 66531289485646467005820943)
            ·
              refine ⟨99796934228469700508731415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66531289485646467005820943 99796934228469700508731415)
              ·
                refine ⟨149695401342704550763097123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99796934228469700508731415 149695401342704550763097123)
                ·
                  refine ⟨224543102014056826144645685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149695401342704550763097123 224543102014056826144645685)
                  ·
                    refine ⟨21050915813817827451060533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224543102014056826144645685 21050915813817827451060533)
                    ·
                      refine ⟨1973523357545421323536925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21050915813817827451060533 1973523357545421323536925)
                      ·
                        rfl

theorem cell23_3843423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3843423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843423 prefixEnd_3843423 := by exact prefixLift 3843423
  have htrace : WordTrace (prefixWord ++ tailWord_3843423) baseStart_3843423 baseEnd_3843423 := by
    simpa [prefixWord, tailWord_3843423, baseEnd_3843423] using wordTrace_append hprefix tailTrace_3843423
  have hstable : (prefixWord ++ tailWord_3843423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843423).length < 2 ^ (prefixWord ++ tailWord_3843423).sum := by decide
  have hdescent : baseEnd_3843423 < baseStart_3843423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843433 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_3843433 : Nat := 118140960795 + 3843433 * 2 ^ 59
def prefixEnd_3843433 : Nat := 4983230072969 + 3 ^ 40 * 3843433 * 2
def baseEnd_3843433 : Nat := 1973528492351966284411879

theorem tailTrace_3843433 : CollatzResearch.WordTrace tailWord_3843433 prefixEnd_3843433 1973528492351966284411879 := by
  unfold tailWord_3843433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140181517884906121942350953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93454345256604081294900635 140181517884906121942350953)
  ·
    refine ⟨105136138413679591456763215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140181517884906121942350953 105136138413679591456763215)
    ·
      refine ⟨157704207620519387185144823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105136138413679591456763215 157704207620519387185144823)
      ·
        refine ⟨236556311430779080777717235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157704207620519387185144823 236556311430779080777717235)
        ·
          refine ⟨354834467146168621166575853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236556311430779080777717235 354834467146168621166575853)
          ·
            refine ⟨133062925179813232937465945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354834467146168621166575853 133062925179813232937465945)
            ·
              refine ⟨99797193884859924703099459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133062925179813232937465945 99797193884859924703099459)
              ·
                refine ⟨149695790827289887054649189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99797193884859924703099459 149695790827289887054649189)
                ·
                  refine ⟨28067960780116853822746723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149695790827289887054649189 28067960780116853822746723)
                  ·
                    refine ⟨42101941170175280734120085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28067960780116853822746723 42101941170175280734120085)
                    ·
                      refine ⟨1973528492351966284411879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42101941170175280734120085 1973528492351966284411879)
                      ·
                        rfl

theorem cell23_3843433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_3843433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843433 prefixEnd_3843433 := by exact prefixLift 3843433
  have htrace : WordTrace (prefixWord ++ tailWord_3843433) baseStart_3843433 baseEnd_3843433 := by
    simpa [prefixWord, tailWord_3843433, baseEnd_3843433] using wordTrace_append hprefix tailTrace_3843433
  have hstable : (prefixWord ++ tailWord_3843433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843433).length < 2 ^ (prefixWord ++ tailWord_3843433).sum := by decide
  have hdescent : baseEnd_3843433 < baseStart_3843433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
