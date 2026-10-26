import V185TrunkScan23Chunk1003

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5945233 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_5945233 : Nat := 118140960795 + 5945233 * 2 ^ 59
def prefixEnd_5945233 : Nat := 4983230072969 + 3 ^ 40 * 5945233 * 2
def baseEnd_5945233 : Nat := 3052762131971842982245877

theorem tailTrace_5945233 : CollatzResearch.WordTrace tailWord_5945233 prefixEnd_5945233 3052762131971842982245877 := by
  unfold tailWord_5945233
  simp only [CollatzResearch.WordTrace]
  refine ⟨216840461670443680804176353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144560307780295787202784235 216840461670443680804176353)
  ·
    refine ⟨162630346252832760603132265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216840461670443680804176353 162630346252832760603132265)
    ·
      refine ⟨121972759689624570452349199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162630346252832760603132265 121972759689624570452349199)
      ·
        refine ⟨182959139534436855678523799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121972759689624570452349199 182959139534436855678523799)
        ·
          refine ⟨274438709301655283517785699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182959139534436855678523799 274438709301655283517785699)
          ·
            refine ⟨411658063952482925276678549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274438709301655283517785699 411658063952482925276678549)
            ·
              refine ⟨19296471747772637122344307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411658063952482925276678549 19296471747772637122344307)
              ·
                refine ⟨28944707621658955683516461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19296471747772637122344307 28944707621658955683516461)
                ·
                  refine ⟨10854265358122108381318673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28944707621658955683516461 10854265358122108381318673)
                  ·
                    refine ⟨8140699018591581285989005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10854265358122108381318673 8140699018591581285989005)
                    ·
                      refine ⟨3052762131971842982245877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8140699018591581285989005 3052762131971842982245877)
                      ·
                        rfl

theorem cell23_5945233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_5945233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945233 prefixEnd_5945233 := by exact prefixLift 5945233
  have htrace : WordTrace (prefixWord ++ tailWord_5945233) baseStart_5945233 baseEnd_5945233 := by
    simpa [prefixWord, tailWord_5945233, baseEnd_5945233] using wordTrace_append hprefix tailTrace_5945233
  have hstable : (prefixWord ++ tailWord_5945233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945233).length < 2 ^ (prefixWord ++ tailWord_5945233).sum := by decide
  have hdescent : baseEnd_5945233 < baseStart_5945233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945234 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5945234 : Nat := 118140960795 + 5945234 * 2 ^ 59
def prefixEnd_5945234 : Nat := 4983230072969 + 3 ^ 40 * 5945234 * 2
def baseEnd_5945234 : Nat := 3052762645452497478333373

theorem tailTrace_5945234 : CollatzResearch.WordTrace tailWord_5945234 prefixEnd_5945234 3052762645452497478333373 := by
  unfold tailWord_5945234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210124535860014493740689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144560332095626705316641837 54210124535860014493740689)
  ·
    refine ⟨40657593401895010870305517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54210124535860014493740689 40657593401895010870305517)
    ·
      refine ⟨15246597525710629076364569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40657593401895010870305517 15246597525710629076364569)
      ·
        refine ⟨11434948144282971807273427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15246597525710629076364569 11434948144282971807273427)
        ·
          refine ⟨17152422216424457710910141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11434948144282971807273427 17152422216424457710910141)
          ·
            refine ⟨6432158331159171641591303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17152422216424457710910141 6432158331159171641591303)
            ·
              refine ⟨9648237496738757462386955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432158331159171641591303 9648237496738757462386955)
              ·
                refine ⟨14472356245108136193580433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9648237496738757462386955 14472356245108136193580433)
                ·
                  refine ⟨10854267183831102145185325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14472356245108136193580433 10854267183831102145185325)
                  ·
                    refine ⟨4070350193936663304444497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10854267183831102145185325 4070350193936663304444497)
                    ·
                      refine ⟨3052762645452497478333373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070350193936663304444497 3052762645452497478333373)
                      ·
                        rfl

theorem cell23_5945234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5945234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945234 prefixEnd_5945234 := by exact prefixLift 5945234
  have htrace : WordTrace (prefixWord ++ tailWord_5945234) baseStart_5945234 baseEnd_5945234 := by
    simpa [prefixWord, tailWord_5945234, baseEnd_5945234] using wordTrace_append hprefix tailTrace_5945234
  have hstable : (prefixWord ++ tailWord_5945234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945234).length < 2 ^ (prefixWord ++ tailWord_5945234).sum := by decide
  have hdescent : baseEnd_5945234 < baseStart_5945234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945266 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_5945266 : Nat := 118140960795 + 5945266 * 2 ^ 59
def prefixEnd_5945266 : Nat := 4983230072969 + 3 ^ 40 * 5945266 * 2
def baseEnd_5945266 : Nat := 1017593025611147117711075

theorem tailTrace_5945266 : CollatzResearch.WordTrace tailWord_5945266 prefixEnd_5945266 1017593025611147117711075 := by
  unfold tailWord_5945266
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210416319831031860031913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144561110186216084960085101 54210416319831031860031913)
  ·
    refine ⟨40657812239873273895023935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54210416319831031860031913 40657812239873273895023935)
    ·
      refine ⟨60986718359809910842535903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40657812239873273895023935 60986718359809910842535903)
      ·
        refine ⟨91480077539714866263803855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60986718359809910842535903 91480077539714866263803855)
        ·
          refine ⟨137220116309572299395705783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91480077539714866263803855 137220116309572299395705783)
          ·
            refine ⟨205830174464358449093558675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137220116309572299395705783 205830174464358449093558675)
            ·
              refine ⟨308745261696537673640338013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205830174464358449093558675 308745261696537673640338013)
              ·
                refine ⟨115779473136201627615126755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308745261696537673640338013 115779473136201627615126755)
                ·
                  refine ⟨173669209704302441422690133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115779473136201627615126755 173669209704302441422690133)
                  ·
                    refine ⟨1017593025611147117711075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 173669209704302441422690133 1017593025611147117711075)
                    ·
                      rfl

theorem cell23_5945266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_5945266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945266 prefixEnd_5945266 := by exact prefixLift 5945266
  have htrace : WordTrace (prefixWord ++ tailWord_5945266) baseStart_5945266 baseEnd_5945266 := by
    simpa [prefixWord, tailWord_5945266, baseEnd_5945266] using wordTrace_append hprefix tailTrace_5945266
  have hstable : (prefixWord ++ tailWord_5945266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945266).length < 2 ^ (prefixWord ++ tailWord_5945266).sum := by decide
  have hdescent : baseEnd_5945266 < baseStart_5945266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945290 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_5945290 : Nat := 118140960795 + 5945290 * 2 ^ 59
def prefixEnd_5945290 : Nat := 4983230072969 + 3 ^ 40 * 5945290 * 2
def baseEnd_5945290 : Nat := 3052791400369149259233115

theorem tailTrace_5945290 : CollatzResearch.WordTrace tailWord_5945290 prefixEnd_5945290 3052791400369149259233115 := by
  unfold tailWord_5945290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210635157809294884750331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144561693754158119692667549 54210635157809294884750331)
  ·
    refine ⟨81315952736713942327125497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54210635157809294884750331 81315952736713942327125497)
    ·
      refine ⟨60986964552535456745344123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81315952736713942327125497 60986964552535456745344123)
      ·
        refine ⟨91480446828803185118016185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60986964552535456745344123 91480446828803185118016185)
        ·
          refine ⟨68610335121602388838512139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91480446828803185118016185 68610335121602388838512139)
          ·
            refine ⟨102915502682403583257768209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68610335121602388838512139 102915502682403583257768209)
            ·
              refine ⟨77186627011802687443326157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102915502682403583257768209 77186627011802687443326157)
              ·
                refine ⟨28944985129426007791247309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77186627011802687443326157 28944985129426007791247309)
                ·
                  refine ⟨10854369423534752921717741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28944985129426007791247309 10854369423534752921717741)
                  ·
                    refine ⟨4070388533825532345644153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10854369423534752921717741 4070388533825532345644153)
                    ·
                      refine ⟨3052791400369149259233115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070388533825532345644153 3052791400369149259233115)
                      ·
                        rfl

theorem cell23_5945290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_5945290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945290 prefixEnd_5945290 := by exact prefixLift 5945290
  have htrace : WordTrace (prefixWord ++ tailWord_5945290) baseStart_5945290 baseEnd_5945290 := by
    simpa [prefixWord, tailWord_5945290, baseEnd_5945290] using wordTrace_append hprefix tailTrace_5945290
  have hstable : (prefixWord ++ tailWord_5945290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945290).length < 2 ^ (prefixWord ++ tailWord_5945290).sum := by decide
  have hdescent : baseEnd_5945290 < baseStart_5945290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945296 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_5945296 : Nat := 118140960795 + 5945296 * 2 ^ 59
def prefixEnd_5945296 : Nat := 4983230072969 + 3 ^ 40 * 5945296 * 2
def baseEnd_5945296 : Nat := 1017598160417692078586029

theorem tailTrace_5945296 : CollatzResearch.WordTrace tailWord_5945296 prefixEnd_5945296 1017598160417692078586029 := by
  unfold tailWord_5945296
  simp only [CollatzResearch.WordTrace]
  refine ⟨108421379734607721281859871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144561839646143628375813161 108421379734607721281859871)
  ·
    refine ⟨162632069601911581922789807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108421379734607721281859871 162632069601911581922789807)
    ·
      refine ⟨243948104402867372884184711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162632069601911581922789807 243948104402867372884184711)
      ·
        refine ⟨365922156604301059326277067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243948104402867372884184711 365922156604301059326277067)
        ·
          refine ⟨548883234906451588989415601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365922156604301059326277067 548883234906451588989415601)
          ·
            refine ⟨411662426179838691742061701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548883234906451588989415601 411662426179838691742061701)
            ·
              refine ⟨77186704908719754701636569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411662426179838691742061701 77186704908719754701636569)
              ·
                refine ⟨57890028681539816026227427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77186704908719754701636569 57890028681539816026227427)
                ·
                  refine ⟨86835043022309724039341141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57890028681539816026227427 86835043022309724039341141)
                  ·
                    refine ⟨1017598160417692078586029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86835043022309724039341141 1017598160417692078586029)
                    ·
                      rfl

theorem cell23_5945296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_5945296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945296 prefixEnd_5945296 := by exact prefixLift 5945296
  have htrace : WordTrace (prefixWord ++ tailWord_5945296) baseStart_5945296 baseEnd_5945296 := by
    simpa [prefixWord, tailWord_5945296, baseEnd_5945296] using wordTrace_append hprefix tailTrace_5945296
  have hstable : (prefixWord ++ tailWord_5945296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945296).length < 2 ^ (prefixWord ++ tailWord_5945296).sum := by decide
  have hdescent : baseEnd_5945296 < baseStart_5945296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945298 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5945298 : Nat := 118140960795 + 5945298 * 2 ^ 59
def prefixEnd_5945298 : Nat := 4983230072969 + 3 ^ 40 * 5945298 * 2
def baseEnd_5945298 : Nat := 3052795508214385227933079

theorem tailTrace_5945298 : CollatzResearch.WordTrace tailWord_5945298 prefixEnd_5945298 3052795508214385227933079 := by
  unfold tailWord_5945298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210708103802049226323137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144561888276805464603528365 54210708103802049226323137)
  ·
    refine ⟨40658031077851536919742353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54210708103802049226323137 40658031077851536919742353)
    ·
      refine ⟨30493523308388652689806765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40658031077851536919742353 30493523308388652689806765)
      ·
        refine ⟨11435071240645744758677537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30493523308388652689806765 11435071240645744758677537)
        ·
          refine ⟨8576303430484308569008153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11435071240645744758677537 8576303430484308569008153)
          ·
            refine ⟨6432227572863231426756115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8576303430484308569008153 6432227572863231426756115)
            ·
              refine ⟨9648341359294847140134173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432227572863231426756115 9648341359294847140134173)
              ·
                refine ⟨3618128009735567677550315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9648341359294847140134173 3618128009735567677550315)
                ·
                  refine ⟨5427192014603351516325473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618128009735567677550315 5427192014603351516325473)
                  ·
                    refine ⟨4070394010952513637244105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5427192014603351516325473 4070394010952513637244105)
                    ·
                      refine ⟨3052795508214385227933079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070394010952513637244105 3052795508214385227933079)
                      ·
                        rfl

theorem cell23_5945298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5945298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945298 prefixEnd_5945298 := by exact prefixLift 5945298
  have htrace : WordTrace (prefixWord ++ tailWord_5945298) baseStart_5945298 baseEnd_5945298 := by
    simpa [prefixWord, tailWord_5945298, baseEnd_5945298] using wordTrace_append hprefix tailTrace_5945298
  have hstable : (prefixWord ++ tailWord_5945298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945298).length < 2 ^ (prefixWord ++ tailWord_5945298).sum := by decide
  have hdescent : baseEnd_5945298 < baseStart_5945298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945353 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_5945353 : Nat := 118140960795 + 5945353 * 2 ^ 59
def prefixEnd_5945353 : Nat := 4983230072969 + 3 ^ 40 * 5945353 * 2
def baseEnd_5945353 : Nat := 3052823749650382512745325

theorem tailTrace_5945353 : CollatzResearch.WordTrace tailWord_5945353 prefixEnd_5945353 3052823749650382512745325 := by
  unfold tailWord_5945353
  simp only [CollatzResearch.WordTrace]
  refine ⟨216844838430008941298544713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144563225620005960865696475 216844838430008941298544713)
  ·
    refine ⟨162633628822506705973908535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216844838430008941298544713 162633628822506705973908535)
    ·
      refine ⟨243950443233760058960862803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162633628822506705973908535 243950443233760058960862803)
      ·
        refine ⟨365925664850640088441294205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243950443233760058960862803 365925664850640088441294205)
        ·
          refine ⟨137222124318990033165485327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365925664850640088441294205 137222124318990033165485327)
          ·
            refine ⟨205833186478485049748227991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137222124318990033165485327 205833186478485049748227991)
            ·
              refine ⟨308749779717727574622341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205833186478485049748227991 308749779717727574622341987)
              ·
                refine ⟨463124669576591361933512981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308749779717727574622341987 463124669576591361933512981)
                ·
                  refine ⟨21708968886402720090633421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 463124669576591361933512981 21708968886402720090633421)
                  ·
                    refine ⟨8140863332401020033987533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21708968886402720090633421 8140863332401020033987533)
                    ·
                      refine ⟨3052823749650382512745325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8140863332401020033987533 3052823749650382512745325)
                      ·
                        rfl

theorem cell23_5945353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_5945353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945353 prefixEnd_5945353 := by exact prefixLift 5945353
  have htrace : WordTrace (prefixWord ++ tailWord_5945353) baseStart_5945353 baseEnd_5945353 := by
    simpa [prefixWord, tailWord_5945353, baseEnd_5945353] using wordTrace_append hprefix tailTrace_5945353
  have hstable : (prefixWord ++ tailWord_5945353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945353).length < 2 ^ (prefixWord ++ tailWord_5945353).sum := by decide
  have hdescent : baseEnd_5945353 < baseStart_5945353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945377 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 5]
def baseStart_5945377 : Nat := 118140960795 + 5945377 * 2 ^ 59
def prefixEnd_5945377 : Nat := 4983230072969 + 3 ^ 40 * 5945377 * 2
def baseEnd_5945377 : Nat := 339204008131787824316135

theorem tailTrace_5945377 : CollatzResearch.WordTrace tailWord_5945377 prefixEnd_5945377 339204008131787824316135 := by
  unfold tailWord_5945377
  simp only [CollatzResearch.WordTrace]
  refine ⟨216845713781921993397418385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144563809187947995598278923 216845713781921993397418385)
  ·
    refine ⟨162634285336441495048063789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216845713781921993397418385 162634285336441495048063789)
    ·
      refine ⟨60987857001165560643023921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162634285336441495048063789 60987857001165560643023921)
      ·
        refine ⟨45740892750874170482267941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60987857001165560643023921 45740892750874170482267941)
        ·
          refine ⟨8576417390788906965425239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45740892750874170482267941 8576417390788906965425239)
          ·
            refine ⟨12864626086183360448137859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576417390788906965425239 12864626086183360448137859)
            ·
              refine ⟨19296939129275040672206789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12864626086183360448137859 19296939129275040672206789)
              ·
                refine ⟨3618176086739070126038773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19296939129275040672206789 3618176086739070126038773)
                ·
                  refine ⟨339204008131787824316135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3618176086739070126038773 339204008131787824316135)
                  ·
                    rfl

theorem cell23_5945377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 5].length) (baseStart_5945377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945377 prefixEnd_5945377 := by exact prefixLift 5945377
  have htrace : WordTrace (prefixWord ++ tailWord_5945377) baseStart_5945377 baseEnd_5945377 := by
    simpa [prefixWord, tailWord_5945377, baseEnd_5945377] using wordTrace_append hprefix tailTrace_5945377
  have hstable : (prefixWord ++ tailWord_5945377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945377).length < 2 ^ (prefixWord ++ tailWord_5945377).sum := by decide
  have hdescent : baseEnd_5945377 < baseStart_5945377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945433 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 8]
def baseStart_5945433 : Nat := 118140960795 + 5945433 * 2 ^ 59
def prefixEnd_5945433 : Nat := 4983230072969 + 3 ^ 40 * 5945433 * 2
def baseEnd_5945433 : Nat := 339207203122526911082773

theorem tailTrace_5945433 : CollatzResearch.WordTrace tailWord_5945433 prefixEnd_5945433 339207203122526911082773 := by
  unfold tailWord_5945433
  simp only [CollatzResearch.WordTrace]
  refine ⟨216847756269719114961456953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144565170846479409974304635 216847756269719114961456953)
  ·
    refine ⟨162635817202289336221092715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216847756269719114961456953 162635817202289336221092715)
    ·
      refine ⟨243953725803434004331639073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162635817202289336221092715 243953725803434004331639073)
      ·
        refine ⟨182965294352575503248729305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243953725803434004331639073 182965294352575503248729305)
        ·
          refine ⟨137223970764431627436546979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182965294352575503248729305 137223970764431627436546979)
          ·
            refine ⟨205835956146647441154820469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137223970764431627436546979 205835956146647441154820469)
            ·
              refine ⟨19297120888748197608264419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205835956146647441154820469 19297120888748197608264419)
              ·
                refine ⟨28945681333122296412396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19297120888748197608264419 28945681333122296412396629)
                ·
                  refine ⟨339207203122526911082773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28945681333122296412396629 339207203122526911082773)
                  ·
                    rfl

theorem cell23_5945433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_5945433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945433 prefixEnd_5945433 := by exact prefixLift 5945433
  have htrace : WordTrace (prefixWord ++ tailWord_5945433) baseStart_5945433 baseEnd_5945433 := by
    simpa [prefixWord, tailWord_5945433, baseEnd_5945433] using wordTrace_append hprefix tailTrace_5945433
  have hstable : (prefixWord ++ tailWord_5945433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945433).length < 2 ^ (prefixWord ++ tailWord_5945433).sum := by decide
  have hdescent : baseEnd_5945433 < baseStart_5945433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945514 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5945514 : Nat := 118140960795 + 5945514 * 2 ^ 59
def prefixEnd_5945514 : Nat := 4983230072969 + 3 ^ 40 * 5945514 * 2
def baseEnd_5945514 : Nat := 1017635473345252127610695

theorem tailTrace_5945514 : CollatzResearch.WordTrace tailWord_5945514 prefixEnd_5945514 1017635473345252127610695 := by
  unfold tailWord_5945514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54212677645606416448788899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144567140388283777196770397 54212677645606416448788899)
  ·
    refine ⟨81319016468409624673183349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54212677645606416448788899 81319016468409624673183349)
    ·
      refine ⟨7623657793913402313110939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81319016468409624673183349 7623657793913402313110939)
      ·
        refine ⟨11435486690870103469666409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7623657793913402313110939 11435486690870103469666409)
        ·
          refine ⟨8576615018152577602249807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11435486690870103469666409 8576615018152577602249807)
          ·
            refine ⟨12864922527228866403374711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576615018152577602249807 12864922527228866403374711)
            ·
              refine ⟨19297383790843299605062067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12864922527228866403374711 19297383790843299605062067)
              ·
                refine ⟨28946075686264949407593101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19297383790843299605062067 28946075686264949407593101)
                ·
                  refine ⟨10854778382349356027847413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28946075686264949407593101 10854778382349356027847413)
                  ·
                    refine ⟨1017635473345252127610695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10854778382349356027847413 1017635473345252127610695)
                    ·
                      rfl

theorem cell23_5945514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5945514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945514 prefixEnd_5945514 := by exact prefixLift 5945514
  have htrace : WordTrace (prefixWord ++ tailWord_5945514) baseStart_5945514 baseEnd_5945514 := by
    simpa [prefixWord, tailWord_5945514, baseEnd_5945514] using wordTrace_append hprefix tailTrace_5945514
  have hstable : (prefixWord ++ tailWord_5945514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945514).length < 2 ^ (prefixWord ++ tailWord_5945514).sum := by decide
  have hdescent : baseEnd_5945514 < baseStart_5945514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945521 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5945521 : Nat := 118140960795 + 5945521 * 2 ^ 59
def prefixEnd_5945521 : Nat := 4983230072969 + 3 ^ 40 * 5945521 * 2
def baseEnd_5945521 : Nat := 3052910014400337855444553

theorem tailTrace_5945521 : CollatzResearch.WordTrace tailWord_5945521 prefixEnd_5945521 3052910014400337855444553 := by
  unfold tailWord_5945521
  simp only [CollatzResearch.WordTrace]
  refine ⟨216850965893400305990660417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144567310595600203993773611 216850965893400305990660417)
  ·
    refine ⟨162638224420050229492995313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216850965893400305990660417 162638224420050229492995313)
    ·
      refine ⟨121978668315037672119746485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162638224420050229492995313 121978668315037672119746485)
      ·
        refine ⟨11435500154534781761226233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121978668315037672119746485 11435500154534781761226233)
        ·
          refine ⟨8576625115901086320919675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11435500154534781761226233 8576625115901086320919675)
          ·
            refine ⟨12864937673851629481379513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576625115901086320919675 12864937673851629481379513)
            ·
              refine ⟨9648703255388722111034635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12864937673851629481379513 9648703255388722111034635)
              ·
                refine ⟨14473054883083083166551953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9648703255388722111034635 14473054883083083166551953)
                ·
                  refine ⟨10854791162312312374913965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14473054883083083166551953 10854791162312312374913965)
                  ·
                    refine ⟨4070546685867117140592737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10854791162312312374913965 4070546685867117140592737)
                    ·
                      refine ⟨3052910014400337855444553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070546685867117140592737 3052910014400337855444553)
                      ·
                        rfl

theorem cell23_5945521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5945521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945521 prefixEnd_5945521 := by exact prefixLift 5945521
  have htrace : WordTrace (prefixWord ++ tailWord_5945521) baseStart_5945521 baseEnd_5945521 := by
    simpa [prefixWord, tailWord_5945521, baseEnd_5945521] using wordTrace_append hprefix tailTrace_5945521
  have hstable : (prefixWord ++ tailWord_5945521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945521).length < 2 ^ (prefixWord ++ tailWord_5945521).sum := by decide
  have hdescent : baseEnd_5945521 < baseStart_5945521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945530 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_5945530 : Nat := 118140960795 + 5945530 * 2 ^ 59
def prefixEnd_5945530 : Nat := 4983230072969 + 3 ^ 40 * 5945530 * 2
def baseEnd_5945530 : Nat := 3052914635726228320232011

theorem tailTrace_5945530 : CollatzResearch.WordTrace tailWord_5945530 prefixEnd_5945530 3052914635726228320232011 := by
  unfold tailWord_5945530
  simp only [CollatzResearch.WordTrace]
  refine ⟨54212823537591925131934511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144567529433578467018492029 54212823537591925131934511)
  ·
    refine ⟨81319235306387887697901767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54212823537591925131934511 81319235306387887697901767)
    ·
      refine ⟨121978852959581831546852651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81319235306387887697901767 121978852959581831546852651)
      ·
        refine ⟨182968279439372747320278977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121978852959581831546852651 182968279439372747320278977)
        ·
          refine ⟨137226209579529560490209233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182968279439372747320278977 137226209579529560490209233)
          ·
            refine ⟨102919657184647170367656925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137226209579529560490209233 102919657184647170367656925)
            ·
              refine ⟨38594871444242688887871347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102919657184647170367656925 38594871444242688887871347)
              ·
                refine ⟨57892307166364033331807021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38594871444242688887871347 57892307166364033331807021)
                ·
                  refine ⟨21709615187386512499427633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57892307166364033331807021 21709615187386512499427633)
                  ·
                    refine ⟨16282211390539884374570725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21709615187386512499427633 16282211390539884374570725)
                    ·
                      refine ⟨3052914635726228320232011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16282211390539884374570725 3052914635726228320232011)
                      ·
                        rfl

theorem cell23_5945530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_5945530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945530 prefixEnd_5945530 := by exact prefixLift 5945530
  have htrace : WordTrace (prefixWord ++ tailWord_5945530) baseStart_5945530 baseEnd_5945530 := by
    simpa [prefixWord, tailWord_5945530, baseEnd_5945530] using wordTrace_append hprefix tailTrace_5945530
  have hstable : (prefixWord ++ tailWord_5945530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945530).length < 2 ^ (prefixWord ++ tailWord_5945530).sum := by decide
  have hdescent : baseEnd_5945530 < baseStart_5945530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945538 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5945538 : Nat := 118140960795 + 5945538 * 2 ^ 59
def prefixEnd_5945538 : Nat := 4983230072969 + 3 ^ 40 * 5945538 * 2
def baseEnd_5945538 : Nat := 3052918743571464288931975

theorem tailTrace_5945538 : CollatzResearch.WordTrace tailWord_5945538 prefixEnd_5945538 3052918743571464288931975 := by
  unfold tailWord_5945538
  simp only [CollatzResearch.WordTrace]
  refine ⟨54212896483584679473507317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144567723956225811929352845 54212896483584679473507317)
  ·
    refine ⟨5082459045336063700641311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54212896483584679473507317 5082459045336063700641311)
    ·
      refine ⟨7623688568004095550961967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5082459045336063700641311 7623688568004095550961967)
      ·
        refine ⟨11435532852006143326442951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7623688568004095550961967 11435532852006143326442951)
        ·
          refine ⟨17153299278009214989664427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11435532852006143326442951 17153299278009214989664427)
          ·
            refine ⟨25729948917013822484496641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17153299278009214989664427 25729948917013822484496641)
            ·
              refine ⟨19297461687760366863372481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25729948917013822484496641 19297461687760366863372481)
              ·
                refine ⟨14473096265820275147529361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19297461687760366863372481 14473096265820275147529361)
                ·
                  refine ⟨10854822199365206360647021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14473096265820275147529361 10854822199365206360647021)
                  ·
                    refine ⟨4070558324761952385242633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10854822199365206360647021 4070558324761952385242633)
                    ·
                      refine ⟨3052918743571464288931975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070558324761952385242633 3052918743571464288931975)
                      ·
                        rfl

theorem cell23_5945538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5945538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945538 prefixEnd_5945538 := by exact prefixLift 5945538
  have htrace : WordTrace (prefixWord ++ tailWord_5945538) baseStart_5945538 baseEnd_5945538 := by
    simpa [prefixWord, tailWord_5945538, baseEnd_5945538] using wordTrace_append hprefix tailTrace_5945538
  have hstable : (prefixWord ++ tailWord_5945538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945538).length < 2 ^ (prefixWord ++ tailWord_5945538).sum := by decide
  have hdescent : baseEnd_5945538 < baseStart_5945538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945540 : List Nat := [2, 3, 3, 1, 2, 12]
def baseStart_5945540 : Nat := 118140960795 + 5945540 * 2 ^ 59
def prefixEnd_5945540 : Nat := 4983230072969 + 3 ^ 40 * 5945540 * 2
def baseEnd_5945540 : Nat := 12563455845813881815255

theorem tailTrace_5945540 : CollatzResearch.WordTrace tailWord_5945540 prefixEnd_5945540 12563455845813881815255 := by
  unfold tailWord_5945540
  simp only [CollatzResearch.WordTrace]
  refine ⟨108425829440165736117801037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144567772586887648157068049 108425829440165736117801037)
  ·
    refine ⟨40659686040062151044175389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108425829440165736117801037 40659686040062151044175389)
    ·
      refine ⟨15247382265023306641565771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40659686040062151044175389 15247382265023306641565771)
      ·
        refine ⟨22871073397534959962348657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15247382265023306641565771 22871073397534959962348657)
        ·
          refine ⟨17153305048151219971761493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22871073397534959962348657 17153305048151219971761493)
          ·
            refine ⟨12563455845813881815255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17153305048151219971761493 12563455845813881815255)
            ·
              rfl

theorem cell23_5945540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 12].length) (baseStart_5945540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945540 prefixEnd_5945540 := by exact prefixLift 5945540
  have htrace : WordTrace (prefixWord ++ tailWord_5945540) baseStart_5945540 baseEnd_5945540 := by
    simpa [prefixWord, tailWord_5945540, baseEnd_5945540] using wordTrace_append hprefix tailTrace_5945540
  have hstable : (prefixWord ++ tailWord_5945540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945540).length < 2 ^ (prefixWord ++ tailWord_5945540).sum := by decide
  have hdescent : baseEnd_5945540 < baseStart_5945540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945551 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 1, 2, 2]
def baseStart_5945551 : Nat := 118140960795 + 5945551 * 2 ^ 59
def prefixEnd_5945551 : Nat := 4983230072969 + 3 ^ 40 * 5945551 * 2
def baseEnd_5945551 : Nat := 3052925418819972738069415

theorem tailTrace_5945551 : CollatzResearch.WordTrace tailWord_5945551 prefixEnd_5945551 3052925418819972738069415 := by
  unfold tailWord_5945551
  simp only [CollatzResearch.WordTrace]
  refine ⟨216852060083291621114252507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144568040055527747409501671 216852060083291621114252507)
  ·
    refine ⟨325278090124937431671378761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216852060083291621114252507 325278090124937431671378761)
    ·
      refine ⟨243958567593703073753534071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325278090124937431671378761 243958567593703073753534071)
      ·
        refine ⟨365937851390554610630301107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243958567593703073753534071 365937851390554610630301107)
        ·
          refine ⟨548906777085831915945451661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365937851390554610630301107 548906777085831915945451661)
          ·
            refine ⟨205840041407186968479544373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548906777085831915945451661 205840041407186968479544373)
            ·
              refine ⟨19297503881923778294957285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205840041407186968479544373 19297503881923778294957285)
              ·
                refine ⟨3618281977860708430304491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19297503881923778294957285 3618281977860708430304491)
                ·
                  refine ⟨5427422966791062645456737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618281977860708430304491 5427422966791062645456737)
                  ·
                    refine ⟨4070567225093296984092553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5427422966791062645456737 4070567225093296984092553)
                    ·
                      refine ⟨3052925418819972738069415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070567225093296984092553 3052925418819972738069415)
                      ·
                        rfl

theorem cell23_5945551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 2, 2].length) (baseStart_5945551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945551 prefixEnd_5945551 := by exact prefixLift 5945551
  have htrace : WordTrace (prefixWord ++ tailWord_5945551) baseStart_5945551 baseEnd_5945551 := by
    simpa [prefixWord, tailWord_5945551, baseEnd_5945551] using wordTrace_append hprefix tailTrace_5945551
  have hstable : (prefixWord ++ tailWord_5945551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945551).length < 2 ^ (prefixWord ++ tailWord_5945551).sum := by decide
  have hdescent : baseEnd_5945551 < baseStart_5945551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945567 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 3]
def baseStart_5945567 : Nat := 118140960795 + 5945567 * 2 ^ 59
def prefixEnd_5945567 : Nat := 4983230072969 + 3 ^ 40 * 5945567 * 2
def baseEnd_5945567 : Nat := 3052933634510444675469341

theorem tailTrace_5945567 : CollatzResearch.WordTrace tailWord_5945567 prefixEnd_5945567 3052933634510444675469341 := by
  unfold tailWord_5945567
  simp only [CollatzResearch.WordTrace]
  refine ⟨216852643651233655846834955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144568429100822437231223303 216852643651233655846834955)
  ·
    refine ⟨325278965476850483770252433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216852643651233655846834955 325278965476850483770252433)
    ·
      refine ⟨243959224107637862827689325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325278965476850483770252433 243959224107637862827689325)
      ·
        refine ⟨91484709040364198560383497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243959224107637862827689325 91484709040364198560383497)
        ·
          refine ⟨68613531780273148920287623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91484709040364198560383497 68613531780273148920287623)
          ·
            refine ⟨102920297670409723380431435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68613531780273148920287623 102920297670409723380431435)
            ·
              refine ⟨154380446505614585070647153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102920297670409723380431435 154380446505614585070647153)
              ·
                refine ⟨115785334879210938802985365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154380446505614585070647153 115785334879210938802985365)
                ·
                  refine ⟨5427437572463012756389939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115785334879210938802985365 5427437572463012756389939)
                  ·
                    refine ⟨8141156358694519134584909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5427437572463012756389939 8141156358694519134584909)
                    ·
                      refine ⟨3052933634510444675469341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8141156358694519134584909 3052933634510444675469341)
                      ·
                        rfl

theorem cell23_5945567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_5945567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945567 prefixEnd_5945567 := by exact prefixLift 5945567
  have htrace : WordTrace (prefixWord ++ tailWord_5945567) baseStart_5945567 baseEnd_5945567 := by
    simpa [prefixWord, tailWord_5945567, baseEnd_5945567] using wordTrace_append hprefix tailTrace_5945567
  have hstable : (prefixWord ++ tailWord_5945567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945567).length < 2 ^ (prefixWord ++ tailWord_5945567).sum := by decide
  have hdescent : baseEnd_5945567 < baseStart_5945567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945580 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_5945580 : Nat := 118140960795 + 5945580 * 2 ^ 59
def prefixEnd_5945580 : Nat := 4983230072969 + 3 ^ 40 * 5945580 * 2
def baseEnd_5945580 : Nat := 3052940309758953124606781

theorem tailTrace_5945580 : CollatzResearch.WordTrace tailWord_5945580 prefixEnd_5945580 3052940309758953124606781 := by
  unfold tailWord_5945580
  simp only [CollatzResearch.WordTrace]
  refine ⟨108426558900093279533529097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144568745200124372711372129 108426558900093279533529097)
  ·
    refine ⟨81319919175069959650146823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108426558900093279533529097 81319919175069959650146823)
    ·
      refine ⟨121979878762604939475220235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81319919175069959650146823 121979878762604939475220235)
      ·
        refine ⟨182969818143907409212830353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121979878762604939475220235 182969818143907409212830353)
        ·
          refine ⟨137227363607930556909622765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182969818143907409212830353 137227363607930556909622765)
          ·
            refine ⟨51460261352973958841108537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137227363607930556909622765 51460261352973958841108537)
            ·
              refine ⟨38595196014730469130831403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51460261352973958841108537 38595196014730469130831403)
              ·
                refine ⟨57892794022095703696247105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38595196014730469130831403 57892794022095703696247105)
                ·
                  refine ⟨43419595516571777772185329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57892794022095703696247105 43419595516571777772185329)
                  ·
                    refine ⟨32564696637428833329138997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43419595516571777772185329 32564696637428833329138997)
                    ·
                      refine ⟨3052940309758953124606781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32564696637428833329138997 3052940309758953124606781)
                      ·
                        rfl

theorem cell23_5945580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_5945580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945580 prefixEnd_5945580 := by exact prefixLift 5945580
  have htrace : WordTrace (prefixWord ++ tailWord_5945580) baseStart_5945580 baseEnd_5945580 := by
    simpa [prefixWord, tailWord_5945580, baseEnd_5945580] using wordTrace_append hprefix tailTrace_5945580
  have hstable : (prefixWord ++ tailWord_5945580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945580).length < 2 ^ (prefixWord ++ tailWord_5945580).sum := by decide
  have hdescent : baseEnd_5945580 < baseStart_5945580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945600 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_5945600 : Nat := 118140960795 + 5945600 * 2 ^ 59
def prefixEnd_5945600 : Nat := 4983230072969 + 3 ^ 40 * 5945600 * 2
def baseEnd_5945600 : Nat := 1017650193124014348785563

theorem tailTrace_5945600 : CollatzResearch.WordTrace tailWord_5945600 prefixEnd_5945600 1017650193124014348785563 := by
  unfold tailWord_5945600
  simp only [CollatzResearch.WordTrace]
  refine ⟨108426923630057051241393127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144569231506742734988524169 108426923630057051241393127)
  ·
    refine ⟨162640385445085576862089691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108426923630057051241393127 162640385445085576862089691)
    ·
      refine ⟨243960578167628365293134537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162640385445085576862089691 243960578167628365293134537)
      ·
        refine ⟨182970433625721273969850903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243960578167628365293134537 182970433625721273969850903)
        ·
          refine ⟨274455650438581910954776355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182970433625721273969850903 274455650438581910954776355)
          ·
            refine ⟨411683475657872866432164533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274455650438581910954776355 411683475657872866432164533)
            ·
              refine ⟨38595325842925581228015425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411683475657872866432164533 38595325842925581228015425)
              ·
                refine ⟨28946494382194185921011569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38595325842925581228015425 28946494382194185921011569)
                ·
                  refine ⟨21709870786645639440758677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28946494382194185921011569 21709870786645639440758677)
                  ·
                    refine ⟨1017650193124014348785563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21709870786645639440758677 1017650193124014348785563)
                    ·
                      rfl

theorem cell23_5945600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_5945600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945600 prefixEnd_5945600 := by exact prefixLift 5945600
  have htrace : WordTrace (prefixWord ++ tailWord_5945600) baseStart_5945600 baseEnd_5945600 := by
    simpa [prefixWord, tailWord_5945600, baseEnd_5945600] using wordTrace_append hprefix tailTrace_5945600
  have hstable : (prefixWord ++ tailWord_5945600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945600).length < 2 ^ (prefixWord ++ tailWord_5945600).sum := by decide
  have hdescent : baseEnd_5945600 < baseStart_5945600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945707 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 5, 4]
def baseStart_5945707 : Nat := 118140960795 + 5945707 * 2 ^ 59
def prefixEnd_5945707 : Nat := 4983230072969 + 3 ^ 40 * 5945707 * 2
def baseEnd_5945707 : Nat := 1017668507267358042572899

theorem tailTrace_5945707 : CollatzResearch.WordTrace tailWord_5945707 prefixEnd_5945707 1017668507267358042572899 := by
  unfold tailWord_5945707
  simp only [CollatzResearch.WordTrace]
  refine ⟨216857749870726459756931375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144571833247150973171287583 216857749870726459756931375)
  ·
    refine ⟨325286624806089689635397063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216857749870726459756931375 325286624806089689635397063)
    ·
      refine ⟨487929937209134534453095595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325286624806089689635397063 487929937209134534453095595)
      ·
        refine ⟨731894905813701801679643393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487929937209134534453095595 731894905813701801679643393)
        ·
          refine ⟨548921179360276351259732545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731894905813701801679643393 548921179360276351259732545)
          ·
            refine ⟨411690884520207263444799409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548921179360276351259732545 411690884520207263444799409)
            ·
              refine ⟨308768163390155447583599557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411690884520207263444799409 308768163390155447583599557)
              ·
                refine ⟨57894030635654146421924917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308768163390155447583599557 57894030635654146421924917)
                ·
                  refine ⟨5427565372092576227055461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57894030635654146421924917 5427565372092576227055461)
                  ·
                    refine ⟨1017668507267358042572899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427565372092576227055461 1017668507267358042572899)
                    ·
                      rfl

theorem cell23_5945707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 4].length) (baseStart_5945707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945707 prefixEnd_5945707 := by exact prefixLift 5945707
  have htrace : WordTrace (prefixWord ++ tailWord_5945707) baseStart_5945707 baseEnd_5945707 := by
    simpa [prefixWord, tailWord_5945707, baseEnd_5945707] using wordTrace_append hprefix tailTrace_5945707
  have hstable : (prefixWord ++ tailWord_5945707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945707).length < 2 ^ (prefixWord ++ tailWord_5945707).sum := by decide
  have hdescent : baseEnd_5945707 < baseStart_5945707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945714 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5945714 : Nat := 118140960795 + 5945714 * 2 ^ 59
def prefixEnd_5945714 : Nat := 4983230072969 + 3 ^ 40 * 5945714 * 2
def baseEnd_5945714 : Nat := 3053009116166655600331165

theorem tailTrace_5945714 : CollatzResearch.WordTrace tailWord_5945714 prefixEnd_5945714 3053009116166655600331165 := by
  unfold tailWord_5945714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54214501295425274988109049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144572003454467399968290797 54214501295425274988109049)
  ·
    refine ⟨40660875971568956241081787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54214501295425274988109049 40660875971568956241081787)
    ·
      refine ⟨60991313957353434361622681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40660875971568956241081787 60991313957353434361622681)
      ·
        refine ⟨45743485468015075771217011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60991313957353434361622681 45743485468015075771217011)
        ·
          refine ⟨68615228202022613656825517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45743485468015075771217011 68615228202022613656825517)
          ·
            refine ⟨25730710575758480121309569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68615228202022613656825517 25730710575758480121309569)
            ·
              refine ⟨19298032931818860090982177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25730710575758480121309569 19298032931818860090982177)
              ·
                refine ⟨14473524698864145068236633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19298032931818860090982177 14473524698864145068236633)
                ·
                  refine ⟨10855143524148108801177475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14473524698864145068236633 10855143524148108801177475)
                  ·
                    refine ⟨16282715286222163201766213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10855143524148108801177475 16282715286222163201766213)
                    ·
                      refine ⟨3053009116166655600331165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16282715286222163201766213 3053009116166655600331165)
                      ·
                        rfl

theorem cell23_5945714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5945714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945714 prefixEnd_5945714 := by exact prefixLift 5945714
  have htrace : WordTrace (prefixWord ++ tailWord_5945714) baseStart_5945714 baseEnd_5945714 := by
    simpa [prefixWord, tailWord_5945714, baseEnd_5945714] using wordTrace_append hprefix tailTrace_5945714
  have hstable : (prefixWord ++ tailWord_5945714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945714).length < 2 ^ (prefixWord ++ tailWord_5945714).sum := by decide
  have hdescent : baseEnd_5945714 < baseStart_5945714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945731 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 2, 4, 2]
def baseStart_5945731 : Nat := 118140960795 + 5945731 * 2 ^ 59
def prefixEnd_5945731 : Nat := 4983230072969 + 3 ^ 40 * 5945731 * 2
def baseEnd_5945731 : Nat := 3053017845337782033818587

theorem tailTrace_5945731 : CollatzResearch.WordTrace tailWord_5945731 prefixEnd_5945731 3053017845337782033818587 := by
  unfold tailWord_5945731
  simp only [CollatzResearch.WordTrace]
  refine ⟨216858625222639511855805047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144572416815093007903870031 216858625222639511855805047)
  ·
    refine ⟨325287937833959267783707571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216858625222639511855805047 325287937833959267783707571)
    ·
      refine ⟨487931906750938901675561357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325287937833959267783707571 487931906750938901675561357)
      ·
        refine ⟨182974465031602088128335509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487931906750938901675561357 182974465031602088128335509)
        ·
          refine ⟨8576928048356347881015727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182974465031602088128335509 8576928048356347881015727)
          ·
            refine ⟨12865392072534521821523591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576928048356347881015727 12865392072534521821523591)
            ·
              refine ⟨19298088108801782732285387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12865392072534521821523591 19298088108801782732285387)
              ·
                refine ⟨28947132163202674098428081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19298088108801782732285387 28947132163202674098428081)
                ·
                  refine ⟨21710349122402005573821061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28947132163202674098428081 21710349122402005573821061)
                  ·
                    refine ⟨4070690460450376045091449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21710349122402005573821061 4070690460450376045091449)
                    ·
                      refine ⟨3053017845337782033818587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070690460450376045091449 3053017845337782033818587)
                      ·
                        rfl

theorem cell23_5945731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_5945731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945731 prefixEnd_5945731 := by exact prefixLift 5945731
  have htrace : WordTrace (prefixWord ++ tailWord_5945731) baseStart_5945731 baseEnd_5945731 := by
    simpa [prefixWord, tailWord_5945731, baseEnd_5945731] using wordTrace_append hprefix tailTrace_5945731
  have hstable : (prefixWord ++ tailWord_5945731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945731).length < 2 ^ (prefixWord ++ tailWord_5945731).sum := by decide
  have hdescent : baseEnd_5945731 < baseStart_5945731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945748 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5945748 : Nat := 118140960795 + 5945748 * 2 ^ 59
def prefixEnd_5945748 : Nat := 4983230072969 + 3 ^ 40 * 5945748 * 2
def baseEnd_5945748 : Nat := 3053026574508908467306009

theorem tailTrace_5945748 : CollatzResearch.WordTrace tailWord_5945748 prefixEnd_5945748 3053026574508908467306009 := by
  unfold tailWord_5945748
  simp only [CollatzResearch.WordTrace]
  refine ⟨108429622631788961879586949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144572830175718615839449265 108429622631788961879586949)
  ·
    refine ⟨20330554243460430352422553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108429622631788961879586949 20330554243460430352422553)
    ·
      refine ⟨15247915682595322764316915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20330554243460430352422553 15247915682595322764316915)
      ·
        refine ⟨22871873523892984146475373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15247915682595322764316915 22871873523892984146475373)
        ·
          refine ⟨8576952571459869054928265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22871873523892984146475373 8576952571459869054928265)
          ·
            refine ⟨6432714428594901791196199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8576952571459869054928265 6432714428594901791196199)
            ·
              refine ⟨9649071642892352686794299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432714428594901791196199 9649071642892352686794299)
              ·
                refine ⟨14473607464338529030191449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9649071642892352686794299 14473607464338529030191449)
                ·
                  refine ⟨10855205598253896772643587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14473607464338529030191449 10855205598253896772643587)
                  ·
                    refine ⟨16282808397380845158965381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10855205598253896772643587 16282808397380845158965381)
                    ·
                      refine ⟨3053026574508908467306009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16282808397380845158965381 3053026574508908467306009)
                      ·
                        rfl

theorem cell23_5945748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5945748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945748 prefixEnd_5945748 := by exact prefixLift 5945748
  have htrace : WordTrace (prefixWord ++ tailWord_5945748) baseStart_5945748 baseEnd_5945748 := by
    simpa [prefixWord, tailWord_5945748, baseEnd_5945748] using wordTrace_append hprefix tailTrace_5945748
  have hstable : (prefixWord ++ tailWord_5945748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945748).length < 2 ^ (prefixWord ++ tailWord_5945748).sum := by decide
  have hdescent : baseEnd_5945748 < baseStart_5945748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945807 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_5945807 : Nat := 118140960795 + 5945807 * 2 ^ 59
def prefixEnd_5945807 : Nat := 4983230072969 + 3 ^ 40 * 5945807 * 2
def baseEnd_5945807 : Nat := 3053056869867523736468237

theorem tailTrace_5945807 : CollatzResearch.WordTrace tailWord_5945807 prefixEnd_5945807 3053056869867523736468237 := by
  unfold tailWord_5945807
  simp only [CollatzResearch.WordTrace]
  refine ⟨216861397170364176835571675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144574264780242784557047783 216861397170364176835571675)
  ·
    refine ⟨325292095755546265253357513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216861397170364176835571675 325292095755546265253357513)
    ·
      refine ⟨243969071816659698940018135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325292095755546265253357513 243969071816659698940018135)
      ·
        refine ⟨365953607724989548410027203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243969071816659698940018135 365953607724989548410027203)
        ·
          refine ⟨548930411587484322615040805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365953607724989548410027203 548930411587484322615040805)
          ·
            refine ⟨102924452172653310490320151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 548930411587484322615040805 102924452172653310490320151)
            ·
              refine ⟨154386678258979965735480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102924452172653310490320151 154386678258979965735480227)
              ·
                refine ⟨231580017388469948603220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154386678258979965735480227 231580017388469948603220341)
                ·
                  refine ⟨21710626630169057681551907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231580017388469948603220341 21710626630169057681551907)
                  ·
                    refine ⟨32565939945253586522327861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21710626630169057681551907 32565939945253586522327861)
                    ·
                      refine ⟨3053056869867523736468237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32565939945253586522327861 3053056869867523736468237)
                      ·
                        rfl

theorem cell23_5945807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_5945807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945807 prefixEnd_5945807 := by exact prefixLift 5945807
  have htrace : WordTrace (prefixWord ++ tailWord_5945807) baseStart_5945807 baseEnd_5945807 := by
    simpa [prefixWord, tailWord_5945807, baseEnd_5945807] using wordTrace_append hprefix tailTrace_5945807
  have hstable : (prefixWord ++ tailWord_5945807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945807).length < 2 ^ (prefixWord ++ tailWord_5945807).sum := by decide
  have hdescent : baseEnd_5945807 < baseStart_5945807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945821 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5945821 : Nat := 118140960795 + 5945821 * 2 ^ 59
def prefixEnd_5945821 : Nat := 4983230072969 + 3 ^ 40 * 5945821 * 2
def baseEnd_5945821 : Nat := 3053064058596686681693173

theorem tailTrace_5945821 : CollatzResearch.WordTrace tailWord_5945821 prefixEnd_5945821 3053064058596686681693173 := by
  unfold tailWord_5945821
  simp only [CollatzResearch.WordTrace]
  refine ⟨216861907792313457226581317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144574605194875638151054211 216861907792313457226581317)
  ·
    refine ⟨40661607711058773229983997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216861907792313457226581317 40661607711058773229983997)
    ·
      refine ⟨15248102891647039961243999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40661607711058773229983997 15248102891647039961243999)
      ·
        refine ⟨22872154337470559941865999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15248102891647039961243999 22872154337470559941865999)
        ·
          refine ⟨34308231506205839912798999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22872154337470559941865999 34308231506205839912798999)
          ·
            refine ⟨51462347259308759869198499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34308231506205839912798999 51462347259308759869198499)
            ·
              refine ⟨77193520888963139803797749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51462347259308759869198499 77193520888963139803797749)
              ·
                refine ⟨7236892583340294356606039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77193520888963139803797749 7236892583340294356606039)
                ·
                  refine ⟨10855338875010441534909059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7236892583340294356606039 10855338875010441534909059)
                  ·
                    refine ⟨16283008312515662302363589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10855338875010441534909059 16283008312515662302363589)
                    ·
                      refine ⟨3053064058596686681693173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16283008312515662302363589 3053064058596686681693173)
                      ·
                        rfl

theorem cell23_5945821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5945821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945821 prefixEnd_5945821 := by exact prefixLift 5945821
  have htrace : WordTrace (prefixWord ++ tailWord_5945821) baseStart_5945821 baseEnd_5945821 := by
    simpa [prefixWord, tailWord_5945821, baseEnd_5945821] using wordTrace_append hprefix tailTrace_5945821
  have hstable : (prefixWord ++ tailWord_5945821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945821).length < 2 ^ (prefixWord ++ tailWord_5945821).sum := by decide
  have hdescent : baseEnd_5945821 < baseStart_5945821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945824 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_5945824 : Nat := 118140960795 + 5945824 * 2 ^ 59
def prefixEnd_5945824 : Nat := 4983230072969 + 3 ^ 40 * 5945824 * 2
def baseEnd_5945824 : Nat := 3053065599038650169955659

theorem tailTrace_5945824 : CollatzResearch.WordTrace tailWord_5945824 prefixEnd_5945824 3053065599038650169955659 := by
  unfold tailWord_5945824
  simp only [CollatzResearch.WordTrace]
  refine ⟨108431008605651294369470263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144574678140868392492627017 108431008605651294369470263)
  ·
    refine ⟨162646512908476941554205395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108431008605651294369470263 162646512908476941554205395)
    ·
      refine ⟨243969769362715412331308093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162646512908476941554205395 243969769362715412331308093)
      ·
        refine ⟨91488663511018279624240535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243969769362715412331308093 91488663511018279624240535)
        ·
          refine ⟨137232995266527419436360803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91488663511018279624240535 137232995266527419436360803)
          ·
            refine ⟨205849492899791129154541205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137232995266527419436360803 205849492899791129154541205)
            ·
              refine ⟨9649194979677709179119119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205849492899791129154541205 9649194979677709179119119)
              ·
                refine ⟨14473792469516563768678679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9649194979677709179119119 14473792469516563768678679)
                ·
                  refine ⟨21710688704274845653018019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14473792469516563768678679 21710688704274845653018019)
                  ·
                    refine ⟨32566033056412268479527029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21710688704274845653018019 32566033056412268479527029)
                    ·
                      refine ⟨3053065599038650169955659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32566033056412268479527029 3053065599038650169955659)
                      ·
                        rfl

theorem cell23_5945824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_5945824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945824 prefixEnd_5945824 := by exact prefixLift 5945824
  have htrace : WordTrace (prefixWord ++ tailWord_5945824) baseStart_5945824 baseEnd_5945824 := by
    simpa [prefixWord, tailWord_5945824, baseEnd_5945824] using wordTrace_append hprefix tailTrace_5945824
  have hstable : (prefixWord ++ tailWord_5945824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945824).length < 2 ^ (prefixWord ++ tailWord_5945824).sum := by decide
  have hdescent : baseEnd_5945824 < baseStart_5945824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945831 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5945831 : Nat := 118140960795 + 5945831 * 2 ^ 59
def prefixEnd_5945831 : Nat := 4983230072969 + 3 ^ 40 * 5945831 * 2
def baseEnd_5945831 : Nat := 1017689731134410547522709

theorem tailTrace_5945831 : CollatzResearch.WordTrace tailWord_5945831 prefixEnd_5945831 1017689731134410547522709 := by
  unfold tailWord_5945831
  simp only [CollatzResearch.WordTrace]
  refine ⟨216862272522277228934445347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144574848348184819289630231 216862272522277228934445347)
  ·
    refine ⟨325293408783415843401668021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216862272522277228934445347 325293408783415843401668021)
    ·
      refine ⟨30496257073445235318906377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325293408783415843401668021 30496257073445235318906377)
      ·
        refine ⟨22872192805083926489179783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30496257073445235318906377 22872192805083926489179783)
        ·
          refine ⟨34308289207625889733769675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22872192805083926489179783 34308289207625889733769675)
          ·
            refine ⟨51462433811438834600654513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34308289207625889733769675 51462433811438834600654513)
            ·
              refine ⟨38596825358579125950490885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51462433811438834600654513 38596825358579125950490885)
              ·
                refine ⟨7236904754733586115717041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38596825358579125950490885 7236904754733586115717041)
                ·
                  refine ⟨5427678566050189586787781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7236904754733586115717041 5427678566050189586787781)
                  ·
                    refine ⟨1017689731134410547522709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427678566050189586787781 1017689731134410547522709)
                    ·
                      rfl

theorem cell23_5945831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5945831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945831 prefixEnd_5945831 := by exact prefixLift 5945831
  have htrace : WordTrace (prefixWord ++ tailWord_5945831) baseStart_5945831 baseEnd_5945831 := by
    simpa [prefixWord, tailWord_5945831, baseEnd_5945831] using wordTrace_append hprefix tailTrace_5945831
  have hstable : (prefixWord ++ tailWord_5945831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945831).length < 2 ^ (prefixWord ++ tailWord_5945831).sum := by decide
  have hdescent : baseEnd_5945831 < baseStart_5945831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945834 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_5945834 : Nat := 118140960795 + 5945834 * 2 ^ 59
def prefixEnd_5945834 : Nat := 4983230072969 + 3 ^ 40 * 5945834 * 2
def baseEnd_5945834 : Nat := 3053070733845195130830613

theorem tailTrace_5945834 : CollatzResearch.WordTrace tailWord_5945834 prefixEnd_5945834 3053070733845195130830613 := by
  unfold tailWord_5945834
  simp only [CollatzResearch.WordTrace]
  refine ⟨54215595485316590111701139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144574921294177573631203037 54215595485316590111701139)
  ·
    refine ⟨81323393227974885167551709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54215595485316590111701139 81323393227974885167551709)
    ·
      refine ⟨30496272460490581937831891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81323393227974885167551709 30496272460490581937831891)
      ·
        refine ⟨45744408690735872906747837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30496272460490581937831891 45744408690735872906747837)
        ·
          refine ⟨17154153259025952340030439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45744408690735872906747837 17154153259025952340030439)
          ·
            refine ⟨25731229888538928510045659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17154153259025952340030439 25731229888538928510045659)
            ·
              refine ⟨38596844832808392765068489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25731229888538928510045659 38596844832808392765068489)
              ·
                refine ⟨28947633624606294573801367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38596844832808392765068489 28947633624606294573801367)
                ·
                  refine ⟨43421450436909441860702051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28947633624606294573801367 43421450436909441860702051)
                  ·
                    refine ⟨65132175655364162791053077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43421450436909441860702051 65132175655364162791053077)
                    ·
                      refine ⟨3053070733845195130830613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65132175655364162791053077 3053070733845195130830613)
                      ·
                        rfl

theorem cell23_5945834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_5945834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945834 prefixEnd_5945834 := by exact prefixLift 5945834
  have htrace : WordTrace (prefixWord ++ tailWord_5945834) baseStart_5945834 baseEnd_5945834 := by
    simpa [prefixWord, tailWord_5945834, baseEnd_5945834] using wordTrace_append hprefix tailTrace_5945834
  have hstable : (prefixWord ++ tailWord_5945834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945834).length < 2 ^ (prefixWord ++ tailWord_5945834).sum := by decide
  have hdescent : baseEnd_5945834 < baseStart_5945834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945895 : List Nat := [1, 1, 7, 2, 2, 1, 1, 8]
def baseStart_5945895 : Nat := 118140960795 + 5945895 * 2 ^ 59
def prefixEnd_5945895 : Nat := 4983230072969 + 3 ^ 40 * 5945895 * 2
def baseEnd_5945895 : Nat := 113077853932041458969179

theorem tailTrace_5945895 : CollatzResearch.WordTrace tailWord_5945895 prefixEnd_5945895 113077853932041458969179 := by
  unfold tailWord_5945895
  simp only [CollatzResearch.WordTrace]
  refine ⟨216864606794045367864775139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144576404529363578576516759 216864606794045367864775139)
  ·
    refine ⟨325296910191068051797162709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216864606794045367864775139 325296910191068051797162709)
    ·
      refine ⟨7624146332603157463996001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 325296910191068051797162709 7624146332603157463996001)
      ·
        refine ⟨5718109749452368097997001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7624146332603157463996001 5718109749452368097997001)
        ·
          refine ⟨4288582312089276073497751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718109749452368097997001 4288582312089276073497751)
          ·
            refine ⟨6432873468133914110246627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288582312089276073497751 6432873468133914110246627)
            ·
              refine ⟨9649310202200871165369941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432873468133914110246627 9649310202200871165369941)
              ·
                refine ⟨113077853932041458969179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9649310202200871165369941 113077853932041458969179)
                ·
                  rfl

theorem cell23_5945895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 8].length) (baseStart_5945895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945895 prefixEnd_5945895 := by exact prefixLift 5945895
  have htrace : WordTrace (prefixWord ++ tailWord_5945895) baseStart_5945895 baseEnd_5945895 := by
    simpa [prefixWord, tailWord_5945895, baseEnd_5945895] using wordTrace_append hprefix tailTrace_5945895
  have hstable : (prefixWord ++ tailWord_5945895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945895).length < 2 ^ (prefixWord ++ tailWord_5945895).sum := by decide
  have hdescent : baseEnd_5945895 < baseStart_5945895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945898 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5945898 : Nat := 118140960795 + 5945898 * 2 ^ 59
def prefixEnd_5945898 : Nat := 4983230072969 + 3 ^ 40 * 5945898 * 2
def baseEnd_5945898 : Nat := 3053103596607082880430319

theorem tailTrace_5945898 : CollatzResearch.WordTrace tailWord_5945898 prefixEnd_5945898 3053103596607082880430319 := by
  unfold tailWord_5945898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54216179053258624844283587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144576477475356332918089565 54216179053258624844283587)
  ·
    refine ⟨81324268579887937266425381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54216179053258624844283587 81324268579887937266425381)
    ·
      refine ⟨15248300358728988237454759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81324268579887937266425381 15248300358728988237454759)
      ·
        refine ⟨22872450538093482356182139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15248300358728988237454759 22872450538093482356182139)
        ·
          refine ⟨34308675807140223534273209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22872450538093482356182139 34308675807140223534273209)
          ·
            refine ⟨25731506855355167650704907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34308675807140223534273209 25731506855355167650704907)
            ·
              refine ⟨38597260283032751476057361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25731506855355167650704907 38597260283032751476057361)
              ·
                refine ⟨28947945212274563607043021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38597260283032751476057361 28947945212274563607043021)
                ·
                  refine ⟨10855479454602961352641133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28947945212274563607043021 10855479454602961352641133)
                  ·
                    refine ⟨4070804795476110507240425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10855479454602961352641133 4070804795476110507240425)
                    ·
                      refine ⟨3053103596607082880430319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070804795476110507240425 3053103596607082880430319)
                      ·
                        rfl

theorem cell23_5945898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5945898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945898 prefixEnd_5945898 := by exact prefixLift 5945898
  have htrace : WordTrace (prefixWord ++ tailWord_5945898) baseStart_5945898 baseEnd_5945898 := by
    simpa [prefixWord, tailWord_5945898, baseEnd_5945898] using wordTrace_append hprefix tailTrace_5945898
  have hstable : (prefixWord ++ tailWord_5945898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945898).length < 2 ^ (prefixWord ++ tailWord_5945898).sum := by decide
  have hdescent : baseEnd_5945898 < baseStart_5945898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945962 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5945962 : Nat := 118140960795 + 5945962 * 2 ^ 59
def prefixEnd_5945962 : Nat := 4983230072969 + 3 ^ 40 * 5945962 * 2
def baseEnd_5945962 : Nat := 3053136459368970630030025

theorem tailTrace_5945962 : CollatzResearch.WordTrace tailWord_5945962 prefixEnd_5945962 3053136459368970630030025 := by
  unfold tailWord_5945962
  simp only [CollatzResearch.WordTrace]
  refine ⟨54216762621200659576866035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144578033656535092204976093 54216762621200659576866035)
  ·
    refine ⟨81325143931800989365299053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54216762621200659576866035 81325143931800989365299053)
    ·
      refine ⟨30496928974425371011987145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81325143931800989365299053 30496928974425371011987145)
      ·
        refine ⟨22872696730819028258990359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30496928974425371011987145 22872696730819028258990359)
        ·
          refine ⟨34309045096228542388485539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22872696730819028258990359 34309045096228542388485539)
          ·
            refine ⟨51463567644342813582728309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34309045096228542388485539 51463567644342813582728309)
            ·
              refine ⟨4824709466657138773380779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51463567644342813582728309 4824709466657138773380779)
              ·
                refine ⟨7237064199985708160071169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824709466657138773380779 7237064199985708160071169)
                ·
                  refine ⟨5427798149989281120053377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7237064199985708160071169 5427798149989281120053377)
                  ·
                    refine ⟨4070848612491960840040033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5427798149989281120053377 4070848612491960840040033)
                    ·
                      refine ⟨3053136459368970630030025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070848612491960840040033 3053136459368970630030025)
                      ·
                        rfl

theorem cell23_5945962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5945962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945962 prefixEnd_5945962 := by exact prefixLift 5945962
  have htrace : WordTrace (prefixWord ++ tailWord_5945962) baseStart_5945962 baseEnd_5945962 := by
    simpa [prefixWord, tailWord_5945962, baseEnd_5945962] using wordTrace_append hprefix tailTrace_5945962
  have hstable : (prefixWord ++ tailWord_5945962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945962).length < 2 ^ (prefixWord ++ tailWord_5945962).sum := by decide
  have hdescent : baseEnd_5945962 < baseStart_5945962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5945964 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_5945964 : Nat := 118140960795 + 5945964 * 2 ^ 59
def prefixEnd_5945964 : Nat := 4983230072969 + 3 ^ 40 * 5945964 * 2
def baseEnd_5945964 : Nat := 1017712495443426540735005

theorem tailTrace_5945964 : CollatzResearch.WordTrace tailWord_5945964 prefixEnd_5945964 1017712495443426540735005 := by
  unfold tailWord_5945964
  simp only [CollatzResearch.WordTrace]
  refine ⟨108433561715397696324518473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144578082287196928432691297 108433561715397696324518473)
  ·
    refine ⟨81325171286548272243388855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108433561715397696324518473 81325171286548272243388855)
    ·
      refine ⟨121987756929822408365083283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81325171286548272243388855 121987756929822408365083283)
      ·
        refine ⟨182981635394733612547624925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121987756929822408365083283 182981635394733612547624925)
        ·
          refine ⟨68618113273025104705359347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182981635394733612547624925 68618113273025104705359347)
          ·
            refine ⟨102927169909537657058039021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68618113273025104705359347 102927169909537657058039021)
            ·
              refine ⟨38597688716076621396764633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102927169909537657058039021 38597688716076621396764633)
              ·
                refine ⟨28948266537057466047573475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38597688716076621396764633 28948266537057466047573475)
                ·
                  refine ⟨43422399805586199071360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28948266537057466047573475 43422399805586199071360213)
                  ·
                    refine ⟨1017712495443426540735005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43422399805586199071360213 1017712495443426540735005)
                    ·
                      rfl

theorem cell23_5945964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_5945964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5945964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5945964 prefixEnd_5945964 := by exact prefixLift 5945964
  have htrace : WordTrace (prefixWord ++ tailWord_5945964) baseStart_5945964 baseEnd_5945964 := by
    simpa [prefixWord, tailWord_5945964, baseEnd_5945964] using wordTrace_append hprefix tailTrace_5945964
  have hstable : (prefixWord ++ tailWord_5945964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5945964).length < 2 ^ (prefixWord ++ tailWord_5945964).sum := by decide
  have hdescent : baseEnd_5945964 < baseStart_5945964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5945964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946021 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_5946021 : Nat := 118140960795 + 5946021 * 2 ^ 59
def prefixEnd_5946021 : Nat := 4983230072969 + 3 ^ 40 * 5946021 * 2
def baseEnd_5946021 : Nat := 3053166754727585899192253

theorem tailTrace_5946021 : CollatzResearch.WordTrace tailWord_5946021 prefixEnd_5946021 3053166754727585899192253 := by
  unfold tailWord_5946021
  simp only [CollatzResearch.WordTrace]
  refine ⟨216869202391588891383861917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144579468261059260922574611 216869202391588891383861917)
  ·
    refine ⟨81325950896845834268948219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216869202391588891383861917 81325950896845834268948219)
    ·
      refine ⟨121988926345268751403422329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81325950896845834268948219 121988926345268751403422329)
      ·
        refine ⟨91491694758951563552566747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121988926345268751403422329 91491694758951563552566747)
        ·
          refine ⟨137237542138427345328850121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91491694758951563552566747 137237542138427345328850121)
          ·
            refine ⟨102928156603820508996637591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137237542138427345328850121 102928156603820508996637591)
            ·
              refine ⟨154392234905730763494956387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102928156603820508996637591 154392234905730763494956387)
              ·
                refine ⟨231588352358596145242434581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154392234905730763494956387 231588352358596145242434581)
                ·
                  refine ⟨10855704016809194308239121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231588352358596145242434581 10855704016809194308239121)
                  ·
                    refine ⟨8141778012606895731179341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10855704016809194308239121 8141778012606895731179341)
                    ·
                      refine ⟨3053166754727585899192253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8141778012606895731179341 3053166754727585899192253)
                      ·
                        rfl

theorem cell23_5946021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_5946021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946021 prefixEnd_5946021 := by exact prefixLift 5946021
  have htrace : WordTrace (prefixWord ++ tailWord_5946021) baseStart_5946021 baseEnd_5946021 := by
    simpa [prefixWord, tailWord_5946021, baseEnd_5946021] using wordTrace_append hprefix tailTrace_5946021
  have hstable : (prefixWord ++ tailWord_5946021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946021).length < 2 ^ (prefixWord ++ tailWord_5946021).sum := by decide
  have hdescent : baseEnd_5946021 < baseStart_5946021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946058 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_5946058 : Nat := 118140960795 + 5946058 * 2 ^ 59
def prefixEnd_5946058 : Nat := 4983230072969 + 3 ^ 40 * 5946058 * 2
def baseEnd_5946058 : Nat := 339242861501311361603287

theorem tailTrace_5946058 : CollatzResearch.WordTrace tailWord_5946058 prefixEnd_5946058 339242861501311361603287 := by
  unfold tailWord_5946058
  simp only [CollatzResearch.WordTrace]
  refine ⟨54217637973113711675739707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144580367928303231135305885 54217637973113711675739707)
  ·
    refine ⟨81326456959670567513609561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54217637973113711675739707 81326456959670567513609561)
    ·
      refine ⟨60994842719752925635207171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81326456959670567513609561 60994842719752925635207171)
      ·
        refine ⟨91492264079629388452810757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60994842719752925635207171 91492264079629388452810757)
        ·
          refine ⟨17154799514930510334902017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91492264079629388452810757 17154799514930510334902017)
          ·
            refine ⟨12866099636197882751176513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17154799514930510334902017 12866099636197882751176513)
            ·
              refine ⟨9649574727148412063382385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12866099636197882751176513 9649574727148412063382385)
              ·
                refine ⟨7237181045361309047536789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9649574727148412063382385 7237181045361309047536789)
                ·
                  refine ⟨339242861501311361603287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7237181045361309047536789 339242861501311361603287)
                  ·
                    rfl

theorem cell23_5946058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_5946058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946058 prefixEnd_5946058 := by exact prefixLift 5946058
  have htrace : WordTrace (prefixWord ++ tailWord_5946058) baseStart_5946058 baseEnd_5946058 := by
    simpa [prefixWord, tailWord_5946058, baseEnd_5946058] using wordTrace_append hprefix tailTrace_5946058
  have hstable : (prefixWord ++ tailWord_5946058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946058).length < 2 ^ (prefixWord ++ tailWord_5946058).sum := by decide
  have hdescent : baseEnd_5946058 < baseStart_5946058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946062 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_5946062 : Nat := 118140960795 + 5946062 * 2 ^ 59
def prefixEnd_5946062 : Nat := 4983230072969 + 3 ^ 40 * 5946062 * 2
def baseEnd_5946062 : Nat := 1017729269144806746259855

theorem tailTrace_5946062 : CollatzResearch.WordTrace tailWord_5946062 prefixEnd_5946062 1017729269144806746259855 := by
  unfold tailWord_5946062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108837223055044423263055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144580465189626903590736293 27108837223055044423263055)
  ·
    refine ⟨40663255834582566634894583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27108837223055044423263055 40663255834582566634894583)
    ·
      refine ⟨60994883751873849952341875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40663255834582566634894583 60994883751873849952341875)
      ·
        refine ⟨91492325627810774928512813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60994883751873849952341875 91492325627810774928512813)
        ·
          refine ⟨34309622110429040598192305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91492325627810774928512813 34309622110429040598192305)
          ·
            refine ⟨25732216582821780448644229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34309622110429040598192305 25732216582821780448644229)
            ·
              refine ⟨4824790609279083834120793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25732216582821780448644229 4824790609279083834120793)
              ·
                refine ⟨3618592956959312875590595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824790609279083834120793 3618592956959312875590595)
                ·
                  refine ⟨5427889435438969313385893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618592956959312875590595 5427889435438969313385893)
                  ·
                    refine ⟨1017729269144806746259855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5427889435438969313385893 1017729269144806746259855)
                    ·
                      rfl

theorem cell23_5946062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_5946062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946062 prefixEnd_5946062 := by exact prefixLift 5946062
  have htrace : WordTrace (prefixWord ++ tailWord_5946062) baseStart_5946062 baseEnd_5946062 := by
    simpa [prefixWord, tailWord_5946062, baseEnd_5946062] using wordTrace_append hprefix tailTrace_5946062
  have hstable : (prefixWord ++ tailWord_5946062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946062).length < 2 ^ (prefixWord ++ tailWord_5946062).sum := by decide
  have hdescent : baseEnd_5946062 < baseStart_5946062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946071 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 3, 5]
def baseStart_5946071 : Nat := 118140960795 + 5946071 * 2 ^ 59
def prefixEnd_5946071 : Nat := 4983230072969 + 3 ^ 40 * 5946071 * 2
def baseEnd_5946071 : Nat := 1017730809586770234522341

theorem tailTrace_5946071 : CollatzResearch.WordTrace tailWord_5946071 prefixEnd_5946071 1017730809586770234522341 := by
  unfold tailWord_5946071
  simp only [CollatzResearch.WordTrace]
  refine ⟨216871026041407749923182067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144580684027605166615454711 216871026041407749923182067)
  ·
    refine ⟨325306539062111624884773101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216871026041407749923182067 325306539062111624884773101)
    ·
      refine ⟨121989952148291859331789913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325306539062111624884773101 121989952148291859331789913)
      ·
        refine ⟨91492464111218894498842435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121989952148291859331789913 91492464111218894498842435)
        ·
          refine ⟨137238696166828341748263653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91492464111218894498842435 137238696166828341748263653)
          ·
            refine ⟨25732255531280314077799435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137238696166828341748263653 25732255531280314077799435)
            ·
              refine ⟨38598383296920471116699153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25732255531280314077799435 38598383296920471116699153)
              ·
                refine ⟨28948787472690353337524365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38598383296920471116699153 28948787472690353337524365)
                ·
                  refine ⟨10855795302258882501571637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28948787472690353337524365 10855795302258882501571637)
                  ·
                    refine ⟨1017730809586770234522341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10855795302258882501571637 1017730809586770234522341)
                    ·
                      rfl

theorem cell23_5946071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_5946071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946071 prefixEnd_5946071 := by exact prefixLift 5946071
  have htrace : WordTrace (prefixWord ++ tailWord_5946071) baseStart_5946071 baseEnd_5946071 := by
    simpa [prefixWord, tailWord_5946071, baseEnd_5946071] using wordTrace_append hprefix tailTrace_5946071
  have hstable : (prefixWord ++ tailWord_5946071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946071).length < 2 ^ (prefixWord ++ tailWord_5946071).sum := by decide
  have hdescent : baseEnd_5946071 < baseStart_5946071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946085 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5946085 : Nat := 118140960795 + 5946085 * 2 ^ 59
def prefixEnd_5946085 : Nat := 4983230072969 + 3 ^ 40 * 5946085 * 2
def baseEnd_5946085 : Nat := 3053199617489473648791959

theorem tailTrace_5946085 : CollatzResearch.WordTrace tailWord_5946085 prefixEnd_5946085 3053199617489473648791959 := by
  unfold tailWord_5946085
  simp only [CollatzResearch.WordTrace]
  refine ⟨216871536663357030314191709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144581024442238020209461139 216871536663357030314191709)
  ·
    refine ⟨81326826248758886367821891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216871536663357030314191709 81326826248758886367821891)
    ·
      refine ⟨121990239373138329551732837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81326826248758886367821891 121990239373138329551732837)
      ·
        refine ⟨22873169882463436790949907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121990239373138329551732837 22873169882463436790949907)
        ·
          refine ⟨34309754823695155186424861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22873169882463436790949907 34309754823695155186424861)
          ·
            refine ⟨12866158058885683194909323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34309754823695155186424861 12866158058885683194909323)
            ·
              refine ⟨19299237088328524792363985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12866158058885683194909323 19299237088328524792363985)
              ·
                refine ⟨14474427816246393594272989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19299237088328524792363985 14474427816246393594272989)
                ·
                  refine ⟨5427910431092397597852371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14474427816246393594272989 5427910431092397597852371)
                  ·
                    refine ⟨8141865646638596396778557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5427910431092397597852371 8141865646638596396778557)
                    ·
                      refine ⟨3053199617489473648791959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8141865646638596396778557 3053199617489473648791959)
                      ·
                        rfl

theorem cell23_5946085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5946085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946085 prefixEnd_5946085 := by exact prefixLift 5946085
  have htrace : WordTrace (prefixWord ++ tailWord_5946085) baseStart_5946085 baseEnd_5946085 := by
    simpa [prefixWord, tailWord_5946085, baseEnd_5946085] using wordTrace_append hprefix tailTrace_5946085
  have hstable : (prefixWord ++ tailWord_5946085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946085).length < 2 ^ (prefixWord ++ tailWord_5946085).sum := by decide
  have hdescent : baseEnd_5946085 < baseStart_5946085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946095 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 2, 3, 2]
def baseStart_5946095 : Nat := 118140960795 + 5946095 * 2 ^ 59
def prefixEnd_5946095 : Nat := 4983230072969 + 3 ^ 40 * 5946095 * 2
def baseEnd_5946095 : Nat := 3053204752296018609666913

theorem tailTrace_5946095 : CollatzResearch.WordTrace tailWord_5946095 prefixEnd_5946095 3053204752296018609666913 := by
  unfold tailWord_5946095
  simp only [CollatzResearch.WordTrace]
  refine ⟨216871901393320802022055739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144581267595547201348037159 216871901393320802022055739)
  ·
    refine ⟨325307852089981203033083609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216871901393320802022055739 325307852089981203033083609)
    ·
      refine ⟨243980889067485902274812707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325307852089981203033083609 243980889067485902274812707)
      ·
        refine ⟨365971333601228853412219061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243980889067485902274812707 365971333601228853412219061)
        ·
          refine ⟨34309812525115205007395537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365971333601228853412219061 34309812525115205007395537)
          ·
            refine ⟨25732359393836403755546653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34309812525115205007395537 25732359393836403755546653)
            ·
              refine ⟨9649634772688651408329995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25732359393836403755546653 9649634772688651408329995)
              ·
                refine ⟨14474452159032977112494993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9649634772688651408329995 14474452159032977112494993)
                ·
                  refine ⟨10855839119274732834371245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14474452159032977112494993 10855839119274732834371245)
                  ·
                    refine ⟨4070939669728024812889217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10855839119274732834371245 4070939669728024812889217)
                    ·
                      refine ⟨3053204752296018609666913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4070939669728024812889217 3053204752296018609666913)
                      ·
                        rfl

theorem cell23_5946095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3, 2].length) (baseStart_5946095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946095 prefixEnd_5946095 := by exact prefixLift 5946095
  have htrace : WordTrace (prefixWord ++ tailWord_5946095) baseStart_5946095 baseEnd_5946095 := by
    simpa [prefixWord, tailWord_5946095, baseEnd_5946095] using wordTrace_append hprefix tailTrace_5946095
  have hstable : (prefixWord ++ tailWord_5946095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946095).length < 2 ^ (prefixWord ++ tailWord_5946095).sum := by decide
  have hdescent : baseEnd_5946095 < baseStart_5946095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946111 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_5946111 : Nat := 118140960795 + 5946111 * 2 ^ 59
def prefixEnd_5946111 : Nat := 4983230072969 + 3 ^ 40 * 5946111 * 2
def baseEnd_5946111 : Nat := 3053212967986490547066839

theorem tailTrace_5946111 : CollatzResearch.WordTrace tailWord_5946111 prefixEnd_5946111 3053212967986490547066839 := by
  unfold tailWord_5946111
  simp only [CollatzResearch.WordTrace]
  refine ⟨216872484961262836754638187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144581656640841891169758791 216872484961262836754638187)
  ·
    refine ⟨325308727441894255131957281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216872484961262836754638187 325308727441894255131957281)
    ·
      refine ⟨243981545581420691348967961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325308727441894255131957281 243981545581420691348967961)
      ·
        refine ⟨182986159186065518511725971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243981545581420691348967961 182986159186065518511725971)
        ·
          refine ⟨274479238779098277767588957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182986159186065518511725971 274479238779098277767588957)
          ·
            refine ⟨102929714542161854162845859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274479238779098277767588957 102929714542161854162845859)
            ·
              refine ⟨154394571813242781244268789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102929714542161854162845859 154394571813242781244268789)
              ·
                refine ⟨14474491107491510741650199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154394571813242781244268789 14474491107491510741650199)
                ·
                  refine ⟨21711736661237266112475299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14474491107491510741650199 21711736661237266112475299)
                  ·
                    refine ⟨32567604991855899168712949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21711736661237266112475299 32567604991855899168712949)
                    ·
                      refine ⟨3053212967986490547066839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32567604991855899168712949 3053212967986490547066839)
                      ·
                        rfl

theorem cell23_5946111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_5946111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946111 prefixEnd_5946111 := by exact prefixLift 5946111
  have htrace : WordTrace (prefixWord ++ tailWord_5946111) baseStart_5946111 baseEnd_5946111 := by
    simpa [prefixWord, tailWord_5946111, baseEnd_5946111] using wordTrace_append hprefix tailTrace_5946111
  have hstable : (prefixWord ++ tailWord_5946111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946111).length < 2 ^ (prefixWord ++ tailWord_5946111).sum := by decide
  have hdescent : baseEnd_5946111 < baseStart_5946111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946121 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_5946121 : Nat := 118140960795 + 5946121 * 2 ^ 59
def prefixEnd_5946121 : Nat := 4983230072969 + 3 ^ 40 * 5946121 * 2
def baseEnd_5946121 : Nat := 3053218102793035507941793

theorem tailTrace_5946121 : CollatzResearch.WordTrace tailWord_5946121 prefixEnd_5946121 3053218102793035507941793 := by
  unfold tailWord_5946121
  simp only [CollatzResearch.WordTrace]
  refine ⟨216872849691226608462502217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144581899794151072308334811 216872849691226608462502217)
  ·
    refine ⟨162654637268419956346876663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216872849691226608462502217 162654637268419956346876663)
    ·
      refine ⟨243981955902629934520314995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162654637268419956346876663 243981955902629934520314995)
      ·
        refine ⟨365972933853944901780472493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243981955902629934520314995 365972933853944901780472493)
        ·
          refine ⟨137239850195229338167677185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365972933853944901780472493 137239850195229338167677185)
          ·
            refine ⟨102929887646422003625757889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137239850195229338167677185 102929887646422003625757889)
            ·
              refine ⟨77197415734816502719318417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102929887646422003625757889 77197415734816502719318417)
              ·
                refine ⟨57898061801112377039488813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77197415734816502719318417 57898061801112377039488813)
                ·
                  refine ⟨21711773175417141389808305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57898061801112377039488813 21711773175417141389808305)
                  ·
                    refine ⟨16283829881562856042356229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21711773175417141389808305 16283829881562856042356229)
                    ·
                      refine ⟨3053218102793035507941793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16283829881562856042356229 3053218102793035507941793)
                      ·
                        rfl

theorem cell23_5946121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_5946121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946121 prefixEnd_5946121 := by exact prefixLift 5946121
  have htrace : WordTrace (prefixWord ++ tailWord_5946121) baseStart_5946121 baseEnd_5946121 := by
    simpa [prefixWord, tailWord_5946121, baseEnd_5946121] using wordTrace_append hprefix tailTrace_5946121
  have hstable : (prefixWord ++ tailWord_5946121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946121).length < 2 ^ (prefixWord ++ tailWord_5946121).sum := by decide
  have hdescent : baseEnd_5946121 < baseStart_5946121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946135 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 1, 6]
def baseStart_5946135 : Nat := 118140960795 + 5946135 * 2 ^ 59
def prefixEnd_5946135 : Nat := 4983230072969 + 3 ^ 40 * 5946135 * 2
def baseEnd_5946135 : Nat := 1017741763840732817722243

theorem tailTrace_5946135 : CollatzResearch.WordTrace tailWord_5946135 prefixEnd_5946135 1017741763840732817722243 := by
  unfold tailWord_5946135
  simp only [CollatzResearch.WordTrace]
  refine ⟨216873360313175888853511859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144582240208783925902341239 216873360313175888853511859)
  ·
    refine ⟨325310040469763833280267789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216873360313175888853511859 325310040469763833280267789)
    ·
      refine ⟨121991265176161437480100421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325310040469763833280267789 121991265176161437480100421)
      ·
        refine ⟨22873362220530269527518829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121991265176161437480100421 22873362220530269527518829)
        ·
          refine ⟨8577510832698851072819561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22873362220530269527518829 8577510832698851072819561)
          ·
            refine ⟨6433133124524138304614671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8577510832698851072819561 6433133124524138304614671)
            ·
              refine ⟨9649699686786207456922007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433133124524138304614671 9649699686786207456922007)
              ·
                refine ⟨14474549530179311185383011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9649699686786207456922007 14474549530179311185383011)
                ·
                  refine ⟨21711824295268966778074517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14474549530179311185383011 21711824295268966778074517)
                  ·
                    refine ⟨1017741763840732817722243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21711824295268966778074517 1017741763840732817722243)
                    ·
                      rfl

theorem cell23_5946135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_5946135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946135 prefixEnd_5946135 := by exact prefixLift 5946135
  have htrace : WordTrace (prefixWord ++ tailWord_5946135) baseStart_5946135 baseEnd_5946135 := by
    simpa [prefixWord, tailWord_5946135, baseEnd_5946135] using wordTrace_append hprefix tailTrace_5946135
  have hstable : (prefixWord ++ tailWord_5946135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946135).length < 2 ^ (prefixWord ++ tailWord_5946135).sum := by decide
  have hdescent : baseEnd_5946135 < baseStart_5946135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946145 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5946145 : Nat := 118140960795 + 5946145 * 2 ^ 59
def prefixEnd_5946145 : Nat := 4983230072969 + 3 ^ 40 * 5946145 * 2
def baseEnd_5946145 : Nat := 3053230426328743414041683

theorem tailTrace_5946145 : CollatzResearch.WordTrace tailWord_5946145 prefixEnd_5946145 3053230426328743414041683 := by
  unfold tailWord_5946145
  simp only [CollatzResearch.WordTrace]
  refine ⟨216873725043139660561375889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144582483362093107040917259 216873725043139660561375889)
  ·
    refine ⟨162655293782354745421031917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216873725043139660561375889 162655293782354745421031917)
    ·
      refine ⟨60995735168383029532886969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162655293782354745421031917 60995735168383029532886969)
      ·
        refine ⟨45746801376287272149665227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60995735168383029532886969 45746801376287272149665227)
        ·
          refine ⟨68620202064430908224497841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45746801376287272149665227 68620202064430908224497841)
          ·
            refine ⟨51465151548323181168373381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68620202064430908224497841 51465151548323181168373381)
            ·
              refine ⟨9649715915310596469070009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51465151548323181168373381 9649715915310596469070009)
              ·
                refine ⟨7237286936482947351802507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9649715915310596469070009 7237286936482947351802507)
                ·
                  refine ⟨10855930404724421027703761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7237286936482947351802507 10855930404724421027703761)
                  ·
                    refine ⟨8141947803543315770777821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10855930404724421027703761 8141947803543315770777821)
                    ·
                      refine ⟨3053230426328743414041683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8141947803543315770777821 3053230426328743414041683)
                      ·
                        rfl

theorem cell23_5946145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5946145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946145 prefixEnd_5946145 := by exact prefixLift 5946145
  have htrace : WordTrace (prefixWord ++ tailWord_5946145) baseStart_5946145 baseEnd_5946145 := by
    simpa [prefixWord, tailWord_5946145, baseEnd_5946145] using wordTrace_append hprefix tailTrace_5946145
  have hstable : (prefixWord ++ tailWord_5946145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946145).length < 2 ^ (prefixWord ++ tailWord_5946145).sum := by decide
  have hdescent : baseEnd_5946145 < baseStart_5946145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946148 : List Nat := [2, 3, 1, 3, 3, 1, 1, 9]
def baseStart_5946148 : Nat := 118140960795 + 5946148 * 2 ^ 59
def prefixEnd_5946148 : Nat := 4983230072969 + 3 ^ 40 * 5946148 * 2
def baseEnd_5946148 : Nat := 113082665435952107492747

theorem tailTrace_5946148 : CollatzResearch.WordTrace tailWord_5946148 prefixEnd_5946148 113082665435952107492747 := by
  unfold tailWord_5946148
  simp only [CollatzResearch.WordTrace]
  refine ⟨108436917231064396036867549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144582556308085861382490065 108436917231064396036867549)
  ·
    refine ⟨40663843961649148513825331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108436917231064396036867549 40663843961649148513825331)
    ·
      refine ⟨60995765942473722770737997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40663843961649148513825331 60995765942473722770737997)
      ·
        refine ⟨22873412228427646039026749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60995765942473722770737997 22873412228427646039026749)
        ·
          refine ⟨8577529585660367264635031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22873412228427646039026749 8577529585660367264635031)
          ·
            refine ⟨12866294378490550896952547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577529585660367264635031 12866294378490550896952547)
            ·
              refine ⟨19299441567735826345428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12866294378490550896952547 19299441567735826345428821)
              ·
                refine ⟨113082665435952107492747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19299441567735826345428821 113082665435952107492747)
                ·
                  rfl

theorem cell23_5946148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 9].length) (baseStart_5946148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946148 prefixEnd_5946148 := by exact prefixLift 5946148
  have htrace : WordTrace (prefixWord ++ tailWord_5946148) baseStart_5946148 baseEnd_5946148 := by
    simpa [prefixWord, tailWord_5946148, baseEnd_5946148] using wordTrace_append hprefix tailTrace_5946148
  have hstable : (prefixWord ++ tailWord_5946148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946148).length < 2 ^ (prefixWord ++ tailWord_5946148).sum := by decide
  have hdescent : baseEnd_5946148 < baseStart_5946148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946175 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 3]
def baseStart_5946175 : Nat := 118140960795 + 5946175 * 2 ^ 59
def prefixEnd_5946175 : Nat := 4983230072969 + 3 ^ 40 * 5946175 * 2
def baseEnd_5946175 : Nat := 3053245830748378296666545

theorem tailTrace_5946175 : CollatzResearch.WordTrace tailWord_5946175 prefixEnd_5946175 3053245830748378296666545 := by
  unfold tailWord_5946175
  simp only [CollatzResearch.WordTrace]
  refine ⟨216874819233030975684967979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144583212822020650456645319 216874819233030975684967979)
  ·
    refine ⟨325312228849546463527451969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216874819233030975684967979 325312228849546463527451969)
    ·
      refine ⟨243984171637159847645588977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325312228849546463527451969 243984171637159847645588977)
      ·
        refine ⟨182988128727869885734191733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243984171637159847645588977 182988128727869885734191733)
        ·
          refine ⟨17155137068237801787580475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182988128727869885734191733 17155137068237801787580475)
          ·
            refine ⟨25732705602356702681370713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17155137068237801787580475 25732705602356702681370713)
            ·
              refine ⟨19299529201767527011028035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25732705602356702681370713 19299529201767527011028035)
              ·
                refine ⟨28949293802651290516542053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19299529201767527011028035 28949293802651290516542053)
                ·
                  refine ⟨5427992587997116971851635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28949293802651290516542053 5427992587997116971851635)
                  ·
                    refine ⟨8141988881995675457777453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5427992587997116971851635 8141988881995675457777453)
                    ·
                      refine ⟨3053245830748378296666545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8141988881995675457777453 3053245830748378296666545)
                      ·
                        rfl

theorem cell23_5946175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_5946175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946175 prefixEnd_5946175 := by exact prefixLift 5946175
  have htrace : WordTrace (prefixWord ++ tailWord_5946175) baseStart_5946175 baseEnd_5946175 := by
    simpa [prefixWord, tailWord_5946175, baseEnd_5946175] using wordTrace_append hprefix tailTrace_5946175
  have hstable : (prefixWord ++ tailWord_5946175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946175).length < 2 ^ (prefixWord ++ tailWord_5946175).sum := by decide
  have hdescent : baseEnd_5946175 < baseStart_5946175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946182 : List Nat := [6, 1, 1, 2, 2, 1, 2, 8]
def baseStart_5946182 : Nat := 118140960795 + 5946182 * 2 ^ 59
def prefixEnd_5946182 : Nat := 4983230072969 + 3 ^ 40 * 5946182 * 2
def baseEnd_5946182 : Nat := 113083312041220732195519

theorem tailTrace_5946182 : CollatzResearch.WordTrace tailWord_5946182 prefixEnd_5946182 113083312041220732195519 := by
  unfold tailWord_5946182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6777346079500175496264775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144583383029337077253648533 6777346079500175496264775)
  ·
    refine ⟨10166019119250263244397163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6777346079500175496264775 10166019119250263244397163)
    ·
      refine ⟨15249028678875394866595745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10166019119250263244397163 15249028678875394866595745)
      ·
        refine ⟨11436771509156546149946809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15249028678875394866595745 11436771509156546149946809)
        ·
          refine ⟨8577578631867409612460107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11436771509156546149946809 8577578631867409612460107)
          ·
            refine ⟨12866367947801114418690161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577578631867409612460107 12866367947801114418690161)
            ·
              refine ⟨9649775960850835814017621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12866367947801114418690161 9649775960850835814017621)
              ·
                refine ⟨113083312041220732195519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9649775960850835814017621 113083312041220732195519)
                ·
                  rfl

theorem cell23_5946182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_5946182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946182 prefixEnd_5946182 := by exact prefixLift 5946182
  have htrace : WordTrace (prefixWord ++ tailWord_5946182) baseStart_5946182 baseEnd_5946182 := by
    simpa [prefixWord, tailWord_5946182, baseEnd_5946182] using wordTrace_append hprefix tailTrace_5946182
  have hstable : (prefixWord ++ tailWord_5946182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946182).length < 2 ^ (prefixWord ++ tailWord_5946182).sum := by decide
  have hdescent : baseEnd_5946182 < baseStart_5946182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946192 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3]
def baseStart_5946192 : Nat := 118140960795 + 5946192 * 2 ^ 59
def prefixEnd_5946192 : Nat := 4983230072969 + 3 ^ 40 * 5946192 * 2
def baseEnd_5946192 : Nat := 3053254559919504730153967

theorem tailTrace_5946192 : CollatzResearch.WordTrace tailWord_5946192 prefixEnd_5946192 3053254559919504730153967 := by
  unfold tailWord_5946192
  simp only [CollatzResearch.WordTrace]
  refine ⟨108437719636984693794168415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144583626182646258392224553 108437719636984693794168415)
  ·
    refine ⟨162656579455477040691252623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108437719636984693794168415 162656579455477040691252623)
    ·
      refine ⟨243984869183215561036878935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162656579455477040691252623 243984869183215561036878935)
      ·
        refine ⟨365977303774823341555318403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243984869183215561036878935 365977303774823341555318403)
        ·
          refine ⟨548965955662235012332977605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365977303774823341555318403 548965955662235012332977605)
          ·
            refine ⟨102931116686669064812433301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 548965955662235012332977605 102931116686669064812433301)
            ·
              refine ⟨4824896094687612413082811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102931116686669064812433301 4824896094687612413082811)
              ·
                refine ⟨7237344142031418619624217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824896094687612413082811 7237344142031418619624217)
                ·
                  refine ⟨5428008106523563964718163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7237344142031418619624217 5428008106523563964718163)
                  ·
                    refine ⟨8142012159785345947077245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5428008106523563964718163 8142012159785345947077245)
                    ·
                      refine ⟨3053254559919504730153967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8142012159785345947077245 3053254559919504730153967)
                      ·
                        rfl

theorem cell23_5946192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3].length) (baseStart_5946192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946192 prefixEnd_5946192 := by exact prefixLift 5946192
  have htrace : WordTrace (prefixWord ++ tailWord_5946192) baseStart_5946192 baseEnd_5946192 := by
    simpa [prefixWord, tailWord_5946192, baseEnd_5946192] using wordTrace_append hprefix tailTrace_5946192
  have hstable : (prefixWord ++ tailWord_5946192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946192).length < 2 ^ (prefixWord ++ tailWord_5946192).sum := by decide
  have hdescent : baseEnd_5946192 < baseStart_5946192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946202 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_5946202 : Nat := 118140960795 + 5946202 * 2 ^ 59
def prefixEnd_5946202 : Nat := 4983230072969 + 3 ^ 40 * 5946202 * 2
def baseEnd_5946202 : Nat := 3053259694726049691028921

theorem tailTrace_5946202 : CollatzResearch.WordTrace tailWord_5946202 prefixEnd_5946202 3053259694726049691028921 := by
  unfold tailWord_5946202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54218951000983289824050215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144583869335955439530800573 54218951000983289824050215)
  ·
    refine ⟨81328426501474934736075323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54218951000983289824050215 81328426501474934736075323)
    ·
      refine ⟨121992639752212402104112985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81328426501474934736075323 121992639752212402104112985)
      ·
        refine ⟨91494479814159301578084739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121992639752212402104112985 91494479814159301578084739)
        ·
          refine ⟨137241719721238952367127109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91494479814159301578084739 137241719721238952367127109)
          ·
            refine ⟨25732822447732303568836333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137241719721238952367127109 25732822447732303568836333)
            ·
              refine ⟨9649808417899613838313625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25732822447732303568836333 9649808417899613838313625)
              ·
                refine ⟨7237356313424710378735219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9649808417899613838313625 7237356313424710378735219)
                ·
                  refine ⟨10856034470137065568102829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7237356313424710378735219 10856034470137065568102829)
                  ·
                    refine ⟨4071012926301399588038561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10856034470137065568102829 4071012926301399588038561)
                    ·
                      refine ⟨3053259694726049691028921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071012926301399588038561 3053259694726049691028921)
                      ·
                        rfl

theorem cell23_5946202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_5946202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946202 prefixEnd_5946202 := by exact prefixLift 5946202
  have htrace : WordTrace (prefixWord ++ tailWord_5946202) baseStart_5946202 baseEnd_5946202 := by
    simpa [prefixWord, tailWord_5946202, baseEnd_5946202] using wordTrace_append hprefix tailTrace_5946202
  have hstable : (prefixWord ++ tailWord_5946202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946202).length < 2 ^ (prefixWord ++ tailWord_5946202).sum := by decide
  have hdescent : baseEnd_5946202 < baseStart_5946202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946215 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_5946215 : Nat := 118140960795 + 5946215 * 2 ^ 59
def prefixEnd_5946215 : Nat := 4983230072969 + 3 ^ 40 * 5946215 * 2
def baseEnd_5946215 : Nat := 3053266369974558140166361

theorem tailTrace_5946215 : CollatzResearch.WordTrace tailWord_5946215 prefixEnd_5946215 3053266369974558140166361 := by
  unfold tailWord_5946215
  simp only [CollatzResearch.WordTrace]
  refine ⟨216876278152886062516424099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144584185435257375010949399 216876278152886062516424099)
  ·
    refine ⟨325314417229329093774636149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216876278152886062516424099 325314417229329093774636149)
    ·
      refine ⟨30498226615249602541372139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325314417229329093774636149 30498226615249602541372139)
      ·
        refine ⟨45747339922874403812058209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30498226615249602541372139 45747339922874403812058209)
        ·
          refine ⟨34310504942155802859043657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45747339922874403812058209 34310504942155802859043657)
          ·
            refine ⟨25732878706616852144282743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34310504942155802859043657 25732878706616852144282743)
            ·
              refine ⟨38599318059925278216424115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25732878706616852144282743 38599318059925278216424115)
              ·
                refine ⟨57898977089887917324636173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38599318059925278216424115 57898977089887917324636173)
                ·
                  refine ⟨21712116408707968996738565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57898977089887917324636173 21712116408707968996738565)
                  ·
                    refine ⟨4071021826632744186888481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21712116408707968996738565 4071021826632744186888481)
                    ·
                      refine ⟨3053266369974558140166361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071021826632744186888481 3053266369974558140166361)
                      ·
                        rfl

theorem cell23_5946215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_5946215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946215 prefixEnd_5946215 := by exact prefixLift 5946215
  have htrace : WordTrace (prefixWord ++ tailWord_5946215) baseStart_5946215 baseEnd_5946215 := by
    simpa [prefixWord, tailWord_5946215, baseEnd_5946215] using wordTrace_append hprefix tailTrace_5946215
  have hstable : (prefixWord ++ tailWord_5946215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946215).length < 2 ^ (prefixWord ++ tailWord_5946215).sum := by decide
  have hdescent : baseEnd_5946215 < baseStart_5946215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946231 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_5946231 : Nat := 118140960795 + 5946231 * 2 ^ 59
def prefixEnd_5946231 : Nat := 4983230072969 + 3 ^ 40 * 5946231 * 2
def baseEnd_5946231 : Nat := 3053274585665030077566287

theorem tailTrace_5946231 : CollatzResearch.WordTrace tailWord_5946231 prefixEnd_5946231 3053274585665030077566287 := by
  unfold tailWord_5946231
  simp only [CollatzResearch.WordTrace]
  refine ⟨216876861720828097249006547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144584574480552064832671031 216876861720828097249006547)
  ·
    refine ⟨325315292581242145873509821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216876861720828097249006547 325315292581242145873509821)
    ·
      refine ⟨121993234717965804702566183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325315292581242145873509821 121993234717965804702566183)
      ·
        refine ⟨182989852076948707053849275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121993234717965804702566183 182989852076948707053849275)
        ·
          refine ⟨274484778115423060580773913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182989852076948707053849275 274484778115423060580773913)
          ·
            refine ⟨205863583586567295435580435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274484778115423060580773913 205863583586567295435580435)
            ·
              refine ⟨308795375379850943153370653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205863583586567295435580435 308795375379850943153370653)
              ·
                refine ⟨115798265767444103682513995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308795375379850943153370653 115798265767444103682513995)
                ·
                  refine ⟨173697398651166155523770993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115798265767444103682513995 173697398651166155523770993)
                  ·
                    refine ⟨130273048988374616642828245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173697398651166155523770993 130273048988374616642828245)
                    ·
                      refine ⟨3053274585665030077566287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130273048988374616642828245 3053274585665030077566287)
                      ·
                        rfl

theorem cell23_5946231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_5946231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946231 prefixEnd_5946231 := by exact prefixLift 5946231
  have htrace : WordTrace (prefixWord ++ tailWord_5946231) baseStart_5946231 baseEnd_5946231 := by
    simpa [prefixWord, tailWord_5946231, baseEnd_5946231] using wordTrace_append hprefix tailTrace_5946231
  have hstable : (prefixWord ++ tailWord_5946231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946231).length < 2 ^ (prefixWord ++ tailWord_5946231).sum := by decide
  have hdescent : baseEnd_5946231 < baseStart_5946231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946315 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 3, 4]
def baseStart_5946315 : Nat := 118140960795 + 5946315 * 2 ^ 59
def prefixEnd_5946315 : Nat := 4983230072969 + 3 ^ 40 * 5946315 * 2
def baseEnd_5946315 : Nat := 1017772572680002582971967

theorem tailTrace_5946315 : CollatzResearch.WordTrace tailWord_5946315 prefixEnd_5946315 1017772572680002582971967 := by
  unfold tailWord_5946315
  simp only [CollatzResearch.WordTrace]
  refine ⟨216879925452523779595064399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144586616968349186396709599 216879925452523779595064399)
  ·
    refine ⟨325319888178785669392596599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216879925452523779595064399 325319888178785669392596599)
    ·
      refine ⟨487979832268178504088894899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325319888178785669392596599 487979832268178504088894899)
      ·
        refine ⟨731969748402267756133342349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487979832268178504088894899 731969748402267756133342349)
        ·
          refine ⟨274488655650850408550003381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731969748402267756133342349 274488655650850408550003381)
          ·
            refine ⟨25733311467267225801562817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274488655650850408550003381 25733311467267225801562817)
            ·
              refine ⟨19299983600450419351172113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25733311467267225801562817 19299983600450419351172113)
              ·
                refine ⟨14474987700337814513379085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19299983600450419351172113 14474987700337814513379085)
                ·
                  refine ⟨5428120387626680442517157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14474987700337814513379085 5428120387626680442517157)
                  ·
                    refine ⟨1017772572680002582971967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5428120387626680442517157 1017772572680002582971967)
                    ·
                      rfl

theorem cell23_5946315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 4].length) (baseStart_5946315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946315 prefixEnd_5946315 := by exact prefixLift 5946315
  have htrace : WordTrace (prefixWord ++ tailWord_5946315) baseStart_5946315 baseEnd_5946315 := by
    simpa [prefixWord, tailWord_5946315, baseEnd_5946315] using wordTrace_append hprefix tailTrace_5946315
  have hstable : (prefixWord ++ tailWord_5946315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946315).length < 2 ^ (prefixWord ++ tailWord_5946315).sum := by decide
  have hdescent : baseEnd_5946315 < baseStart_5946315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946328 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 8]
def baseStart_5946328 : Nat := 118140960795 + 5946328 * 2 ^ 59
def prefixEnd_5946328 : Nat := 4983230072969 + 3 ^ 40 * 5946328 * 2
def baseEnd_5946328 : Nat := 339258265920946244228149

theorem tailTrace_5946328 : CollatzResearch.WordTrace tailWord_5946328 prefixEnd_5946328 339258265920946244228149 := by
  unfold tailWord_5946328
  simp only [CollatzResearch.WordTrace]
  refine ⟨108440199800738341407643819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144586933067651121876858425 108440199800738341407643819)
  ·
    refine ⟨162660299701107512111465729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108440199800738341407643819 162660299701107512111465729)
    ·
      refine ⟨121995224775830634083599297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162660299701107512111465729 121995224775830634083599297)
      ·
        refine ⟨91496418581872975562699473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121995224775830634083599297 91496418581872975562699473)
        ·
          refine ⟨68622313936404731672024605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91496418581872975562699473 68622313936404731672024605)
          ·
            refine ⟨25733367726151774377009227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68622313936404731672024605 25733367726151774377009227)
            ·
              refine ⟨38600051589227661565513841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25733367726151774377009227 38600051589227661565513841)
              ·
                refine ⟨28950038691920746174135381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38600051589227661565513841 28950038691920746174135381)
                ·
                  refine ⟨339258265920946244228149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28950038691920746174135381 339258265920946244228149)
                  ·
                    rfl

theorem cell23_5946328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_5946328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946328 prefixEnd_5946328 := by exact prefixLift 5946328
  have htrace : WordTrace (prefixWord ++ tailWord_5946328) baseStart_5946328 baseEnd_5946328 := by
    simpa [prefixWord, tailWord_5946328, baseEnd_5946328] using wordTrace_append hprefix tailTrace_5946328
  have hstable : (prefixWord ++ tailWord_5946328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946328).length < 2 ^ (prefixWord ++ tailWord_5946328).sum := by decide
  have hdescent : baseEnd_5946328 < baseStart_5946328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946375 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 3, 5]
def baseStart_5946375 : Nat := 118140960795 + 5946375 * 2 ^ 59
def prefixEnd_5946375 : Nat := 4983230072969 + 3 ^ 40 * 5946375 * 2
def baseEnd_5946375 : Nat := 1017782842293092504721875

theorem tailTrace_5946375 : CollatzResearch.WordTrace tailWord_5946375 prefixEnd_5946375 1017782842293092504721875 := by
  unfold tailWord_5946375
  simp only [CollatzResearch.WordTrace]
  refine ⟨216882113832306409842248579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144588075888204273228165719 216882113832306409842248579)
  ·
    refine ⟨325323170748459614763372869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216882113832306409842248579 325323170748459614763372869)
    ·
      refine ⟨60998094515336177768132413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325323170748459614763372869 60998094515336177768132413)
      ·
        refine ⟨22874285443251066663049655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60998094515336177768132413 22874285443251066663049655)
        ·
          refine ⟨34311428164876599994574483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22874285443251066663049655 34311428164876599994574483)
          ·
            refine ⟨51467142247314899991861725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34311428164876599994574483 51467142247314899991861725)
            ·
              refine ⟨19300178342743087496948147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51467142247314899991861725 19300178342743087496948147)
              ·
                refine ⟨28950267514114631245422221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19300178342743087496948147 28950267514114631245422221)
                ·
                  refine ⟨10856350317792986717033333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28950267514114631245422221 10856350317792986717033333)
                  ·
                    refine ⟨1017782842293092504721875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10856350317792986717033333 1017782842293092504721875)
                    ·
                      rfl

theorem cell23_5946375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_5946375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946375 prefixEnd_5946375 := by exact prefixLift 5946375
  have htrace : WordTrace (prefixWord ++ tailWord_5946375) baseStart_5946375 baseEnd_5946375 := by
    simpa [prefixWord, tailWord_5946375, baseEnd_5946375] using wordTrace_append hprefix tailTrace_5946375
  have hstable : (prefixWord ++ tailWord_5946375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946375).length < 2 ^ (prefixWord ++ tailWord_5946375).sum := by decide
  have hdescent : baseEnd_5946375 < baseStart_5946375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946395 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 6, 2]
def baseStart_5946395 : Nat := 118140960795 + 5946395 * 2 ^ 59
def prefixEnd_5946395 : Nat := 4983230072969 + 3 ^ 40 * 5946395 * 2
def baseEnd_5946395 : Nat := 3053358796492367435915533

theorem tailTrace_5946395 : CollatzResearch.WordTrace tailWord_5946395 prefixEnd_5946395 3053358796492367435915533 := by
  unfold tailWord_5946395
  simp only [CollatzResearch.WordTrace]
  refine ⟨216882843292233953257976639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144588562194822635505317759 216882843292233953257976639)
  ·
    refine ⟨325324264938350929886964959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216882843292233953257976639 325324264938350929886964959)
    ·
      refine ⟨487986397407526394830447439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325324264938350929886964959 487986397407526394830447439)
      ·
        refine ⟨731979596111289592245671159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487986397407526394830447439 731979596111289592245671159)
        ·
          refine ⟨1097969394166934388368506739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731979596111289592245671159 1097969394166934388368506739)
          ·
            refine ⟨1646954091250401582552760109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097969394166934388368506739 1646954091250401582552760109)
            ·
              refine ⟨617607784218900593457285041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646954091250401582552760109 617607784218900593457285041)
              ·
                refine ⟨463205838164175445092963781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617607784218900593457285041 463205838164175445092963781)
                ·
                  refine ⟨86851094655782895954930709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463205838164175445092963781 86851094655782895954930709)
                  ·
                    refine ⟨4071145061989823247887377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86851094655782895954930709 4071145061989823247887377)
                    ·
                      refine ⟨3053358796492367435915533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071145061989823247887377 3053358796492367435915533)
                      ·
                        rfl

theorem cell23_5946395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6, 2].length) (baseStart_5946395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946395 prefixEnd_5946395 := by exact prefixLift 5946395
  have htrace : WordTrace (prefixWord ++ tailWord_5946395) baseStart_5946395 baseEnd_5946395 := by
    simpa [prefixWord, tailWord_5946395, baseEnd_5946395] using wordTrace_append hprefix tailTrace_5946395
  have hstable : (prefixWord ++ tailWord_5946395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946395).length < 2 ^ (prefixWord ++ tailWord_5946395).sum := by decide
  have hdescent : baseEnd_5946395 < baseStart_5946395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946400 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 1, 4]
def baseStart_5946400 : Nat := 118140960795 + 5946400 * 2 ^ 59
def prefixEnd_5946400 : Nat := 4983230072969 + 3 ^ 40 * 5946400 * 2
def baseEnd_5946400 : Nat := 1017787121298546638784337

theorem tailTrace_5946400 : CollatzResearch.WordTrace tailWord_5946400 prefixEnd_5946400 1017787121298546638784337 := by
  unfold tailWord_5946400
  simp only [CollatzResearch.WordTrace]
  refine ⟨108441512828607919555954327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144588683771477226074605769 108441512828607919555954327)
  ·
    refine ⟨162662269242911879333931491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108441512828607919555954327 162662269242911879333931491)
    ·
      refine ⟨243993403864367819000897237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162662269242911879333931491 243993403864367819000897237)
      ·
        refine ⟨5718595403071120757833529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 243993403864367819000897237 5718595403071120757833529)
        ·
          refine ⟨4288946552303340568375147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718595403071120757833529 4288946552303340568375147)
          ·
            refine ⟨6433419828455010852562721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288946552303340568375147 6433419828455010852562721)
            ·
              refine ⟨4825064871341258139422041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6433419828455010852562721 4825064871341258139422041)
              ·
                refine ⟨3618798653505943604566531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4825064871341258139422041 3618798653505943604566531)
                ·
                  refine ⟨5428197980258915406849797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618798653505943604566531 5428197980258915406849797)
                  ·
                    refine ⟨1017787121298546638784337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5428197980258915406849797 1017787121298546638784337)
                    ·
                      rfl

theorem cell23_5946400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 4].length) (baseStart_5946400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946400 prefixEnd_5946400 := by exact prefixLift 5946400
  have htrace : WordTrace (prefixWord ++ tailWord_5946400) baseStart_5946400 baseEnd_5946400 := by
    simpa [prefixWord, tailWord_5946400, baseEnd_5946400] using wordTrace_append hprefix tailTrace_5946400
  have hstable : (prefixWord ++ tailWord_5946400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946400).length < 2 ^ (prefixWord ++ tailWord_5946400).sum := by decide
  have hdescent : baseEnd_5946400 < baseStart_5946400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946422 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5946422 : Nat := 118140960795 + 5946422 * 2 ^ 59
def prefixEnd_5946422 : Nat := 4983230072969 + 3 ^ 40 * 5946422 * 2
def baseEnd_5946422 : Nat := 1017790886823346276759303

theorem tailTrace_5946422 : CollatzResearch.WordTrace tailWord_5946422 prefixEnd_5946422 1017790886823346276759303 := by
  unfold tailWord_5946422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13555239253946008554325595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144589218708757424579473013 13555239253946008554325595)
  ·
    refine ⟨20332858880919012831488393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13555239253946008554325595 20332858880919012831488393)
    ·
      refine ⟨15249644160689259623616295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20332858880919012831488393 15249644160689259623616295)
      ·
        refine ⟨22874466241033889435424443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15249644160689259623616295 22874466241033889435424443)
        ·
          refine ⟨34311699361550834153136665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22874466241033889435424443 34311699361550834153136665)
          ·
            refine ⟨25733774521163125614852499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34311699361550834153136665 25733774521163125614852499)
            ·
              refine ⟨38600661781744688422278749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25733774521163125614852499 38600661781744688422278749)
              ·
                refine ⟨14475248168154258158354531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38600661781744688422278749 14475248168154258158354531)
                ·
                  refine ⟨21712872252231387237531797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14475248168154258158354531 21712872252231387237531797)
                  ·
                    refine ⟨1017790886823346276759303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21712872252231387237531797 1017790886823346276759303)
                    ·
                      rfl

theorem cell23_5946422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5946422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946422 prefixEnd_5946422 := by exact prefixLift 5946422
  have htrace : WordTrace (prefixWord ++ tailWord_5946422) baseStart_5946422 baseEnd_5946422 := by
    simpa [prefixWord, tailWord_5946422, baseEnd_5946422] using wordTrace_append hprefix tailTrace_5946422
  have hstable : (prefixWord ++ tailWord_5946422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946422).length < 2 ^ (prefixWord ++ tailWord_5946422).sum := by decide
  have hdescent : baseEnd_5946422 < baseStart_5946422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946429 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5946429 : Nat := 118140960795 + 5946429 * 2 ^ 59
def prefixEnd_5946429 : Nat := 4983230072969 + 3 ^ 40 * 5946429 * 2
def baseEnd_5946429 : Nat := 3053376254834620302890377

theorem tailTrace_5946429 : CollatzResearch.WordTrace tailWord_5946429 prefixEnd_5946429 3053376254834620302890377 := by
  unfold tailWord_5946429
  simp only [CollatzResearch.WordTrace]
  refine ⟨216884083374110777064714341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144589388916073851376476227 216884083374110777064714341)
  ·
    refine ⟨40665765632645770699633939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216884083374110777064714341 40665765632645770699633939)
    ·
      refine ⟨60998648448968656049450909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40665765632645770699633939 60998648448968656049450909)
      ·
        refine ⟨22874493168363246018544091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60998648448968656049450909 22874493168363246018544091)
        ·
          refine ⟨34311739752544869027816137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22874493168363246018544091 34311739752544869027816137)
          ·
            refine ⟨25733804814408651770862103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34311739752544869027816137 25733804814408651770862103)
            ·
              refine ⟨38600707221612977656293155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25733804814408651770862103 38600707221612977656293155)
              ·
                refine ⟨57901060832419466484439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38600707221612977656293155 57901060832419466484439733)
                ·
                  refine ⟨5428224453039324982916225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57901060832419466484439733 5428224453039324982916225)
                  ·
                    refine ⟨4071168339779493737187169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5428224453039324982916225 4071168339779493737187169)
                    ·
                      refine ⟨3053376254834620302890377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071168339779493737187169 3053376254834620302890377)
                      ·
                        rfl

theorem cell23_5946429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5946429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946429 prefixEnd_5946429 := by exact prefixLift 5946429
  have htrace : WordTrace (prefixWord ++ tailWord_5946429) baseStart_5946429 baseEnd_5946429 := by
    simpa [prefixWord, tailWord_5946429, baseEnd_5946429] using wordTrace_append hprefix tailTrace_5946429
  have hstable : (prefixWord ++ tailWord_5946429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946429).length < 2 ^ (prefixWord ++ tailWord_5946429).sum := by decide
  have hdescent : baseEnd_5946429 < baseStart_5946429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946432 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_5946432 : Nat := 118140960795 + 5946432 * 2 ^ 59
def prefixEnd_5946432 : Nat := 4983230072969 + 3 ^ 40 * 5946432 * 2
def baseEnd_5946432 : Nat := 3053377795276583791152863

theorem tailTrace_5946432 : CollatzResearch.WordTrace tailWord_5946432 prefixEnd_5946432 3053377795276583791152863 := by
  unfold tailWord_5946432
  simp only [CollatzResearch.WordTrace]
  refine ⟨108442096396549954288536775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144589461862066605718049033 108442096396549954288536775)
  ·
    refine ⟨162663144594824931432805163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108442096396549954288536775 162663144594824931432805163)
    ·
      refine ⟨243994716892237397149207745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162663144594824931432805163 243994716892237397149207745)
      ·
        refine ⟨182996037669178047861905809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243994716892237397149207745 182996037669178047861905809)
        ·
          refine ⟨137247028251883535896429357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182996037669178047861905809 137247028251883535896429357)
          ·
            refine ⟨51467635594456325961161009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137247028251883535896429357 51467635594456325961161009)
            ·
              refine ⟨38600726695842244470870757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51467635594456325961161009 38600726695842244470870757)
              ·
                refine ⟨7237636255470420838288267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38600726695842244470870757 7237636255470420838288267)
                ·
                  refine ⟨10856454383205631257432401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7237636255470420838288267 10856454383205631257432401)
                  ·
                    refine ⟨8142340787404223443074301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10856454383205631257432401 8142340787404223443074301)
                    ·
                      refine ⟨3053377795276583791152863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8142340787404223443074301 3053377795276583791152863)
                      ·
                        rfl

theorem cell23_5946432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_5946432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946432 prefixEnd_5946432 := by exact prefixLift 5946432
  have htrace : WordTrace (prefixWord ++ tailWord_5946432) baseStart_5946432 baseEnd_5946432 := by
    simpa [prefixWord, tailWord_5946432, baseEnd_5946432] using wordTrace_append hprefix tailTrace_5946432
  have hstable : (prefixWord ++ tailWord_5946432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946432).length < 2 ^ (prefixWord ++ tailWord_5946432).sum := by decide
  have hdescent : baseEnd_5946432 < baseStart_5946432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946433 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_5946433 : Nat := 118140960795 + 5946433 * 2 ^ 59
def prefixEnd_5946433 : Nat := 4983230072969 + 3 ^ 40 * 5946433 * 2
def baseEnd_5946433 : Nat := 3053378308757238287240359

theorem tailTrace_5946433 : CollatzResearch.WordTrace tailWord_5946433 prefixEnd_5946433 3053378308757238287240359 := by
  unfold tailWord_5946433
  simp only [CollatzResearch.WordTrace]
  refine ⟨216884229266096285747859953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144589486177397523831906635 216884229266096285747859953)
  ·
    refine ⟨162663171949572214310894965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216884229266096285747859953 162663171949572214310894965)
    ·
      refine ⟨15249672370272395091646403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162663171949572214310894965 15249672370272395091646403)
      ·
        refine ⟨22874508555408592637469605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15249672370272395091646403 22874508555408592637469605)
        ·
          refine ⟨4288970354139111119525551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22874508555408592637469605 4288970354139111119525551)
          ·
            refine ⟨6433455531208666679288327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288970354139111119525551 6433455531208666679288327)
            ·
              refine ⟨9650183296813000018932491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433455531208666679288327 9650183296813000018932491)
              ·
                refine ⟨14475274945219500028398737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9650183296813000018932491 14475274945219500028398737)
                ·
                  refine ⟨10856456208914625021299053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14475274945219500028398737 10856456208914625021299053)
                  ·
                    refine ⟨4071171078342984382987145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10856456208914625021299053 4071171078342984382987145)
                    ·
                      refine ⟨3053378308757238287240359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071171078342984382987145 3053378308757238287240359)
                      ·
                        rfl

theorem cell23_5946433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_5946433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946433 prefixEnd_5946433 := by exact prefixLift 5946433
  have htrace : WordTrace (prefixWord ++ tailWord_5946433) baseStart_5946433 baseEnd_5946433 := by
    simpa [prefixWord, tailWord_5946433, baseEnd_5946433] using wordTrace_append hprefix tailTrace_5946433
  have hstable : (prefixWord ++ tailWord_5946433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946433).length < 2 ^ (prefixWord ++ tailWord_5946433).sum := by decide
  have hdescent : baseEnd_5946433 < baseStart_5946433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946435 : List Nat := [1, 1, 1, 3, 1, 2, 7, 7]
def baseStart_5946435 : Nat := 118140960795 + 5946435 * 2 ^ 59
def prefixEnd_5946435 : Nat := 4983230072969 + 3 ^ 40 * 5946435 * 2
def baseEnd_5946435 : Nat := 113088123545131380719087

theorem tailTrace_5946435 : CollatzResearch.WordTrace tailWord_5946435 prefixEnd_5946435 113088123545131380719087 := by
  unfold tailWord_5946435
  simp only [CollatzResearch.WordTrace]
  refine ⟨216884302212089040089432759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144589534808059360059621839 216884302212089040089432759)
  ·
    refine ⟨325326453318133560134149139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216884302212089040089432759 325326453318133560134149139)
    ·
      refine ⟨487989679977200340201223709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325326453318133560134149139 487989679977200340201223709)
      ·
        refine ⟨182996129991450127575458891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487989679977200340201223709 182996129991450127575458891)
        ·
          refine ⟨274494194987175191363188337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182996129991450127575458891 274494194987175191363188337)
          ·
            refine ⟨205870646240381393522391253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274494194987175191363188337 205870646240381393522391253)
            ·
              refine ⟨4825093271258938910681045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205870646240381393522391253 4825093271258938910681045)
              ·
                refine ⟨113088123545131380719087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4825093271258938910681045 113088123545131380719087)
                ·
                  rfl

theorem cell23_5946435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 7].length) (baseStart_5946435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946435 prefixEnd_5946435 := by exact prefixLift 5946435
  have htrace : WordTrace (prefixWord ++ tailWord_5946435) baseStart_5946435 baseEnd_5946435 := by
    simpa [prefixWord, tailWord_5946435, baseEnd_5946435] using wordTrace_append hprefix tailTrace_5946435
  have hstable : (prefixWord ++ tailWord_5946435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946435).length < 2 ^ (prefixWord ++ tailWord_5946435).sum := by decide
  have hdescent : baseEnd_5946435 < baseStart_5946435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946449 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_5946449 : Nat := 118140960795 + 5946449 * 2 ^ 59
def prefixEnd_5946449 : Nat := 4983230072969 + 3 ^ 40 * 5946449 * 2
def baseEnd_5946449 : Nat := 3053386524447710224640285

theorem tailTrace_5946449 : CollatzResearch.WordTrace tailWord_5946449 prefixEnd_5946449 3053386524447710224640285 := by
  unfold tailWord_5946449
  simp only [CollatzResearch.WordTrace]
  refine ⟨216884812834038320480442401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144589875222692213653628267 216884812834038320480442401)
  ·
    refine ⟨162663609625528740360331801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216884812834038320480442401 162663609625528740360331801)
    ·
      refine ⟨121997707219146555270248851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162663609625528740360331801 121997707219146555270248851)
      ·
        refine ⟨182996560828719832905373277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121997707219146555270248851 182996560828719832905373277)
        ·
          refine ⟨68623710310769937339514979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182996560828719832905373277 68623710310769937339514979)
          ·
            refine ⟨102935565466154906009272469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68623710310769937339514979 102935565466154906009272469)
            ·
              refine ⟨4825104631226011219184647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102935565466154906009272469 4825104631226011219184647)
              ·
                refine ⟨7237656946839016828776971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825104631226011219184647 7237656946839016828776971)
                ·
                  refine ⟨10856485420258525243165457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7237656946839016828776971 10856485420258525243165457)
                  ·
                    refine ⟨8142364065193893932374093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10856485420258525243165457 8142364065193893932374093)
                    ·
                      refine ⟨3053386524447710224640285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8142364065193893932374093 3053386524447710224640285)
                      ·
                        rfl

theorem cell23_5946449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_5946449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946449 prefixEnd_5946449 := by exact prefixLift 5946449
  have htrace : WordTrace (prefixWord ++ tailWord_5946449) baseStart_5946449 baseEnd_5946449 := by
    simpa [prefixWord, tailWord_5946449, baseEnd_5946449] using wordTrace_append hprefix tailTrace_5946449
  have hstable : (prefixWord ++ tailWord_5946449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946449).length < 2 ^ (prefixWord ++ tailWord_5946449).sum := by decide
  have hdescent : baseEnd_5946449 < baseStart_5946449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946505 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_5946505 : Nat := 118140960795 + 5946505 * 2 ^ 59
def prefixEnd_5946505 : Nat := 4983230072969 + 3 ^ 40 * 5946505 * 2
def baseEnd_5946505 : Nat := 3053415279364362005540027

theorem tailTrace_5946505 : CollatzResearch.WordTrace tailWord_5946505 prefixEnd_5946505 3053415279364362005540027 := by
  unfold tailWord_5946505
  simp only [CollatzResearch.WordTrace]
  refine ⟨216886855321835442044480969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144591236881223628029653979 216886855321835442044480969)
  ·
    refine ⟨162665141491376581533360727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216886855321835442044480969 162665141491376581533360727)
    ·
      refine ⟨243997712237064872300041091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162665141491376581533360727 243997712237064872300041091)
      ·
        refine ⟨365996568355597308450061637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243997712237064872300041091 365996568355597308450061637)
        ·
          refine ⟨68624356566674495334386557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365996568355597308450061637 68624356566674495334386557)
          ·
            refine ⟨25734133712502935750394959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68624356566674495334386557 25734133712502935750394959)
            ·
              refine ⟨38601200568754403625592439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25734133712502935750394959 38601200568754403625592439)
              ·
                refine ⟨57901800853131605438388659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38601200568754403625592439 57901800853131605438388659)
                ·
                  refine ⟨86852701279697408157582989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57901800853131605438388659 86852701279697408157582989)
                  ·
                    refine ⟨32569762979886528059093621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86852701279697408157582989 32569762979886528059093621)
                    ·
                      refine ⟨3053415279364362005540027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32569762979886528059093621 3053415279364362005540027)
                      ·
                        rfl

theorem cell23_5946505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_5946505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946505 prefixEnd_5946505 := by exact prefixLift 5946505
  have htrace : WordTrace (prefixWord ++ tailWord_5946505) baseStart_5946505 baseEnd_5946505 := by
    simpa [prefixWord, tailWord_5946505, baseEnd_5946505] using wordTrace_append hprefix tailTrace_5946505
  have hstable : (prefixWord ++ tailWord_5946505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946505).length < 2 ^ (prefixWord ++ tailWord_5946505).sum := by decide
  have hdescent : baseEnd_5946505 < baseStart_5946505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946515 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_5946515 : Nat := 118140960795 + 5946515 * 2 ^ 59
def prefixEnd_5946515 : Nat := 4983230072969 + 3 ^ 40 * 5946515 * 2
def baseEnd_5946515 : Nat := 3053420414170906966414981

theorem tailTrace_5946515 : CollatzResearch.WordTrace tailWord_5946515 prefixEnd_5946515 3053420414170906966414981 := by
  unfold tailWord_5946515
  simp only [CollatzResearch.WordTrace]
  refine ⟨216887220051799213752344999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144591480034532809168229999 216887220051799213752344999)
  ·
    refine ⟨325330830077698820628517499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216887220051799213752344999 325330830077698820628517499)
    ·
      refine ⟨487996245116548230942776249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325330830077698820628517499 487996245116548230942776249)
      ·
        refine ⟨365997183837411173207082187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487996245116548230942776249 365997183837411173207082187)
        ·
          refine ⟨548995775756116759810623281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365997183837411173207082187 548995775756116759810623281)
          ·
            refine ⟨411746831817087569857967461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548995775756116759810623281 411746831817087569857967461)
            ·
              refine ⟨77202530965703919348368899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411746831817087569857967461 77202530965703919348368899)
              ·
                refine ⟨115803796448555879022553349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77202530965703919348368899 115803796448555879022553349)
                ·
                  refine ⟨21713211834104227316728753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115803796448555879022553349 21713211834104227316728753)
                  ·
                    refine ⟨16284908875578170487546565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21713211834104227316728753 16284908875578170487546565)
                    ·
                      refine ⟨3053420414170906966414981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16284908875578170487546565 3053420414170906966414981)
                      ·
                        rfl

theorem cell23_5946515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_5946515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946515 prefixEnd_5946515 := by exact prefixLift 5946515
  have htrace : WordTrace (prefixWord ++ tailWord_5946515) baseStart_5946515 baseEnd_5946515 := by
    simpa [prefixWord, tailWord_5946515, baseEnd_5946515] using wordTrace_append hprefix tailTrace_5946515
  have hstable : (prefixWord ++ tailWord_5946515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946515).length < 2 ^ (prefixWord ++ tailWord_5946515).sum := by decide
  have hdescent : baseEnd_5946515 < baseStart_5946515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946530 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5946530 : Nat := 118140960795 + 5946530 * 2 ^ 59
def prefixEnd_5946530 : Nat := 4983230072969 + 3 ^ 40 * 5946530 * 2
def baseEnd_5946530 : Nat := 3053428116380724407727413

theorem tailTrace_5946530 : CollatzResearch.WordTrace tailWord_5946530 prefixEnd_5946530 3053428116380724407727413 := by
  unfold tailWord_5946530
  simp only [CollatzResearch.WordTrace]
  refine ⟨54221941786686217828535261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144591844764496580876094029 54221941786686217828535261)
  ·
    refine ⟨20333228170007331685700723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54221941786686217828535261 20333228170007331685700723)
    ·
      refine ⟨30499842255010997528551085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20333228170007331685700723 30499842255010997528551085)
      ·
        refine ⟨11437440845629124073206657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30499842255010997528551085 11437440845629124073206657)
        ·
          refine ⟨8578080634221843054904993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11437440845629124073206657 8578080634221843054904993)
          ·
            refine ⟨6433560475666382291178745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578080634221843054904993 6433560475666382291178745)
            ·
              refine ⟨4825170356749786718384059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6433560475666382291178745 4825170356749786718384059)
              ·
                refine ⟨7237755535124680077576089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825170356749786718384059 7237755535124680077576089)
                ·
                  refine ⟨5428316651343510058182067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7237755535124680077576089 5428316651343510058182067)
                  ·
                    refine ⟨8142474977015265087273101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5428316651343510058182067 8142474977015265087273101)
                    ·
                      refine ⟨3053428116380724407727413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8142474977015265087273101 3053428116380724407727413)
                      ·
                        rfl

theorem cell23_5946530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5946530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946530 prefixEnd_5946530 := by exact prefixLift 5946530
  have htrace : WordTrace (prefixWord ++ tailWord_5946530) baseStart_5946530 baseEnd_5946530 := by
    simpa [prefixWord, tailWord_5946530, baseEnd_5946530] using wordTrace_append hprefix tailTrace_5946530
  have hstable : (prefixWord ++ tailWord_5946530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946530).length < 2 ^ (prefixWord ++ tailWord_5946530).sum := by decide
  have hdescent : baseEnd_5946530 < baseStart_5946530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946585 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_5946585 : Nat := 118140960795 + 5946585 * 2 ^ 59
def prefixEnd_5946585 : Nat := 4983230072969 + 3 ^ 40 * 5946585 * 2
def baseEnd_5946585 : Nat := 1017818785938907230846553

theorem tailTrace_5946585 : CollatzResearch.WordTrace tailWord_5946585 prefixEnd_5946585 1017818785938907230846553 := by
  unfold tailWord_5946585
  simp only [CollatzResearch.WordTrace]
  refine ⟨216889773161545615707393209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144593182107697077138262139 216889773161545615707393209)
  ·
    refine ⟨162667329871159211780544907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216889773161545615707393209 162667329871159211780544907)
    ·
      refine ⟨244000994806738817670817361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162667329871159211780544907 244000994806738817670817361)
      ·
        refine ⟨183000746105054113253113021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244000994806738817670817361 183000746105054113253113021)
        ·
          refine ⟨68625279789395292469917383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183000746105054113253113021 68625279789395292469917383)
          ·
            refine ⟨102937919684092938704876075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68625279789395292469917383 102937919684092938704876075)
            ·
              refine ⟨154406879526139408057314113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102937919684092938704876075 154406879526139408057314113)
              ·
                refine ⟨115805159644604556042985585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154406879526139408057314113 115805159644604556042985585)
                ·
                  refine ⟨86853869733453417032239189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115805159644604556042985585 86853869733453417032239189)
                  ·
                    refine ⟨1017818785938907230846553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86853869733453417032239189 1017818785938907230846553)
                    ·
                      rfl

theorem cell23_5946585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_5946585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946585 prefixEnd_5946585 := by exact prefixLift 5946585
  have htrace : WordTrace (prefixWord ++ tailWord_5946585) baseStart_5946585 baseEnd_5946585 := by
    simpa [prefixWord, tailWord_5946585, baseEnd_5946585] using wordTrace_append hprefix tailTrace_5946585
  have hstable : (prefixWord ++ tailWord_5946585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946585).length < 2 ^ (prefixWord ++ tailWord_5946585).sum := by decide
  have hdescent : baseEnd_5946585 < baseStart_5946585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946615 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 10]
def baseStart_5946615 : Nat := 118140960795 + 5946615 * 2 ^ 59
def prefixEnd_5946615 : Nat := 4983230072969 + 3 ^ 40 * 5946615 * 2
def baseEnd_5946615 : Nat := 339274640248484063907169

theorem tailTrace_5946615 : CollatzResearch.WordTrace tailWord_5946615 prefixEnd_5946615 339274640248484063907169 := by
  unfold tailWord_5946615
  simp only [CollatzResearch.WordTrace]
  refine ⟨216890867351436930830985299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144593911567624620553990199 216890867351436930830985299)
  ·
    refine ⟨325336301027155396246477949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216890867351436930830985299 325336301027155396246477949)
    ·
      refine ⟨122001112885183273592429231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325336301027155396246477949 122001112885183273592429231)
      ·
        refine ⟨183001669327774910388643847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122001112885183273592429231 183001669327774910388643847)
        ·
          refine ⟨274502503991662365582965771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183001669327774910388643847 274502503991662365582965771)
          ·
            refine ⟨411753755987493548374448657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274502503991662365582965771 411753755987493548374448657)
            ·
              refine ⟨308815316990620161280836493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411753755987493548374448657 308815316990620161280836493)
              ·
                refine ⟨115805743871482560480313685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308815316990620161280836493 115805743871482560480313685)
                ·
                  refine ⟨339274640248484063907169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115805743871482560480313685 339274640248484063907169)
                  ·
                    rfl

theorem cell23_5946615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 10].length) (baseStart_5946615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946615 prefixEnd_5946615 := by exact prefixLift 5946615
  have htrace : WordTrace (prefixWord ++ tailWord_5946615) baseStart_5946615 baseEnd_5946615 := by
    simpa [prefixWord, tailWord_5946615, baseEnd_5946615] using wordTrace_append hprefix tailTrace_5946615
  have hstable : (prefixWord ++ tailWord_5946615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946615).length < 2 ^ (prefixWord ++ tailWord_5946615).sum := by decide
  have hdescent : baseEnd_5946615 < baseStart_5946615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946636 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_5946636 : Nat := 118140960795 + 5946636 * 2 ^ 59
def prefixEnd_5946636 : Nat := 4983230072969 + 3 ^ 40 * 5946636 * 2
def baseEnd_5946636 : Nat := 1017827515110033664333975

theorem tailTrace_5946636 : CollatzResearch.WordTrace tailWord_5946636 prefixEnd_5946636 1017827515110033664333975 := by
  unfold tailWord_5946636
  simp only [CollatzResearch.WordTrace]
  refine ⟨108445816642180425708749881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144594422189573900944999841 108445816642180425708749881)
  ·
    refine ⟨81334362481635319281562411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108445816642180425708749881 81334362481635319281562411)
    ·
      refine ⟨122001543722452978922343617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81334362481635319281562411 122001543722452978922343617)
      ·
        refine ⟨91501157791839734191757713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122001543722452978922343617 91501157791839734191757713)
        ·
          refine ⟨68625868343879800643818285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91501157791839734191757713 68625868343879800643818285)
          ·
            refine ⟨25734700628954925241431857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68625868343879800643818285 25734700628954925241431857)
            ·
              refine ⟨19301025471716193931073893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25734700628954925241431857 19301025471716193931073893)
              ·
                refine ⟨3618942275946786362076355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19301025471716193931073893 3618942275946786362076355)
                ·
                  refine ⟨5428413413920179543114533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618942275946786362076355 5428413413920179543114533)
                  ·
                    refine ⟨1017827515110033664333975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5428413413920179543114533 1017827515110033664333975)
                    ·
                      rfl

theorem cell23_5946636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_5946636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946636 prefixEnd_5946636 := by exact prefixLift 5946636
  have htrace : WordTrace (prefixWord ++ tailWord_5946636) baseStart_5946636 baseEnd_5946636 := by
    simpa [prefixWord, tailWord_5946636, baseEnd_5946636] using wordTrace_append hprefix tailTrace_5946636
  have hstable : (prefixWord ++ tailWord_5946636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946636).length < 2 ^ (prefixWord ++ tailWord_5946636).sum := by decide
  have hdescent : baseEnd_5946636 < baseStart_5946636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946712 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_5946712 : Nat := 118140960795 + 5946712 * 2 ^ 59
def prefixEnd_5946712 : Nat := 4983230072969 + 3 ^ 40 * 5946712 * 2
def baseEnd_5946712 : Nat := 3053521569859842695651575

theorem tailTrace_5946712 : CollatzResearch.WordTrace tailWord_5946712 prefixEnd_5946712 3053521569859842695651575 := by
  unfold tailWord_5946712
  simp only [CollatzResearch.WordTrace]
  refine ⟨108447202616042758198633195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144596270154723677598177593 108447202616042758198633195)
  ·
    refine ⟨162670803924064137297949793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108447202616042758198633195 162670803924064137297949793)
    ·
      refine ⟨122003102943048102973462345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162670803924064137297949793 122003102943048102973462345)
      ·
        refine ⟨91502327207286077230096759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122003102943048102973462345 91502327207286077230096759)
        ·
          refine ⟨137253490810929115845145139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91502327207286077230096759 137253490810929115845145139)
          ·
            refine ⟨205880236216393673767717709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137253490810929115845145139 205880236216393673767717709)
            ·
              refine ⟨77205088581147627662894141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205880236216393673767717709 77205088581147627662894141)
              ·
                refine ⟨28951908217930360373585303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77205088581147627662894141 28951908217930360373585303)
                ·
                  refine ⟨43427862326895540560377955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28951908217930360373585303 43427862326895540560377955)
                  ·
                    refine ⟨65141793490343310840566933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43427862326895540560377955 65141793490343310840566933)
                    ·
                      refine ⟨3053521569859842695651575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65141793490343310840566933 3053521569859842695651575)
                      ·
                        rfl

theorem cell23_5946712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_5946712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946712 prefixEnd_5946712 := by exact prefixLift 5946712
  have htrace : WordTrace (prefixWord ++ tailWord_5946712) baseStart_5946712 baseEnd_5946712 := by
    simpa [prefixWord, tailWord_5946712, baseEnd_5946712] using wordTrace_append hprefix tailTrace_5946712
  have hstable : (prefixWord ++ tailWord_5946712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946712).length < 2 ^ (prefixWord ++ tailWord_5946712).sum := by decide
  have hdescent : baseEnd_5946712 < baseStart_5946712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946733 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_5946733 : Nat := 118140960795 + 5946733 * 2 ^ 59
def prefixEnd_5946733 : Nat := 4983230072969 + 3 ^ 40 * 5946733 * 2
def baseEnd_5946733 : Nat := 3053532352953587113488979

theorem tailTrace_5946733 : CollatzResearch.WordTrace tailWord_5946733 prefixEnd_5946733 3053532352953587113488979 := by
  unfold tailWord_5946733
  simp only [CollatzResearch.WordTrace]
  refine ⟨216895171165009436983780853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144596780776672957989187235 216895171165009436983780853)
  ·
    refine ⟨20333922296719634717229455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216895171165009436983780853 20333922296719634717229455)
    ·
      refine ⟨30500883445079452075844183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20333922296719634717229455 30500883445079452075844183)
      ·
        refine ⟨45751325167619178113766275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30500883445079452075844183 45751325167619178113766275)
        ·
          refine ⟨68626987751428767170649413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45751325167619178113766275 68626987751428767170649413)
          ·
            refine ⟨12867560203392893844496765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68626987751428767170649413 12867560203392893844496765)
            ·
              refine ⟨4825335076272335191686287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12867560203392893844496765 4825335076272335191686287)
              ·
                refine ⟨7238002614408502787529431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825335076272335191686287 7238002614408502787529431)
                ·
                  refine ⟨10857003921612754181294147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7238002614408502787529431 10857003921612754181294147)
                  ·
                    refine ⟨16285505882419131271941221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10857003921612754181294147 16285505882419131271941221)
                    ·
                      refine ⟨3053532352953587113488979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16285505882419131271941221 3053532352953587113488979)
                      ·
                        rfl

theorem cell23_5946733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_5946733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946733 prefixEnd_5946733 := by exact prefixLift 5946733
  have htrace : WordTrace (prefixWord ++ tailWord_5946733) baseStart_5946733 baseEnd_5946733 := by
    simpa [prefixWord, tailWord_5946733, baseEnd_5946733] using wordTrace_append hprefix tailTrace_5946733
  have hstable : (prefixWord ++ tailWord_5946733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946733).length < 2 ^ (prefixWord ++ tailWord_5946733).sum := by decide
  have hdescent : baseEnd_5946733 < baseStart_5946733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946749 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_5946749 : Nat := 118140960795 + 5946749 * 2 ^ 59
def prefixEnd_5946749 : Nat := 4983230072969 + 3 ^ 40 * 5946749 * 2
def baseEnd_5946749 : Nat := 3053540568644059050888905

theorem tailTrace_5946749 : CollatzResearch.WordTrace tailWord_5946749 prefixEnd_5946749 3053540568644059050888905 := by
  unfold tailWord_5946749
  simp only [CollatzResearch.WordTrace]
  refine ⟨216895754732951471716363301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144597169821967647810908867 216895754732951471716363301)
  ·
    refine ⟨40667954012428400946818119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216895754732951471716363301 40667954012428400946818119)
    ·
      refine ⟨61001931018642601420227179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40667954012428400946818119 61001931018642601420227179)
      ·
        refine ⟨91502896527963902130340769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61001931018642601420227179 91502896527963902130340769)
        ·
          refine ⟨68627172395972926597755577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91502896527963902130340769 68627172395972926597755577)
          ·
            refine ⟨51470379296979694948316683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68627172395972926597755577 51470379296979694948316683)
            ·
              refine ⟨77205568945469542422475025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51470379296979694948316683 77205568945469542422475025)
              ·
                refine ⟨57904176709102156816856269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77205568945469542422475025 57904176709102156816856269)
                ·
                  refine ⟨21714066265913308806321101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57904176709102156816856269 21714066265913308806321101)
                  ·
                    refine ⟨8142774849717490802370413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21714066265913308806321101 8142774849717490802370413)
                    ·
                      refine ⟨3053540568644059050888905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8142774849717490802370413 3053540568644059050888905)
                      ·
                        rfl

theorem cell23_5946749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_5946749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946749 prefixEnd_5946749 := by exact prefixLift 5946749
  have htrace : WordTrace (prefixWord ++ tailWord_5946749) baseStart_5946749 baseEnd_5946749 := by
    simpa [prefixWord, tailWord_5946749, baseEnd_5946749] using wordTrace_append hprefix tailTrace_5946749
  have hstable : (prefixWord ++ tailWord_5946749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946749).length < 2 ^ (prefixWord ++ tailWord_5946749).sum := by decide
  have hdescent : baseEnd_5946749 < baseStart_5946749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946819 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_5946819 : Nat := 118140960795 + 5946819 * 2 ^ 59
def prefixEnd_5946819 : Nat := 4983230072969 + 3 ^ 40 * 5946819 * 2
def baseEnd_5946819 : Nat := 3053576512289873777013583

theorem tailTrace_5946819 : CollatzResearch.WordTrace tailWord_5946819 prefixEnd_5946819 3053576512289873777013583 := by
  unfold tailWord_5946819
  simp only [CollatzResearch.WordTrace]
  refine ⟨216898307842697873671411511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144598871895131915780941007 216898307842697873671411511)
  ·
    refine ⟨325347461764046810507117267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216898307842697873671411511 325347461764046810507117267)
    ·
      refine ⟨488021192646070215760675901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325347461764046810507117267 488021192646070215760675901)
      ·
        refine ⟨183007947242276330910253463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488021192646070215760675901 183007947242276330910253463)
        ·
          refine ⟨274511920863414496365380195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183007947242276330910253463 274511920863414496365380195)
          ·
            refine ⟨411767881295121744548070293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274511920863414496365380195 411767881295121744548070293)
            ·
              refine ⟨19301619435708831775690795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411767881295121744548070293 19301619435708831775690795)
              ·
                refine ⟨28952429153563247663536193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19301619435708831775690795 28952429153563247663536193)
                ·
                  refine ⟨21714321865172435747652145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28952429153563247663536193 21714321865172435747652145)
                  ·
                    refine ⟨16285741398879326810739109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21714321865172435747652145 16285741398879326810739109)
                    ·
                      refine ⟨3053576512289873777013583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16285741398879326810739109 3053576512289873777013583)
                      ·
                        rfl

theorem cell23_5946819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_5946819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946819 prefixEnd_5946819 := by exact prefixLift 5946819
  have htrace : WordTrace (prefixWord ++ tailWord_5946819) baseStart_5946819 baseEnd_5946819 := by
    simpa [prefixWord, tailWord_5946819, baseEnd_5946819] using wordTrace_append hprefix tailTrace_5946819
  have hstable : (prefixWord ++ tailWord_5946819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946819).length < 2 ^ (prefixWord ++ tailWord_5946819).sum := by decide
  have hdescent : baseEnd_5946819 < baseStart_5946819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946839 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_5946839 : Nat := 118140960795 + 5946839 * 2 ^ 59
def prefixEnd_5946839 : Nat := 4983230072969 + 3 ^ 40 * 5946839 * 2
def baseEnd_5946839 : Nat := 3053586781902963698763491

theorem tailTrace_5946839 : CollatzResearch.WordTrace tailWord_5946839 prefixEnd_5946839 3053586781902963698763491 := by
  unfold tailWord_5946839
  simp only [CollatzResearch.WordTrace]
  refine ⟨216899037302625417087139571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144599358201750278058093047 216899037302625417087139571)
  ·
    refine ⟨325348555953938125630709357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216899037302625417087139571 325348555953938125630709357)
    ·
      refine ⟨122005708482726797111516009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325348555953938125630709357 122005708482726797111516009)
      ·
        refine ⟨91504281362045097833637007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122005708482726797111516009 91504281362045097833637007)
        ·
          refine ⟨137256422043067646750455511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91504281362045097833637007 137256422043067646750455511)
          ·
            refine ⟨205884633064601470125683267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137256422043067646750455511 205884633064601470125683267)
            ·
              refine ⟨308826949596902205188524901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205884633064601470125683267 308826949596902205188524901)
              ·
                refine ⟨57905053049419163472848419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308826949596902205188524901 57905053049419163472848419)
                ·
                  refine ⟨86857579574128745209272629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57905053049419163472848419 86857579574128745209272629)
                  ·
                    refine ⟨8142898085074569863369309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86857579574128745209272629 8142898085074569863369309)
                    ·
                      refine ⟨3053586781902963698763491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8142898085074569863369309 3053586781902963698763491)
                      ·
                        rfl

theorem cell23_5946839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_5946839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946839 prefixEnd_5946839 := by exact prefixLift 5946839
  have htrace : WordTrace (prefixWord ++ tailWord_5946839) baseStart_5946839 baseEnd_5946839 := by
    simpa [prefixWord, tailWord_5946839, baseEnd_5946839] using wordTrace_append hprefix tailTrace_5946839
  have hstable : (prefixWord ++ tailWord_5946839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946839).length < 2 ^ (prefixWord ++ tailWord_5946839).sum := by decide
  have hdescent : baseEnd_5946839 < baseStart_5946839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946879 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_5946879 : Nat := 118140960795 + 5946879 * 2 ^ 59
def prefixEnd_5946879 : Nat := 4983230072969 + 3 ^ 40 * 5946879 * 2
def baseEnd_5946879 : Nat := 3053607321129143542263307

theorem tailTrace_5946879 : CollatzResearch.WordTrace tailWord_5946879 prefixEnd_5946879 3053607321129143542263307 := by
  unfold tailWord_5946879
  simp only [CollatzResearch.WordTrace]
  refine ⟨216900496222480503918595691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144600330814987002612397127 216900496222480503918595691)
  ·
    refine ⟨325350744333720755877893537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216900496222480503918595691 325350744333720755877893537)
    ·
      refine ⟨244013058250290566908420153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325350744333720755877893537 244013058250290566908420153)
      ·
        refine ⟨183009793687717925181315115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244013058250290566908420153 183009793687717925181315115)
        ·
          refine ⟨274514690531576887771972673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183009793687717925181315115 274514690531576887771972673)
          ·
            refine ⟨205886017898682665828979505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274514690531576887771972673 205886017898682665828979505)
            ·
              refine ⟨154414513424011999371734629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205886017898682665828979505 154414513424011999371734629)
              ·
                refine ⟨28952721267002249882200243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154414513424011999371734629 28952721267002249882200243)
                ·
                  refine ⟨43429081900503374823300365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28952721267002249882200243 43429081900503374823300365)
                  ·
                    refine ⟨16285905712688765558737637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43429081900503374823300365 16285905712688765558737637)
                    ·
                      refine ⟨3053607321129143542263307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16285905712688765558737637 3053607321129143542263307)
                      ·
                        rfl

theorem cell23_5946879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_5946879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946879 prefixEnd_5946879 := by exact prefixLift 5946879
  have htrace : WordTrace (prefixWord ++ tailWord_5946879) baseStart_5946879 baseEnd_5946879 := by
    simpa [prefixWord, tailWord_5946879, baseEnd_5946879] using wordTrace_append hprefix tailTrace_5946879
  have hstable : (prefixWord ++ tailWord_5946879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946879).length < 2 ^ (prefixWord ++ tailWord_5946879).sum := by decide
  have hdescent : baseEnd_5946879 < baseStart_5946879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946936 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 6]
def baseStart_5946936 : Nat := 118140960795 + 5946936 * 2 ^ 59
def prefixEnd_5946936 : Nat := 4983230072969 + 3 ^ 40 * 5946936 * 2
def baseEnd_5946936 : Nat := 339292954391827757694505

theorem tailTrace_5946936 : CollatzResearch.WordTrace tailWord_5946936 prefixEnd_5946936 339292954391827757694505 := by
  unfold tailWord_5946936
  simp only [CollatzResearch.WordTrace]
  refine ⟨108451287591637001326710331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144601716788849335102280441 108451287591637001326710331)
  ·
    refine ⟨162676931387455501990065497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108451287591637001326710331 162676931387455501990065497)
    ·
      refine ⟨122007698540591626492549123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162676931387455501990065497 122007698540591626492549123)
      ·
        refine ⟨183011547810887439738823685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122007698540591626492549123 183011547810887439738823685)
        ·
          refine ⟨34314665214541394951029441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183011547810887439738823685 34314665214541394951029441)
          ·
            refine ⟨25735998910906046213272081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34314665214541394951029441 25735998910906046213272081)
            ·
              refine ⟨19301999183179534659954061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25735998910906046213272081 19301999183179534659954061)
              ·
                refine ⟨7238249693692325497482773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19301999183179534659954061 7238249693692325497482773)
                ·
                  refine ⟨339292954391827757694505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7238249693692325497482773 339292954391827757694505)
                  ·
                    rfl

theorem cell23_5946936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_5946936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946936 prefixEnd_5946936 := by exact prefixLift 5946936
  have htrace : WordTrace (prefixWord ++ tailWord_5946936) baseStart_5946936 baseEnd_5946936 := by
    simpa [prefixWord, tailWord_5946936, baseEnd_5946936] using wordTrace_append hprefix tailTrace_5946936
  have hstable : (prefixWord ++ tailWord_5946936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946936).length < 2 ^ (prefixWord ++ tailWord_5946936).sum := by decide
  have hdescent : baseEnd_5946936 < baseStart_5946936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946959 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_5946959 : Nat := 118140960795 + 5946959 * 2 ^ 59
def prefixEnd_5946959 : Nat := 4983230072969 + 3 ^ 40 * 5946959 * 2
def baseEnd_5946959 : Nat := 3053648399581503229262939

theorem tailTrace_5946959 : CollatzResearch.WordTrace tailWord_5946959 prefixEnd_5946959 3053648399581503229262939 := by
  unfold tailWord_5946959
  simp only [CollatzResearch.WordTrace]
  refine ⟨216903414062190677581507931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144602276041460451721005287 216903414062190677581507931)
  ·
    refine ⟨325355121093286016372261897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216903414062190677581507931 325355121093286016372261897)
    ·
      refine ⟨244016340819964512279196423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325355121093286016372261897 244016340819964512279196423)
      ·
        refine ⟨366024511229946768418794635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244016340819964512279196423 366024511229946768418794635)
        ·
          refine ⟨549036766844920152628191953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366024511229946768418794635 549036766844920152628191953)
          ·
            refine ⟨411777575133690114471143965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549036766844920152628191953 411777575133690114471143965)
            ·
              refine ⟨154416590675133792926678987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411777575133690114471143965 154416590675133792926678987)
              ·
                refine ⟨231624886012700689390018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154416590675133792926678987 231624886012700689390018481)
                ·
                  refine ⟨173718664509525517042513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231624886012700689390018481 173718664509525517042513861)
                  ·
                    refine ⟨32572249595536034445471349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173718664509525517042513861 32572249595536034445471349)
                    ·
                      refine ⟨3053648399581503229262939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32572249595536034445471349 3053648399581503229262939)
                      ·
                        rfl

theorem cell23_5946959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_5946959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946959 prefixEnd_5946959 := by exact prefixLift 5946959
  have htrace : WordTrace (prefixWord ++ tailWord_5946959) baseStart_5946959 baseEnd_5946959 := by
    simpa [prefixWord, tailWord_5946959, baseEnd_5946959] using wordTrace_append hprefix tailTrace_5946959
  have hstable : (prefixWord ++ tailWord_5946959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946959).length < 2 ^ (prefixWord ++ tailWord_5946959).sum := by decide
  have hdescent : baseEnd_5946959 < baseStart_5946959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946980 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_5946980 : Nat := 118140960795 + 5946980 * 2 ^ 59
def prefixEnd_5946980 : Nat := 4983230072969 + 3 ^ 40 * 5946980 * 2
def baseEnd_5946980 : Nat := 3053659182675247647100343

theorem tailTrace_5946980 : CollatzResearch.WordTrace tailWord_5946980 prefixEnd_5946980 3053659182675247647100343 := by
  unfold tailWord_5946980
  simp only [CollatzResearch.WordTrace]
  refine ⟨108452089997557299084011197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144602786663409732112014929 108452089997557299084011197)
  ·
    refine ⟨40669533749083987156504199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108452089997557299084011197 40669533749083987156504199)
    ·
      refine ⟨61004300623625980734756299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40669533749083987156504199 61004300623625980734756299)
      ·
        refine ⟨91506450935438971102134449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61004300623625980734756299 91506450935438971102134449)
        ·
          refine ⟨68629838201579228326600837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91506450935438971102134449 68629838201579228326600837)
          ·
            refine ⟨12868094662796105311237657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68629838201579228326600837 12868094662796105311237657)
            ·
              refine ⟨9651070997097078983428243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12868094662796105311237657 9651070997097078983428243)
              ·
                refine ⟨14476606495645618475142365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9651070997097078983428243 14476606495645618475142365)
                ·
                  refine ⟨5428727435867106928178387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14476606495645618475142365 5428727435867106928178387)
                  ·
                    refine ⟨8143091153800660392267581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5428727435867106928178387 8143091153800660392267581)
                    ·
                      refine ⟨3053659182675247647100343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8143091153800660392267581 3053659182675247647100343)
                      ·
                        rfl

theorem cell23_5946980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_5946980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946980 prefixEnd_5946980 := by exact prefixLift 5946980
  have htrace : WordTrace (prefixWord ++ tailWord_5946980) baseStart_5946980 baseEnd_5946980 := by
    simpa [prefixWord, tailWord_5946980, baseEnd_5946980] using wordTrace_append hprefix tailTrace_5946980
  have hstable : (prefixWord ++ tailWord_5946980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946980).length < 2 ^ (prefixWord ++ tailWord_5946980).sum := by decide
  have hdescent : baseEnd_5946980 < baseStart_5946980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947003 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 4]
def baseStart_5947003 : Nat := 118140960795 + 5947003 * 2 ^ 59
def prefixEnd_5947003 : Nat := 4983230072969 + 3 ^ 40 * 5947003 * 2
def baseEnd_5947003 : Nat := 3053670992730301057112737

theorem tailTrace_5947003 : CollatzResearch.WordTrace tailWord_5947003 prefixEnd_5947003 3053670992730301057112737 := by
  unfold tailWord_5947003
  simp only [CollatzResearch.WordTrace]
  refine ⟨216905018874031273096109663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144603345916020848730739775 216905018874031273096109663)
  ·
    refine ⟨325357528311046909644164495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216905018874031273096109663 325357528311046909644164495)
    ·
      refine ⟨488036292466570364466246743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325357528311046909644164495 488036292466570364466246743)
      ·
        refine ⟨732054438699855546699370115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488036292466570364466246743 732054438699855546699370115)
        ·
          refine ⟨1098081658049783320049055173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732054438699855546699370115 1098081658049783320049055173)
          ·
            refine ⟨205890310884334372509197845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1098081658049783320049055173 205890310884334372509197845)
            ·
              refine ⟨9651108322703173711368649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205890310884334372509197845 9651108322703173711368649)
              ·
                refine ⟨7238331242027380283526487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9651108322703173711368649 7238331242027380283526487)
                ·
                  refine ⟨10857496863041070425289731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7238331242027380283526487 10857496863041070425289731)
                  ·
                    refine ⟨16286245294561605637934597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10857496863041070425289731 16286245294561605637934597)
                    ·
                      refine ⟨3053670992730301057112737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16286245294561605637934597 3053670992730301057112737)
                      ·
                        rfl

theorem cell23_5947003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 4].length) (baseStart_5947003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947003 prefixEnd_5947003 := by exact prefixLift 5947003
  have htrace : WordTrace (prefixWord ++ tailWord_5947003) baseStart_5947003 baseEnd_5947003 := by
    simpa [prefixWord, tailWord_5947003, baseEnd_5947003] using wordTrace_append hprefix tailTrace_5947003
  have hstable : (prefixWord ++ tailWord_5947003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947003).length < 2 ^ (prefixWord ++ tailWord_5947003).sum := by decide
  have hdescent : baseEnd_5947003 < baseStart_5947003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947054 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5947054 : Nat := 118140960795 + 5947054 * 2 ^ 59
def prefixEnd_5947054 : Nat := 4983230072969 + 3 ^ 40 * 5947054 * 2
def baseEnd_5947054 : Nat := 3053697180243680357575003

theorem tailTrace_5947054 : CollatzResearch.WordTrace tailWord_5947054 prefixEnd_5947054 3053697180243680357575003 := by
  unfold tailWord_5947054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113359874605813600777027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144604585997897672537477477 27113359874605813600777027)
  ·
    refine ⟨40670039811908720401165541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27113359874605813600777027 40670039811908720401165541)
    ·
      refine ⟨7625632464732885075218539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40670039811908720401165541 7625632464732885075218539)
      ·
        refine ⟨11438448697099327612827809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7625632464732885075218539 11438448697099327612827809)
        ·
          refine ⟨8578836522824495709620857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11438448697099327612827809 8578836522824495709620857)
          ·
            refine ⟨6434127392118371782215643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578836522824495709620857 6434127392118371782215643)
            ·
              refine ⟨9651191088177557673323465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434127392118371782215643 9651191088177557673323465)
              ·
                refine ⟨7238393316133168254992599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9651191088177557673323465 7238393316133168254992599)
                ·
                  refine ⟨10857589974199752382488899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7238393316133168254992599 10857589974199752382488899)
                  ·
                    refine ⟨16286384961299628573733349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10857589974199752382488899 16286384961299628573733349)
                    ·
                      refine ⟨3053697180243680357575003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16286384961299628573733349 3053697180243680357575003)
                      ·
                        rfl

theorem cell23_5947054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5947054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947054 prefixEnd_5947054 := by exact prefixLift 5947054
  have htrace : WordTrace (prefixWord ++ tailWord_5947054) baseStart_5947054 baseEnd_5947054 := by
    simpa [prefixWord, tailWord_5947054, baseEnd_5947054] using wordTrace_append hprefix tailTrace_5947054
  have hstable : (prefixWord ++ tailWord_5947054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947054).length < 2 ^ (prefixWord ++ tailWord_5947054).sum := by decide
  have hdescent : baseEnd_5947054 < baseStart_5947054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947070 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_5947070 : Nat := 118140960795 + 5947070 * 2 ^ 59
def prefixEnd_5947070 : Nat := 4983230072969 + 3 ^ 40 * 5947070 * 2
def baseEnd_5947070 : Nat := 3053705395934152294974929

theorem tailTrace_5947070 : CollatzResearch.WordTrace tailWord_5947070 prefixEnd_5947070 3053705395934152294974929 := by
  unfold tailWord_5947070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113432820598567942349833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144604975043192362359199109 27113432820598567942349833)
  ·
    refine ⟨20335074615448925956762375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27113432820598567942349833 20335074615448925956762375)
    ·
      refine ⟨30502611923173388935143563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20335074615448925956762375 30502611923173388935143563)
      ·
        refine ⟨45753917884760083402715345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30502611923173388935143563 45753917884760083402715345)
        ·
          refine ⟨34315438413570062552036509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45753917884760083402715345 34315438413570062552036509)
          ·
            refine ⟨12868289405088773457013691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34315438413570062552036509 12868289405088773457013691)
            ·
              refine ⟨19302434107633160185520537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12868289405088773457013691 19302434107633160185520537)
              ·
                refine ⟨14476825580724870139140403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19302434107633160185520537 14476825580724870139140403)
                ·
                  refine ⟨21715238371087305208710605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14476825580724870139140403 21715238371087305208710605)
                  ·
                    refine ⟨8143214389157739453266477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21715238371087305208710605 8143214389157739453266477)
                    ·
                      refine ⟨3053705395934152294974929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8143214389157739453266477 3053705395934152294974929)
                      ·
                        rfl

theorem cell23_5947070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_5947070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947070 prefixEnd_5947070 := by exact prefixLift 5947070
  have htrace : WordTrace (prefixWord ++ tailWord_5947070) baseStart_5947070 baseEnd_5947070 := by
    simpa [prefixWord, tailWord_5947070, baseEnd_5947070] using wordTrace_append hprefix tailTrace_5947070
  have hstable : (prefixWord ++ tailWord_5947070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947070).length < 2 ^ (prefixWord ++ tailWord_5947070).sum := by decide
  have hdescent : baseEnd_5947070 < baseStart_5947070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947094 : List Nat := [5, 2, 1, 3, 2, 1, 1, 8]
def baseStart_5947094 : Nat := 118140960795 + 5947094 * 2 ^ 59
def prefixEnd_5947094 : Nat := 4983230072969 + 3 ^ 40 * 5947094 * 2
def baseEnd_5947094 : Nat := 113100656276661488928697

theorem tailTrace_5947094 : CollatzResearch.WordTrace tailWord_5947094 prefixEnd_5947094 113100656276661488928697 := by
  unfold tailWord_5947094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556771119793849727354521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144605558611134397091781557 13556771119793849727354521)
  ·
    refine ⟨10167578339845387295515891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13556771119793849727354521 10167578339845387295515891)
    ·
      refine ⟨15251367509768080943273837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10167578339845387295515891 15251367509768080943273837)
      ·
        refine ⟨5719262816163030353727689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15251367509768080943273837 5719262816163030353727689)
        ·
          refine ⟨4289447112122272765295767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5719262816163030353727689 4289447112122272765295767)
          ·
            refine ⟨6434170668183409147943651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289447112122272765295767 6434170668183409147943651)
            ·
              refine ⟨9651256002275113721915477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434170668183409147943651 9651256002275113721915477)
              ·
                refine ⟨113100656276661488928697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9651256002275113721915477 113100656276661488928697)
                ·
                  rfl

theorem cell23_5947094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_5947094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947094 prefixEnd_5947094 := by exact prefixLift 5947094
  have htrace : WordTrace (prefixWord ++ tailWord_5947094) baseStart_5947094 baseEnd_5947094 := by
    simpa [prefixWord, tailWord_5947094, baseEnd_5947094] using wordTrace_append hprefix tailTrace_5947094
  have hstable : (prefixWord ++ tailWord_5947094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947094).length < 2 ^ (prefixWord ++ tailWord_5947094).sum := by decide
  have hdescent : baseEnd_5947094 < baseStart_5947094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947116 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 9]
def baseStart_5947116 : Nat := 118140960795 + 5947116 * 2 ^ 59
def prefixEnd_5947116 : Nat := 4983230072969 + 3 ^ 40 * 5947116 * 2
def baseEnd_5947116 : Nat := 339303224004917679444413

theorem tailTrace_5947116 : CollatzResearch.WordTrace tailWord_5947116 prefixEnd_5947116 339303224004917679444413 := by
  unfold tailWord_5947116
  simp only [CollatzResearch.WordTrace]
  refine ⟨108454570161310946697486601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144606093548414595596648801 108454570161310946697486601)
  ·
    refine ⟨81340927620983210023114951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108454570161310946697486601 81340927620983210023114951)
    ·
      refine ⟨122011391431474815034672427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81340927620983210023114951 122011391431474815034672427)
      ·
        refine ⟨183017087147212222552008641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122011391431474815034672427 183017087147212222552008641)
        ·
          refine ⟨137262815360409166914006481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183017087147212222552008641 137262815360409166914006481)
          ·
            refine ⟨102947111520306875185504861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137262815360409166914006481 102947111520306875185504861)
            ·
              refine ⟨38605166820115078194564323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102947111520306875185504861 38605166820115078194564323)
              ·
                refine ⟨57907750230172617291846485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38605166820115078194564323 57907750230172617291846485)
                ·
                  refine ⟨339303224004917679444413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57907750230172617291846485 339303224004917679444413)
                  ·
                    rfl

theorem cell23_5947116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_5947116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947116 prefixEnd_5947116 := by exact prefixLift 5947116
  have htrace : WordTrace (prefixWord ++ tailWord_5947116) baseStart_5947116 baseEnd_5947116 := by
    simpa [prefixWord, tailWord_5947116, baseEnd_5947116] using wordTrace_append hprefix tailTrace_5947116
  have hstable : (prefixWord ++ tailWord_5947116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947116).length < 2 ^ (prefixWord ++ tailWord_5947116).sum := by decide
  have hdescent : baseEnd_5947116 < baseStart_5947116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947150 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_5947150 : Nat := 118140960795 + 5947150 * 2 ^ 59
def prefixEnd_5947150 : Nat := 4983230072969 + 3 ^ 40 * 5947150 * 2
def baseEnd_5947150 : Nat := 339305163820723553552729

theorem tailTrace_5947150 : CollatzResearch.WordTrace tailWord_5947150 prefixEnd_5947150 339305163820723553552729 := by
  unfold tailWord_5947150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113797550562339650213863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144606920269665811467807269 27113797550562339650213863)
  ·
    refine ⟨40670696325843509475320795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27113797550562339650213863 40670696325843509475320795)
    ·
      refine ⟨61006044488765264212981193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40670696325843509475320795 61006044488765264212981193)
      ·
        refine ⟨45754533366573948159735895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61006044488765264212981193 45754533366573948159735895)
        ·
          refine ⟨68631800049860922239603843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45754533366573948159735895 68631800049860922239603843)
          ·
            refine ⟨102947700074791383359405765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68631800049860922239603843 102947700074791383359405765)
            ·
              refine ⟨19302693764023384379888581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102947700074791383359405765 19302693764023384379888581)
              ·
                refine ⟨3619255080754384571229109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19302693764023384379888581 3619255080754384571229109)
                ·
                  refine ⟨339305163820723553552729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3619255080754384571229109 339305163820723553552729)
                  ·
                    rfl

theorem cell23_5947150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_5947150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947150 prefixEnd_5947150 := by exact prefixLift 5947150
  have htrace : WordTrace (prefixWord ++ tailWord_5947150) baseStart_5947150 baseEnd_5947150 := by
    simpa [prefixWord, tailWord_5947150, baseEnd_5947150] using wordTrace_append hprefix tailTrace_5947150
  have hstable : (prefixWord ++ tailWord_5947150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947150).length < 2 ^ (prefixWord ++ tailWord_5947150).sum := by decide
  have hdescent : baseEnd_5947150 < baseStart_5947150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947260 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_5947260 : Nat := 118140960795 + 5947260 * 2 ^ 59
def prefixEnd_5947260 : Nat := 4983230072969 + 3 ^ 40 * 5947260 * 2
def baseEnd_5947260 : Nat := 3053802957258506551599055

theorem tailTrace_5947260 : CollatzResearch.WordTrace tailWord_5947260 prefixEnd_5947260 3053802957258506551599055 := by
  unfold tailWord_5947260
  simp only [CollatzResearch.WordTrace]
  refine ⟨108457196217050102994107617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144609594956066803992143489 108457196217050102994107617)
  ·
    refine ⟨81342897162787577245580713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108457196217050102994107617 81342897162787577245580713)
    ·
      refine ⟨61007172872090682934185535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81342897162787577245580713 61007172872090682934185535)
      ·
        refine ⟨91510759308136024401278303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61007172872090682934185535 91510759308136024401278303)
        ·
          refine ⟨137266138962204036601917455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91510759308136024401278303 137266138962204036601917455)
          ·
            refine ⟨205899208443306054902876183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137266138962204036601917455 205899208443306054902876183)
            ·
              refine ⟨308848812664959082354314275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205899208443306054902876183 308848812664959082354314275)
              ·
                refine ⟨463273218997438623531471413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308848812664959082354314275 463273218997438623531471413)
                ·
                  refine ⟨43431864281009870956075445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 463273218997438623531471413 43431864281009870956075445)
                  ·
                    refine ⟨4071737276344675402132073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43431864281009870956075445 4071737276344675402132073)
                    ·
                      refine ⟨3053802957258506551599055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071737276344675402132073 3053802957258506551599055)
                      ·
                        rfl

theorem cell23_5947260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_5947260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947260 prefixEnd_5947260 := by exact prefixLift 5947260
  have htrace : WordTrace (prefixWord ++ tailWord_5947260) baseStart_5947260 baseEnd_5947260 := by
    simpa [prefixWord, tailWord_5947260, baseEnd_5947260] using wordTrace_append hprefix tailTrace_5947260
  have hstable : (prefixWord ++ tailWord_5947260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947260).length < 2 ^ (prefixWord ++ tailWord_5947260).sum := by decide
  have hdescent : baseEnd_5947260 < baseStart_5947260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947284 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5947284 : Nat := 118140960795 + 5947284 * 2 ^ 59
def prefixEnd_5947284 : Nat := 4983230072969 + 3 ^ 40 * 5947284 * 2
def baseEnd_5947284 : Nat := 3053815280794214457698945

theorem tailTrace_5947284 : CollatzResearch.WordTrace tailWord_5947284 prefixEnd_5947284 3053815280794214457698945 := by
  unfold tailWord_5947284
  simp only [CollatzResearch.WordTrace]
  refine ⟨108457633893006629043544453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144610178524008838724725937 108457633893006629043544453)
  ·
    refine ⟨20335806354938742945664585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108457633893006629043544453 20335806354938742945664585)
    ·
      refine ⟨15251854766204057209248439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20335806354938742945664585 15251854766204057209248439)
      ·
        refine ⟨22877782149306085813872659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15251854766204057209248439 22877782149306085813872659)
        ·
          refine ⟨34316673223959128720808989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22877782149306085813872659 34316673223959128720808989)
          ·
            refine ⟨12868752458984673270303371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34316673223959128720808989 12868752458984673270303371)
            ·
              refine ⟨19303128688477009905455057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12868752458984673270303371 19303128688477009905455057)
              ·
                refine ⟨14477346516357757429091293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19303128688477009905455057 14477346516357757429091293)
                ·
                  refine ⟨5429004943634159035909235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14477346516357757429091293 5429004943634159035909235)
                  ·
                    refine ⟨8143507415451238553863853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429004943634159035909235 8143507415451238553863853)
                    ·
                      refine ⟨3053815280794214457698945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8143507415451238553863853 3053815280794214457698945)
                      ·
                        rfl

theorem cell23_5947284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5947284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947284 prefixEnd_5947284 := by exact prefixLift 5947284
  have htrace : WordTrace (prefixWord ++ tailWord_5947284) baseStart_5947284 baseEnd_5947284 := by
    simpa [prefixWord, tailWord_5947284, baseEnd_5947284] using wordTrace_append hprefix tailTrace_5947284
  have hstable : (prefixWord ++ tailWord_5947284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947284).length < 2 ^ (prefixWord ++ tailWord_5947284).sum := by decide
  have hdescent : baseEnd_5947284 < baseStart_5947284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947300 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_5947300 : Nat := 118140960795 + 5947300 * 2 ^ 59
def prefixEnd_5947300 : Nat := 4983230072969 + 3 ^ 40 * 5947300 * 2
def baseEnd_5947300 : Nat := 1017941165494895465032957

theorem tailTrace_5947300 : CollatzResearch.WordTrace tailWord_5947300 prefixEnd_5947300 1017941165494895465032957 := by
  unfold tailWord_5947300
  simp only [CollatzResearch.WordTrace]
  refine ⟨108457925676977646409835677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144610567569303528546447569 108457925676977646409835677)
  ·
    refine ⟨40671722128866617403688379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108457925676977646409835677 40671722128866617403688379)
    ·
      refine ⟨61007583193299926105532569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40671722128866617403688379 61007583193299926105532569)
      ·
        refine ⟨45755687394974944579149427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61007583193299926105532569 45755687394974944579149427)
        ·
          refine ⟨68633531092462416868724141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45755687394974944579149427 68633531092462416868724141)
          ·
            refine ⟨25737574159673406325771553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68633531092462416868724141 25737574159673406325771553)
            ·
              refine ⟨19303180619755054744328665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25737574159673406325771553 19303180619755054744328665)
              ·
                refine ⟨14477385464816291058246499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19303180619755054744328665 14477385464816291058246499)
                ·
                  refine ⟨21716078197224436587369749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14477385464816291058246499 21716078197224436587369749)
                  ·
                    refine ⟨1017941165494895465032957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21716078197224436587369749 1017941165494895465032957)
                    ·
                      rfl

theorem cell23_5947300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_5947300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947300 prefixEnd_5947300 := by exact prefixLift 5947300
  have htrace : WordTrace (prefixWord ++ tailWord_5947300) baseStart_5947300 baseEnd_5947300 := by
    simpa [prefixWord, tailWord_5947300, baseEnd_5947300] using wordTrace_append hprefix tailTrace_5947300
  have hstable : (prefixWord ++ tailWord_5947300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947300).length < 2 ^ (prefixWord ++ tailWord_5947300).sum := by decide
  have hdescent : baseEnd_5947300 < baseStart_5947300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947317 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5947317 : Nat := 118140960795 + 5947317 * 2 ^ 59
def prefixEnd_5947317 : Nat := 4983230072969 + 3 ^ 40 * 5947317 * 2
def baseEnd_5947317 : Nat := 1017944075218604276195431

theorem tailTrace_5947317 : CollatzResearch.WordTrace tailWord_5947317 prefixEnd_5947317 1017944075218604276195431 := by
  unfold tailWord_5947317
  simp only [CollatzResearch.WordTrace]
  refine ⟨216916471394893704723040205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144610980929929136482026803 216916471394893704723040205)
  ·
    refine ⟨81343676773085139271140077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216916471394893704723040205 81343676773085139271140077)
    ·
      refine ⟨30503878789906927226677529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81343676773085139271140077 30503878789906927226677529)
      ·
        refine ⟨22877909092430195420008147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30503878789906927226677529 22877909092430195420008147)
        ·
          refine ⟨34316863638645293130012221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22877909092430195420008147 34316863638645293130012221)
          ·
            refine ⟨12868823864491984923754583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34316863638645293130012221 12868823864491984923754583)
            ·
              refine ⟨19303235796737977385631875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12868823864491984923754583 19303235796737977385631875)
              ·
                refine ⟨28954853695106966078447813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19303235796737977385631875 28954853695106966078447813)
                ·
                  refine ⟨5429035067832556139708965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28954853695106966078447813 5429035067832556139708965)
                  ·
                    refine ⟨1017944075218604276195431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429035067832556139708965 1017944075218604276195431)
                    ·
                      rfl

theorem cell23_5947317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5947317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947317 prefixEnd_5947317 := by exact prefixLift 5947317
  have htrace : WordTrace (prefixWord ++ tailWord_5947317) baseStart_5947317 baseEnd_5947317 := by
    simpa [prefixWord, tailWord_5947317, baseEnd_5947317] using wordTrace_append hprefix tailTrace_5947317
  have hstable : (prefixWord ++ tailWord_5947317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947317).length < 2 ^ (prefixWord ++ tailWord_5947317).sum := by decide
  have hdescent : baseEnd_5947317 < baseStart_5947317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_5947333 : Nat := 118140960795 + 5947333 * 2 ^ 59
def prefixEnd_5947333 : Nat := 4983230072969 + 3 ^ 40 * 5947333 * 2
def baseEnd_5947333 : Nat := 3053840441346284765986219

theorem tailTrace_5947333 : CollatzResearch.WordTrace tailWord_5947333 prefixEnd_5947333 3053840441346284765986219 := by
  unfold tailWord_5947333
  simp only [CollatzResearch.WordTrace]
  refine ⟨216917054962835739455622653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144611369975223826303748435 216917054962835739455622653)
  ·
    refine ⟨81343895611063402295858495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216917054962835739455622653 81343895611063402295858495)
    ·
      refine ⟨122015843416595103443787743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81343895611063402295858495 122015843416595103443787743)
      ·
        refine ⟨183023765124892655165681615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122015843416595103443787743 183023765124892655165681615)
        ·
          refine ⟨274535647687338982748522423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183023765124892655165681615 274535647687338982748522423)
          ·
            refine ⟨411803471531008474122783635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274535647687338982748522423 411803471531008474122783635)
            ·
              refine ⟨617705207296512711184175453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411803471531008474122783635 617705207296512711184175453)
              ·
                refine ⟨231639452736192266694065795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617705207296512711184175453 231639452736192266694065795)
                ·
                  refine ⟨347459179104288400041098693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231639452736192266694065795 347459179104288400041098693)
                  ·
                    refine ⟨65148596082054075007706005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347459179104288400041098693 65148596082054075007706005)
                    ·
                      refine ⟨3053840441346284765986219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65148596082054075007706005 3053840441346284765986219)
                      ·
                        rfl

theorem cell23_5947333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_5947333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947333 prefixEnd_5947333 := by exact prefixLift 5947333
  have htrace : WordTrace (prefixWord ++ tailWord_5947333) baseStart_5947333 baseEnd_5947333 := by
    simpa [prefixWord, tailWord_5947333, baseEnd_5947333] using wordTrace_append hprefix tailTrace_5947333
  have hstable : (prefixWord ++ tailWord_5947333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947333).length < 2 ^ (prefixWord ++ tailWord_5947333).sum := by decide
  have hdescent : baseEnd_5947333 < baseStart_5947333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947370 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5947370 : Nat := 118140960795 + 5947370 * 2 ^ 59
def prefixEnd_5947370 : Nat := 4983230072969 + 3 ^ 40 * 5947370 * 2
def baseEnd_5947370 : Nat := 3053859440130501121223549

theorem tailTrace_5947370 : CollatzResearch.WordTrace tailWord_5947370 prefixEnd_5947370 3053859440130501121223549 := by
  unfold tailWord_5947370
  simp only [CollatzResearch.WordTrace]
  refine ⟨54229601115925423693679891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144612269642467796516479709 54229601115925423693679891)
  ·
    refine ⟨81344401673888135540519837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54229601115925423693679891 81344401673888135540519837)
    ·
      refine ⟨30504150627708050827694939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81344401673888135540519837 30504150627708050827694939)
      ·
        refine ⟨45756225941562076241542409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30504150627708050827694939 45756225941562076241542409)
        ·
          refine ⟨34317169456171557181156807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45756225941562076241542409 34317169456171557181156807)
          ·
            refine ⟨51475754184257335771735211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34317169456171557181156807 51475754184257335771735211)
            ·
              refine ⟨77213631276386003657602817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51475754184257335771735211 77213631276386003657602817)
              ·
                refine ⟨57910223457289502743202113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77213631276386003657602817 57910223457289502743202113)
                ·
                  refine ⟨43432667592967127057401585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57910223457289502743202113 43432667592967127057401585)
                  ·
                    refine ⟨32574500694725345293051189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43432667592967127057401585 32574500694725345293051189)
                    ·
                      refine ⟨3053859440130501121223549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32574500694725345293051189 3053859440130501121223549)
                      ·
                        rfl

theorem cell23_5947370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5947370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947370 prefixEnd_5947370 := by exact prefixLift 5947370
  have htrace : WordTrace (prefixWord ++ tailWord_5947370) baseStart_5947370 baseEnd_5947370 := by
    simpa [prefixWord, tailWord_5947370, baseEnd_5947370] using wordTrace_append hprefix tailTrace_5947370
  have hstable : (prefixWord ++ tailWord_5947370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947370).length < 2 ^ (prefixWord ++ tailWord_5947370).sum := by decide
  have hdescent : baseEnd_5947370 < baseStart_5947370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947374 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_5947374 : Nat := 118140960795 + 5947374 * 2 ^ 59
def prefixEnd_5947374 : Nat := 4983230072969 + 3 ^ 40 * 5947374 * 2
def baseEnd_5947374 : Nat := 3053861494053119105573531

theorem tailTrace_5947374 : CollatzResearch.WordTrace tailWord_5947374 prefixEnd_5947374 3053861494053119105573531 := by
  unfold tailWord_5947374
  simp only [CollatzResearch.WordTrace]
  refine ⟨27114818794460900432233147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144612366903791468971910117 27114818794460900432233147)
  ·
    refine ⟨40672228191691350648349721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27114818794460900432233147 40672228191691350648349721)
    ·
      refine ⟨30504171143768512986262291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40672228191691350648349721 30504171143768512986262291)
      ·
        refine ⟨45756256715652769479393437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30504171143768512986262291 45756256715652769479393437)
        ·
          refine ⟨17158596268369788554772539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45756256715652769479393437 17158596268369788554772539)
          ·
            refine ⟨25737894402554682832158809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17158596268369788554772539 25737894402554682832158809)
            ·
              refine ⟨19303420801916012124119107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25737894402554682832158809 19303420801916012124119107)
              ·
                refine ⟨28955131202874018186178661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19303420801916012124119107 28955131202874018186178661)
                ·
                  refine ⟨5429087100538878409908499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28955131202874018186178661 5429087100538878409908499)
                  ·
                    refine ⟨8143630650808317614862749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429087100538878409908499 8143630650808317614862749)
                    ·
                      refine ⟨3053861494053119105573531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8143630650808317614862749 3053861494053119105573531)
                      ·
                        rfl

theorem cell23_5947374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_5947374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947374 prefixEnd_5947374 := by exact prefixLift 5947374
  have htrace : WordTrace (prefixWord ++ tailWord_5947374) baseStart_5947374 baseEnd_5947374 := by
    simpa [prefixWord, tailWord_5947374, baseEnd_5947374] using wordTrace_append hprefix tailTrace_5947374
  have hstable : (prefixWord ++ tailWord_5947374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947374).length < 2 ^ (prefixWord ++ tailWord_5947374).sum := by decide
  have hdescent : baseEnd_5947374 < baseStart_5947374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947400 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5947400 : Nat := 118140960795 + 5947400 * 2 ^ 59
def prefixEnd_5947400 : Nat := 4983230072969 + 3 ^ 40 * 5947400 * 2
def baseEnd_5947400 : Nat := 3053874844550136003848411

theorem tailTrace_5947400 : CollatzResearch.WordTrace tailWord_5947400 prefixEnd_5947400 3053874844550136003848411 := by
  unfold tailWord_5947400
  simp only [CollatzResearch.WordTrace]
  refine ⟨108459749326796504949155827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144612999102395339932207769 108459749326796504949155827)
  ·
    refine ⟨162689623990194757423733741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108459749326796504949155827 162689623990194757423733741)
    ·
      refine ⟨61008608996323034033900153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162689623990194757423733741 61008608996323034033900153)
      ·
        refine ⟨45756456747242275525425115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61008608996323034033900153 45756456747242275525425115)
        ·
          refine ⟨68634685120863413288137673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45756456747242275525425115 68634685120863413288137673)
          ·
            refine ⟨51476013840647559966103255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68634685120863413288137673 51476013840647559966103255)
            ·
              refine ⟨77214020760971339949154883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51476013840647559966103255 77214020760971339949154883)
              ·
                refine ⟨115821031141457009923732325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77214020760971339949154883 115821031141457009923732325)
                ·
                  refine ⟨21716443339023189360699811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115821031141457009923732325 21716443339023189360699811)
                  ·
                    refine ⟨32574665008534784041049717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21716443339023189360699811 32574665008534784041049717)
                    ·
                      refine ⟨3053874844550136003848411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32574665008534784041049717 3053874844550136003848411)
                      ·
                        rfl

theorem cell23_5947400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5947400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947400 prefixEnd_5947400 := by exact prefixLift 5947400
  have htrace : WordTrace (prefixWord ++ tailWord_5947400) baseStart_5947400 baseEnd_5947400 := by
    simpa [prefixWord, tailWord_5947400, baseEnd_5947400] using wordTrace_append hprefix tailTrace_5947400
  have hstable : (prefixWord ++ tailWord_5947400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947400).length < 2 ^ (prefixWord ++ tailWord_5947400).sum := by decide
  have hdescent : baseEnd_5947400 < baseStart_5947400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947450 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_5947450 : Nat := 118140960795 + 5947450 * 2 ^ 59
def prefixEnd_5947450 : Nat := 4983230072969 + 3 ^ 40 * 5947450 * 2
def baseEnd_5947450 : Nat := 1017966839527620269407727

theorem tailTrace_5947450 : CollatzResearch.WordTrace tailWord_5947450 prefixEnd_5947450 1017966839527620269407727 := by
  unfold tailWord_5947450
  simp only [CollatzResearch.WordTrace]
  refine ⟨54230330575852967109407951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144614214868941245625087869 54230330575852967109407951)
  ·
    refine ⟨81345495863779450664111927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54230330575852967109407951 81345495863779450664111927)
    ·
      refine ⟨122018243795669175996167891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81345495863779450664111927 122018243795669175996167891)
      ·
        refine ⟨183027365693503763994251837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122018243795669175996167891 183027365693503763994251837)
        ·
          refine ⟨68635262135063911497844439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183027365693503763994251837 68635262135063911497844439)
          ·
            refine ⟨102952893202595867246766659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68635262135063911497844439 102952893202595867246766659)
            ·
              refine ⟨154429339803893800870149989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102952893202595867246766659 154429339803893800870149989)
              ·
                refine ⟨28955501213230087663153123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154429339803893800870149989 28955501213230087663153123)
                ·
                  refine ⟨43433251819845131494729685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28955501213230087663153123 43433251819845131494729685)
                  ·
                    refine ⟨1017966839527620269407727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43433251819845131494729685 1017966839527620269407727)
                    ·
                      rfl

theorem cell23_5947450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_5947450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947450 prefixEnd_5947450 := by exact prefixLift 5947450
  have htrace : WordTrace (prefixWord ++ tailWord_5947450) baseStart_5947450 baseEnd_5947450 := by
    simpa [prefixWord, tailWord_5947450, baseEnd_5947450] using wordTrace_append hprefix tailTrace_5947450
  have hstable : (prefixWord ++ tailWord_5947450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947450).length < 2 ^ (prefixWord ++ tailWord_5947450).sum := by decide
  have hdescent : baseEnd_5947450 < baseStart_5947450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947454 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_5947454 : Nat := 118140960795 + 5947454 * 2 ^ 59
def prefixEnd_5947454 : Nat := 4983230072969 + 3 ^ 40 * 5947454 * 2
def baseEnd_5947454 : Nat := 339322508056164310285907

theorem tailTrace_5947454 : CollatzResearch.WordTrace tailWord_5947454 prefixEnd_5947454 339322508056164310285907 := by
  unfold tailWord_5947454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115183524424672140097177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144614312130264918080518277 27115183524424672140097177)
  ·
    refine ⟨20336387643318504105072883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27115183524424672140097177 20336387643318504105072883)
    ·
      refine ⟨30504581464977756157609325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20336387643318504105072883 30504581464977756157609325)
      ·
        refine ⟨11439218049366658559103497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30504581464977756157609325 11439218049366658559103497)
        ·
          refine ⟨8579413537024993919327623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11439218049366658559103497 8579413537024993919327623)
          ·
            refine ⟨12869120305537490878991435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8579413537024993919327623 12869120305537490878991435)
            ·
              refine ⟨19303680458306236318487153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12869120305537490878991435 19303680458306236318487153)
              ·
                refine ⟨14477760343729677238865365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19303680458306236318487153 14477760343729677238865365)
                ·
                  refine ⟨339322508056164310285907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14477760343729677238865365 339322508056164310285907)
                  ·
                    rfl

theorem cell23_5947454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_5947454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947454 prefixEnd_5947454 := by exact prefixLift 5947454
  have htrace : WordTrace (prefixWord ++ tailWord_5947454) baseStart_5947454 baseEnd_5947454 := by
    simpa [prefixWord, tailWord_5947454, baseEnd_5947454] using wordTrace_append hprefix tailTrace_5947454
  have hstable : (prefixWord ++ tailWord_5947454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947454).length < 2 ^ (prefixWord ++ tailWord_5947454).sum := by decide
  have hdescent : baseEnd_5947454 < baseStart_5947454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947504 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2]
def baseStart_5947504 : Nat := 118140960795 + 5947504 * 2 ^ 59
def prefixEnd_5947504 : Nat := 4983230072969 + 3 ^ 40 * 5947504 * 2
def baseEnd_5947504 : Nat := 3053928246538203596947933

theorem tailTrace_5947504 : CollatzResearch.WordTrace tailWord_5947504 prefixEnd_5947504 3053928246538203596947933 := by
  unfold tailWord_5947504
  simp only [CollatzResearch.WordTrace]
  refine ⟨108461645922608117830048783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144615527896810823773398377 108461645922608117830048783)
  ·
    refine ⟨162692468883912176745073175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108461645922608117830048783 162692468883912176745073175)
    ·
      refine ⟨244038703325868265117609763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162692468883912176745073175 244038703325868265117609763)
      ·
        refine ⟨366058054988802397676414645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244038703325868265117609763 366058054988802397676414645)
        ·
          refine ⟨34317942655200224782163873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366058054988802397676414645 34317942655200224782163873)
          ·
            refine ⟨25738456991400168586622905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34317942655200224782163873 25738456991400168586622905)
            ·
              refine ⟨19303842743550126439967179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25738456991400168586622905 19303842743550126439967179)
              ·
                refine ⟨28955764115325189659950769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19303842743550126439967179 28955764115325189659950769)
                ·
                  refine ⟨21716823086493892244963077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28955764115325189659950769 21716823086493892244963077)
                  ·
                    refine ⟨4071904328717604795930577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21716823086493892244963077 4071904328717604795930577)
                    ·
                      refine ⟨3053928246538203596947933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4071904328717604795930577 3053928246538203596947933)
                      ·
                        rfl

theorem cell23_5947504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2].length) (baseStart_5947504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947504 prefixEnd_5947504 := by exact prefixLift 5947504
  have htrace : WordTrace (prefixWord ++ tailWord_5947504) baseStart_5947504 baseEnd_5947504 := by
    simpa [prefixWord, tailWord_5947504, baseEnd_5947504] using wordTrace_append hprefix tailTrace_5947504
  have hstable : (prefixWord ++ tailWord_5947504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947504).length < 2 ^ (prefixWord ++ tailWord_5947504).sum := by decide
  have hdescent : baseEnd_5947504 < baseStart_5947504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947524 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_5947524 : Nat := 118140960795 + 5947524 * 2 ^ 59
def prefixEnd_5947524 : Nat := 4983230072969 + 3 ^ 40 * 5947524 * 2
def baseEnd_5947524 : Nat := 3053938516151293518697841

theorem tailTrace_5947524 : CollatzResearch.WordTrace tailWord_5947524 prefixEnd_5947524 3053938516151293518697841 := by
  unfold tailWord_5947524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108462010652571889537912813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144616014203429186050550417 108462010652571889537912813)
  ·
    refine ⟨40673253994714458576717305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108462010652571889537912813 40673253994714458576717305)
    ·
      refine ⟨30504940496035843932537979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40673253994714458576717305 30504940496035843932537979)
      ·
        refine ⟨45757410744053765898806969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30504940496035843932537979 45757410744053765898806969)
        ·
          refine ⟨34318058058040324424105227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45757410744053765898806969 34318058058040324424105227)
          ·
            refine ⟨51477087087060486636157841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34318058058040324424105227 51477087087060486636157841)
            ·
              refine ⟨38607815315295364977118381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51477087087060486636157841 38607815315295364977118381)
              ·
                refine ⟨14477930743235761866419393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38607815315295364977118381 14477930743235761866419393)
                ·
                  refine ⟨10858448057426821399814545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14477930743235761866419393 10858448057426821399814545)
                  ·
                    refine ⟨8143836043070116049860909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10858448057426821399814545 8143836043070116049860909)
                    ·
                      refine ⟨3053938516151293518697841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8143836043070116049860909 3053938516151293518697841)
                      ·
                        rfl

theorem cell23_5947524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_5947524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947524 prefixEnd_5947524 := by exact prefixLift 5947524
  have htrace : WordTrace (prefixWord ++ tailWord_5947524) baseStart_5947524 baseEnd_5947524 := by
    simpa [prefixWord, tailWord_5947524, baseEnd_5947524] using wordTrace_append hprefix tailTrace_5947524
  have hstable : (prefixWord ++ tailWord_5947524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947524).length < 2 ^ (prefixWord ++ tailWord_5947524).sum := by decide
  have hdescent : baseEnd_5947524 < baseStart_5947524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947548 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5947548 : Nat := 118140960795 + 5947548 * 2 ^ 59
def prefixEnd_5947548 : Nat := 4983230072969 + 3 ^ 40 * 5947548 * 2
def baseEnd_5947548 : Nat := 1017983613229000474932577

theorem tailTrace_5947548 : CollatzResearch.WordTrace tailWord_5947548 prefixEnd_5947548 1017983613229000474932577 := by
  unfold tailWord_5947548
  simp only [CollatzResearch.WordTrace]
  refine ⟨108462448328528415587349649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144616597771371220783132865 108462448328528415587349649)
  ·
    refine ⟨81346836246396311690512237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108462448328528415587349649 81346836246396311690512237)
    ·
      refine ⟨30505063592398616883942089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81346836246396311690512237 30505063592398616883942089)
      ·
        refine ⟨22878797694298962662956567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30505063592398616883942089 22878797694298962662956567)
        ·
          refine ⟨34318196541448443994434851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22878797694298962662956567 34318196541448443994434851)
          ·
            refine ⟨51477294812172665991652277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34318196541448443994434851 51477294812172665991652277)
            ·
              refine ⟨4825996388641187436717401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51477294812172665991652277 4825996388641187436717401)
              ·
                refine ⟨3619497291480890577538051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4825996388641187436717401 3619497291480890577538051)
                ·
                  refine ⟨5429245937221335866307077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619497291480890577538051 5429245937221335866307077)
                  ·
                    refine ⟨1017983613229000474932577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429245937221335866307077 1017983613229000474932577)
                    ·
                      rfl

theorem cell23_5947548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5947548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947548 prefixEnd_5947548 := by exact prefixLift 5947548
  have htrace : WordTrace (prefixWord ++ tailWord_5947548) baseStart_5947548 baseEnd_5947548 := by
    simpa [prefixWord, tailWord_5947548, baseEnd_5947548] using wordTrace_append hprefix tailTrace_5947548
  have hstable : (prefixWord ++ tailWord_5947548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947548).length < 2 ^ (prefixWord ++ tailWord_5947548).sum := by decide
  have hdescent : baseEnd_5947548 < baseStart_5947548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947557 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_5947557 : Nat := 118140960795 + 5947557 * 2 ^ 59
def prefixEnd_5947557 : Nat := 4983230072969 + 3 ^ 40 * 5947557 * 2
def baseEnd_5947557 : Nat := 1017985153670963963195063

theorem tailTrace_5947557 : CollatzResearch.WordTrace tailWord_5947557 prefixEnd_5947557 1017985153670963963195063 := by
  unfold tailWord_5947557
  simp only [CollatzResearch.WordTrace]
  refine ⟨216925224914024225711776925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144616816609349483807851283 216925224914024225711776925)
  ·
    refine ⟨81346959342759084641916347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216925224914024225711776925 81346959342759084641916347)
    ·
      refine ⟨122020439014138626962874521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81346959342759084641916347 122020439014138626962874521)
      ·
        refine ⟨91515329260603970222155891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122020439014138626962874521 91515329260603970222155891)
        ·
          refine ⟨137272993890905955333233837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91515329260603970222155891 137272993890905955333233837)
          ·
            refine ⟨51477372709089733249962689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137272993890905955333233837 51477372709089733249962689)
            ·
              refine ⟨38608029531817299937472017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51477372709089733249962689 38608029531817299937472017)
              ·
                refine ⟨28956022148862974953104013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38608029531817299937472017 28956022148862974953104013)
                ·
                  refine ⟨10858508305823615607414005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28956022148862974953104013 10858508305823615607414005)
                  ·
                    refine ⟨1017985153670963963195063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10858508305823615607414005 1017985153670963963195063)
                    ·
                      rfl

theorem cell23_5947557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_5947557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947557 prefixEnd_5947557 := by exact prefixLift 5947557
  have htrace : WordTrace (prefixWord ++ tailWord_5947557) baseStart_5947557 baseEnd_5947557 := by
    simpa [prefixWord, tailWord_5947557, baseEnd_5947557] using wordTrace_append hprefix tailTrace_5947557
  have hstable : (prefixWord ++ tailWord_5947557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947557).length < 2 ^ (prefixWord ++ tailWord_5947557).sum := by decide
  have hdescent : baseEnd_5947557 < baseStart_5947557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947605 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5947605 : Nat := 118140960795 + 5947605 * 2 ^ 59
def prefixEnd_5947605 : Nat := 4983230072969 + 3 ^ 40 * 5947605 * 2
def baseEnd_5947605 : Nat := 3053980108084307701784969

theorem tailTrace_5947605 : CollatzResearch.WordTrace tailWord_5947605 prefixEnd_5947605 3053980108084307701784969 := by
  unfold tailWord_5947605
  simp only [CollatzResearch.WordTrace]
  refine ⟨216926975617850329909524269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144617983745233553273016179 216926975617850329909524269)
  ·
    refine ⟨81347615856693873716071601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216926975617850329909524269 81347615856693873716071601)
    ·
      refine ⟨61010711892520405287053701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81347615856693873716071601 61010711892520405287053701)
      ·
        refine ⟨11439508479847575991322569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61010711892520405287053701 11439508479847575991322569)
        ·
          refine ⟨8579631359885681993491927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11439508479847575991322569 8579631359885681993491927)
          ·
            refine ⟨12869447039828522990237891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8579631359885681993491927 12869447039828522990237891)
            ·
              refine ⟨19304170559742784485356837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12869447039828522990237891 19304170559742784485356837)
              ·
                refine ⟨3619531979951772091004407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19304170559742784485356837 3619531979951772091004407)
                ·
                  refine ⟨5429297969927658136506611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619531979951772091004407 5429297969927658136506611)
                  ·
                    refine ⟨8143946954891487204759917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429297969927658136506611 8143946954891487204759917)
                    ·
                      refine ⟨3053980108084307701784969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8143946954891487204759917 3053980108084307701784969)
                      ·
                        rfl

theorem cell23_5947605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5947605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947605 prefixEnd_5947605 := by exact prefixLift 5947605
  have htrace : WordTrace (prefixWord ++ tailWord_5947605) baseStart_5947605 baseEnd_5947605 := by
    simpa [prefixWord, tailWord_5947605, baseEnd_5947605] using wordTrace_append hprefix tailTrace_5947605
  have hstable : (prefixWord ++ tailWord_5947605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947605).length < 2 ^ (prefixWord ++ tailWord_5947605).sum := by decide
  have hdescent : baseEnd_5947605 < baseStart_5947605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947607 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_5947607 : Nat := 118140960795 + 5947607 * 2 ^ 59
def prefixEnd_5947607 : Nat := 4983230072969 + 3 ^ 40 * 5947607 * 2
def baseEnd_5947607 : Nat := 3053981135045616693959959

theorem tailTrace_5947607 : CollatzResearch.WordTrace tailWord_5947607 prefixEnd_5947607 3053981135045616693959959 := by
  unfold tailWord_5947607
  simp only [CollatzResearch.WordTrace]
  refine ⟨216927048563843084251097075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144618032375895389500731383 216927048563843084251097075)
  ·
    refine ⟨325390572845764626376645613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216927048563843084251097075 325390572845764626376645613)
    ·
      refine ⟨122021464817161734891242105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325390572845764626376645613 122021464817161734891242105)
      ·
        refine ⟨91516098612871301168431579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122021464817161734891242105 91516098612871301168431579)
        ·
          refine ⟨137274147919306951752647369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91516098612871301168431579 137274147919306951752647369)
          ·
            refine ⟨102955610939480213814485527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137274147919306951752647369 102955610939480213814485527)
            ·
              refine ⟨154433416409220320721728291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102955610939480213814485527 154433416409220320721728291)
              ·
                refine ⟨231650124613830481082592437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154433416409220320721728291 231650124613830481082592437)
                ·
                  refine ⟨21717199182546607601493041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231650124613830481082592437 21717199182546607601493041)
                  ·
                    refine ⟨16287899386909955701119781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21717199182546607601493041 16287899386909955701119781)
                    ·
                      refine ⟨3053981135045616693959959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16287899386909955701119781 3053981135045616693959959)
                      ·
                        rfl

theorem cell23_5947607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_5947607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947607 prefixEnd_5947607 := by exact prefixLift 5947607
  have htrace : WordTrace (prefixWord ++ tailWord_5947607) baseStart_5947607 baseEnd_5947607 := by
    simpa [prefixWord, tailWord_5947607, baseEnd_5947607] using wordTrace_append hprefix tailTrace_5947607
  have hstable : (prefixWord ++ tailWord_5947607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947607).length < 2 ^ (prefixWord ++ tailWord_5947607).sum := by decide
  have hdescent : baseEnd_5947607 < baseStart_5947607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947621 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_5947621 : Nat := 118140960795 + 5947621 * 2 ^ 59
def prefixEnd_5947621 : Nat := 4983230072969 + 3 ^ 40 * 5947621 * 2
def baseEnd_5947621 : Nat := 1017996107924926546394965

theorem tailTrace_5947621 : CollatzResearch.WordTrace tailWord_5947621 prefixEnd_5947621 1017996107924926546394965 := by
  unfold tailWord_5947621
  simp only [CollatzResearch.WordTrace]
  refine ⟨216927559185792364642106717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144618372790528243094737811 216927559185792364642106717)
  ·
    refine ⟨81347834694672136740790019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216927559185792364642106717 81347834694672136740790019)
    ·
      refine ⟨122021752042008205111185029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81347834694672136740790019 122021752042008205111185029)
      ·
        refine ⟨22879078507876538458347193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122021752042008205111185029 22879078507876538458347193)
        ·
          refine ⟨17159308880907403843760395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22879078507876538458347193 17159308880907403843760395)
          ·
            refine ⟨25738963321361105765640593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17159308880907403843760395 25738963321361105765640593)
            ·
              refine ⟨19304222491020829324230445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25738963321361105765640593 19304222491020829324230445)
              ·
                refine ⟨7239083434132810996586417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19304222491020829324230445 7239083434132810996586417)
                ·
                  refine ⟨5429312575599608247439813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7239083434132810996586417 5429312575599608247439813)
                  ·
                    refine ⟨1017996107924926546394965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429312575599608247439813 1017996107924926546394965)
                    ·
                      rfl

theorem cell23_5947621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_5947621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947621 prefixEnd_5947621 := by exact prefixLift 5947621
  have htrace : WordTrace (prefixWord ++ tailWord_5947621) baseStart_5947621 baseEnd_5947621 := by
    simpa [prefixWord, tailWord_5947621, baseEnd_5947621] using wordTrace_append hprefix tailTrace_5947621
  have hstable : (prefixWord ++ tailWord_5947621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947621).length < 2 ^ (prefixWord ++ tailWord_5947621).sum := by decide
  have hdescent : baseEnd_5947621 < baseStart_5947621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947624 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5947624 : Nat := 118140960795 + 5947624 * 2 ^ 59
def prefixEnd_5947624 : Nat := 4983230072969 + 3 ^ 40 * 5947624 * 2
def baseEnd_5947624 : Nat := 3053989864216743127447381

theorem tailTrace_5947624 : CollatzResearch.WordTrace tailWord_5947624 prefixEnd_5947624 3053989864216743127447381 := by
  unfold tailWord_5947624
  simp only [CollatzResearch.WordTrace]
  refine ⟨108463834302390748077232963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144618445736520997436310617 108463834302390748077232963)
  ·
    refine ⟨162695751453586122115849445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108463834302390748077232963 162695751453586122115849445)
    ·
      refine ⟨30505453397547397896721771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162695751453586122115849445 30505453397547397896721771)
      ·
        refine ⟨45758180096321096845082657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30505453397547397896721771 45758180096321096845082657)
        ·
          refine ⟨34318635072240822633811993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45758180096321096845082657 34318635072240822633811993)
          ·
            refine ⟨25738976304180616975358995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34318635072240822633811993 25738976304180616975358995)
            ·
              refine ⟨38608464456270925463038493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25738976304180616975358995 38608464456270925463038493)
              ·
                refine ⟨14478174171101597048639435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38608464456270925463038493 14478174171101597048639435)
                ·
                  refine ⟨21717261256652395572959153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14478174171101597048639435 21717261256652395572959153)
                  ·
                    refine ⟨16287945942489296679719365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21717261256652395572959153 16287945942489296679719365)
                    ·
                      refine ⟨3053989864216743127447381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16287945942489296679719365 3053989864216743127447381)
                      ·
                        rfl

theorem cell23_5947624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5947624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947624 prefixEnd_5947624 := by exact prefixLift 5947624
  have htrace : WordTrace (prefixWord ++ tailWord_5947624) baseStart_5947624 baseEnd_5947624 := by
    simpa [prefixWord, tailWord_5947624, baseEnd_5947624] using wordTrace_append hprefix tailTrace_5947624
  have hstable : (prefixWord ++ tailWord_5947624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947624).length < 2 ^ (prefixWord ++ tailWord_5947624).sum := by decide
  have hdescent : baseEnd_5947624 < baseStart_5947624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947655 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 2, 4]
def baseStart_5947655 : Nat := 118140960795 + 5947655 * 2 ^ 59
def prefixEnd_5947655 : Nat := 4983230072969 + 3 ^ 40 * 5947655 * 2
def baseEnd_5947655 : Nat := 1018001927372344168719913

theorem tailTrace_5947655 : CollatzResearch.WordTrace tailWord_5947655 prefixEnd_5947655 1018001927372344168719913 := by
  unfold tailWord_5947655
  simp only [CollatzResearch.WordTrace]
  refine ⟨216928799267669188448844419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144619199511779458965896279 216928799267669188448844419)
  ·
    refine ⟨325393198901503782673266629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216928799267669188448844419 325393198901503782673266629)
    ·
      refine ⟨61011224794031959251237493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325393198901503782673266629 61011224794031959251237493)
      ·
        refine ⟨5719802324440496179803515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61011224794031959251237493 5719802324440496179803515)
        ·
          refine ⟨8579703486660744269705273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719802324440496179803515 8579703486660744269705273)
          ·
            refine ⟨6434777614995558202278955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8579703486660744269705273 6434777614995558202278955)
            ·
              refine ⟨9652166422493337303418433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434777614995558202278955 9652166422493337303418433)
              ·
                refine ⟨7239124816870002977563825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9652166422493337303418433 7239124816870002977563825)
                ·
                  refine ⟨5429343612652502233172869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7239124816870002977563825 5429343612652502233172869)
                  ·
                    refine ⟨1018001927372344168719913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429343612652502233172869 1018001927372344168719913)
                    ·
                      rfl

theorem cell23_5947655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_5947655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947655 prefixEnd_5947655 := by exact prefixLift 5947655
  have htrace : WordTrace (prefixWord ++ tailWord_5947655) baseStart_5947655 baseEnd_5947655 := by
    simpa [prefixWord, tailWord_5947655, baseEnd_5947655] using wordTrace_append hprefix tailTrace_5947655
  have hstable : (prefixWord ++ tailWord_5947655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947655).length < 2 ^ (prefixWord ++ tailWord_5947655).sum := by decide
  have hdescent : baseEnd_5947655 < baseStart_5947655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947667 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_5947667 : Nat := 118140960795 + 5947667 * 2 ^ 59
def prefixEnd_5947667 : Nat := 4983230072969 + 3 ^ 40 * 5947667 * 2
def baseEnd_5947667 : Nat := 3054011943884886459209683

theorem tailTrace_5947667 : CollatzResearch.WordTrace tailWord_5947667 prefixEnd_5947667 3054011943884886459209683 := by
  unfold tailWord_5947667
  simp only [CollatzResearch.WordTrace]
  refine ⟨216929236943625714498281255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144619491295750476332187503 216929236943625714498281255)
  ·
    refine ⟨325393855415438571747421883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216929236943625714498281255 325393855415438571747421883)
    ·
      refine ⟨488090783123157857621132825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325393855415438571747421883 488090783123157857621132825)
      ·
        refine ⟨366068087342368393215849619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488090783123157857621132825 366068087342368393215849619)
        ·
          refine ⟨549102131013552589823774429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366068087342368393215849619 549102131013552589823774429)
          ·
            refine ⟨205913299130082221183915411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549102131013552589823774429 205913299130082221183915411)
            ·
              refine ⟨308869948695123331775873117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205913299130082221183915411 308869948695123331775873117)
              ·
                refine ⟨115826230760671249415952419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308869948695123331775873117 115826230760671249415952419)
                ·
                  refine ⟨173739346141006874123928629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115826230760671249415952419 173739346141006874123928629)
                  ·
                    refine ⟨16288063700719394449118309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173739346141006874123928629 16288063700719394449118309)
                    ·
                      refine ⟨3054011943884886459209683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16288063700719394449118309 3054011943884886459209683)
                      ·
                        rfl

theorem cell23_5947667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_5947667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947667 prefixEnd_5947667 := by exact prefixLift 5947667
  have htrace : WordTrace (prefixWord ++ tailWord_5947667) baseStart_5947667 baseEnd_5947667 := by
    simpa [prefixWord, tailWord_5947667, baseEnd_5947667] using wordTrace_append hprefix tailTrace_5947667
  have hstable : (prefixWord ++ tailWord_5947667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947667).length < 2 ^ (prefixWord ++ tailWord_5947667).sum := by decide
  have hdescent : baseEnd_5947667 < baseStart_5947667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947701 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_5947701 : Nat := 118140960795 + 5947701 * 2 ^ 59
def prefixEnd_5947701 : Nat := 4983230072969 + 3 ^ 40 * 5947701 * 2
def baseEnd_5947701 : Nat := 3054029402227139326184527

theorem tailTrace_5947701 : CollatzResearch.WordTrace tailWord_5947701 prefixEnd_5947701 3054029402227139326184527 := by
  unfold tailWord_5947701
  simp only [CollatzResearch.WordTrace]
  refine ⟨216930477025502538305018957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144620318017001692203345971 216930477025502538305018957)
  ·
    refine ⟨81348928884563451864382109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216930477025502538305018957 81348928884563451864382109)
    ·
      refine ⟨30505848331711294449143291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81348928884563451864382109 30505848331711294449143291)
      ·
        refine ⟨45758772497566941673714937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30505848331711294449143291 45758772497566941673714937)
        ·
          refine ⟨34319079373175206255286203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45758772497566941673714937 34319079373175206255286203)
          ·
            refine ⟨51478619059762809382929305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34319079373175206255286203 51478619059762809382929305)
            ·
              refine ⟨38608964294822107037196979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51478619059762809382929305 38608964294822107037196979)
              ·
                refine ⟨57913446442233160555795469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38608964294822107037196979 57913446442233160555795469)
                ·
                  refine ⟨21717542415837435208423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57913446442233160555795469 21717542415837435208423301)
                  ·
                    refine ⟨4072039202969519101579369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21717542415837435208423301 4072039202969519101579369)
                    ·
                      refine ⟨3054029402227139326184527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072039202969519101579369 3054029402227139326184527)
                      ·
                        rfl

theorem cell23_5947701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_5947701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947701 prefixEnd_5947701 := by exact prefixLift 5947701
  have htrace : WordTrace (prefixWord ++ tailWord_5947701) baseStart_5947701 baseEnd_5947701 := by
    simpa [prefixWord, tailWord_5947701, baseEnd_5947701] using wordTrace_append hprefix tailTrace_5947701
  have hstable : (prefixWord ++ tailWord_5947701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947701).length < 2 ^ (prefixWord ++ tailWord_5947701).sum := by decide
  have hdescent : baseEnd_5947701 < baseStart_5947701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_5947727 : Nat := 118140960795 + 5947727 * 2 ^ 59
def prefixEnd_5947727 : Nat := 4983230072969 + 3 ^ 40 * 5947727 * 2
def baseEnd_5947727 : Nat := 3054042752724156224459407

theorem tailTrace_5947727 : CollatzResearch.WordTrace tailWord_5947727 prefixEnd_5947727 3054042752724156224459407 := by
  unfold tailWord_5947727
  simp only [CollatzResearch.WordTrace]
  refine ⟨216931425323408344745465435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144620950215605563163643623 216931425323408344745465435)
  ·
    refine ⟨325397137985112517118198153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216931425323408344745465435 325397137985112517118198153)
    ·
      refine ⟨244047853488834387838648615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325397137985112517118198153 244047853488834387838648615)
      ·
        refine ⟨366071780233251581757972923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244047853488834387838648615 366071780233251581757972923)
        ·
          refine ⟨549107670349877372636959385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366071780233251581757972923 549107670349877372636959385)
          ·
            refine ⟨411830752762408029477719539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549107670349877372636959385 411830752762408029477719539)
            ·
              refine ⟨617746129143612044216579309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411830752762408029477719539 617746129143612044216579309)
              ·
                refine ⟨231654798428854516581217241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617746129143612044216579309 231654798428854516581217241)
                ·
                  refine ⟨173741098821640887435912931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231654798428854516581217241 173741098821640887435912931)
                  ·
                    refine ⟨260611648232461331153869397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173741098821640887435912931 260611648232461331153869397)
                    ·
                      refine ⟨3054042752724156224459407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260611648232461331153869397 3054042752724156224459407)
                      ·
                        rfl

theorem cell23_5947727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_5947727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947727 prefixEnd_5947727 := by exact prefixLift 5947727
  have htrace : WordTrace (prefixWord ++ tailWord_5947727) baseStart_5947727 baseEnd_5947727 := by
    simpa [prefixWord, tailWord_5947727, baseEnd_5947727] using wordTrace_append hprefix tailTrace_5947727
  have hstable : (prefixWord ++ tailWord_5947727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947727).length < 2 ^ (prefixWord ++ tailWord_5947727).sum := by decide
  have hdescent : baseEnd_5947727 < baseStart_5947727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947801 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_5947801 : Nat := 118140960795 + 5947801 * 2 ^ 59
def prefixEnd_5947801 : Nat := 4983230072969 + 3 ^ 40 * 5947801 * 2
def baseEnd_5947801 : Nat := 1018026916764196311644689

theorem tailTrace_5947801 : CollatzResearch.WordTrace tailWord_5947801 prefixEnd_5947801 1018026916764196311644689 := by
  unfold tailWord_5947801
  simp only [CollatzResearch.WordTrace]
  refine ⟨216934124325140255383659257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144622749550093503589106171 216934124325140255383659257)
  ·
    refine ⟨162700593243855191537744443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216934124325140255383659257 162700593243855191537744443)
    ·
      refine ⟨244050889865782787306616665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162700593243855191537744443 244050889865782787306616665)
      ·
        refine ⟨183038167399337090479962499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244050889865782787306616665 183038167399337090479962499)
        ·
          refine ⟨274557251099005635719943749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183038167399337090479962499 274557251099005635719943749)
          ·
            refine ⟨51479484581063556697489453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274557251099005635719943749 51479484581063556697489453)
            ·
              refine ⟨19304806717898833761558545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51479484581063556697489453 19304806717898833761558545)
              ·
                refine ⟨14478605038424125321168909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19304806717898833761558545 14478605038424125321168909)
                ·
                  refine ⟨5429476889409046995438341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14478605038424125321168909 5429476889409046995438341)
                  ·
                    refine ⟨1018026916764196311644689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429476889409046995438341 1018026916764196311644689)
                    ·
                      rfl

theorem cell23_5947801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_5947801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947801 prefixEnd_5947801 := by exact prefixLift 5947801
  have htrace : WordTrace (prefixWord ++ tailWord_5947801) baseStart_5947801 baseEnd_5947801 := by
    simpa [prefixWord, tailWord_5947801, baseEnd_5947801] using wordTrace_append hprefix tailTrace_5947801
  have hstable : (prefixWord ++ tailWord_5947801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947801).length < 2 ^ (prefixWord ++ tailWord_5947801).sum := by decide
  have hdescent : baseEnd_5947801 < baseStart_5947801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947805 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5947805 : Nat := 118140960795 + 5947805 * 2 ^ 59
def prefixEnd_5947805 : Nat := 4983230072969 + 3 ^ 40 * 5947805 * 2
def baseEnd_5947805 : Nat := 1018027601405068973094683

theorem tailTrace_5947805 : CollatzResearch.WordTrace tailWord_5947805 prefixEnd_5947805 1018027601405068973094683 := by
  unfold tailWord_5947805
  simp only [CollatzResearch.WordTrace]
  refine ⟨216934270217125764066804869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144622846811417176044536579 216934270217125764066804869)
  ·
    refine ⟨40675175665711080762525913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216934270217125764066804869 40675175665711080762525913)
    ·
      refine ⟨30506381749283310571894435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40675175665711080762525913 30506381749283310571894435)
      ·
        refine ⟨45759572623924965857841653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30506381749283310571894435 45759572623924965857841653)
        ·
          refine ⟨4289959933492965549172655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45759572623924965857841653 4289959933492965549172655)
          ·
            refine ⟨6434939900239448323758983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289959933492965549172655 6434939900239448323758983)
            ·
              refine ⟨9652409850359172485638475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434939900239448323758983 9652409850359172485638475)
              ·
                refine ⟨14478614775538758728457713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9652409850359172485638475 14478614775538758728457713)
                ·
                  refine ⟨10858961081654069046343285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14478614775538758728457713 10858961081654069046343285)
                  ·
                    refine ⟨1018027601405068973094683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10858961081654069046343285 1018027601405068973094683)
                    ·
                      rfl

theorem cell23_5947805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5947805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947805 prefixEnd_5947805 := by exact prefixLift 5947805
  have htrace : WordTrace (prefixWord ++ tailWord_5947805) baseStart_5947805 baseEnd_5947805 := by
    simpa [prefixWord, tailWord_5947805, baseEnd_5947805] using wordTrace_append hprefix tailTrace_5947805
  have hstable : (prefixWord ++ tailWord_5947805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947805).length < 2 ^ (prefixWord ++ tailWord_5947805).sum := by decide
  have hdescent : baseEnd_5947805 < baseStart_5947805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947808 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_5947808 : Nat := 118140960795 + 5947808 * 2 ^ 59
def prefixEnd_5947808 : Nat := 4983230072969 + 3 ^ 40 * 5947808 * 2
def baseEnd_5947808 : Nat := 3054084344657170407546535

theorem tailTrace_5947808 : CollatzResearch.WordTrace tailWord_5947808 prefixEnd_5947808 3054084344657170407546535 := by
  unfold tailWord_5947808
  simp only [CollatzResearch.WordTrace]
  refine ⟨108467189818057447789582039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144622919757409930386109385 108467189818057447789582039)
  ·
    refine ⟨162700784727086171684373059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108467189818057447789582039 162700784727086171684373059)
    ·
      refine ⟨244051177090629257526559589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162700784727086171684373059 244051177090629257526559589)
      ·
        refine ⟨45759595704492985786229923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244051177090629257526559589 45759595704492985786229923)
        ·
          refine ⟨68639393556739478679344885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45759595704492985786229923 68639393556739478679344885)
          ·
            refine ⟨6434943145944326126188583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68639393556739478679344885 6434943145944326126188583)
            ·
              refine ⟨9652414718916489189282875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434943145944326126188583 9652414718916489189282875)
              ·
                refine ⟨14478622078374733783924313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9652414718916489189282875 14478622078374733783924313)
                ·
                  refine ⟨10858966558781050337943235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14478622078374733783924313 10858966558781050337943235)
                  ·
                    refine ⟨16288449838171575506914853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10858966558781050337943235 16288449838171575506914853)
                    ·
                      refine ⟨3054084344657170407546535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16288449838171575506914853 3054084344657170407546535)
                      ·
                        rfl

theorem cell23_5947808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_5947808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947808 prefixEnd_5947808 := by exact prefixLift 5947808
  have htrace : WordTrace (prefixWord ++ tailWord_5947808) baseStart_5947808 baseEnd_5947808 := by
    simpa [prefixWord, tailWord_5947808, baseEnd_5947808] using wordTrace_append hprefix tailTrace_5947808
  have hstable : (prefixWord ++ tailWord_5947808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947808).length < 2 ^ (prefixWord ++ tailWord_5947808).sum := by decide
  have hdescent : baseEnd_5947808 < baseStart_5947808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947811 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3]
def baseStart_5947811 : Nat := 118140960795 + 5947811 * 2 ^ 59
def prefixEnd_5947811 : Nat := 4983230072969 + 3 ^ 40 * 5947811 * 2
def baseEnd_5947811 : Nat := 3054085885099133895809021

theorem tailTrace_5947811 : CollatzResearch.WordTrace tailWord_5947811 prefixEnd_5947811 3054085885099133895809021 := by
  unfold tailWord_5947811
  simp only [CollatzResearch.WordTrace]
  refine ⟨216934489055104027091523287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144622992703402684727682191 216934489055104027091523287)
  ·
    refine ⟨325401733582656040637284931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216934489055104027091523287 325401733582656040637284931)
    ·
      refine ⟨488102600373984060955927397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325401733582656040637284931 488102600373984060955927397)
      ·
        refine ⟨91519237570122011429236387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 488102600373984060955927397 91519237570122011429236387)
        ·
          refine ⟨137278856355183017143854581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91519237570122011429236387 137278856355183017143854581)
          ·
            refine ⟨12869892783298407857236367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137278856355183017143854581 12869892783298407857236367)
            ·
              refine ⟨19304839174947611785854551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12869892783298407857236367 19304839174947611785854551)
              ·
                refine ⟨28957258762421417678781827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19304839174947611785854551 28957258762421417678781827)
                ·
                  refine ⟨43435888143632126518172741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28957258762421417678781827 43435888143632126518172741)
                  ·
                    refine ⟨8144229026931023722157389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43435888143632126518172741 8144229026931023722157389)
                    ·
                      refine ⟨3054085885099133895809021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8144229026931023722157389 3054085885099133895809021)
                      ·
                        rfl

theorem cell23_5947811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_5947811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947811 prefixEnd_5947811 := by exact prefixLift 5947811
  have htrace : WordTrace (prefixWord ++ tailWord_5947811) baseStart_5947811 baseEnd_5947811 := by
    simpa [prefixWord, tailWord_5947811, baseEnd_5947811] using wordTrace_append hprefix tailTrace_5947811
  have hstable : (prefixWord ++ tailWord_5947811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947811).length < 2 ^ (prefixWord ++ tailWord_5947811).sum := by decide
  have hdescent : baseEnd_5947811 < baseStart_5947811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947831 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 6]
def baseStart_5947831 : Nat := 118140960795 + 5947831 * 2 ^ 59
def prefixEnd_5947831 : Nat := 4983230072969 + 3 ^ 40 * 5947831 * 2
def baseEnd_5947831 : Nat := 339344017190247090839881

theorem tailTrace_5947831 : CollatzResearch.WordTrace tailWord_5947831 prefixEnd_5947831 339344017190247090839881 := by
  unfold tailWord_5947831
  simp only [CollatzResearch.WordTrace]
  refine ⟨216935218515031570507251347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144623479010021047004834231 216935218515031570507251347)
  ·
    refine ⟨325402827772547355760877021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216935218515031570507251347 325402827772547355760877021)
    ·
      refine ⟨122026060414705258410328883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325402827772547355760877021 122026060414705258410328883)
      ·
        refine ⟨183039090622057887615493325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122026060414705258410328883 183039090622057887615493325)
        ·
          refine ⟨68639658983271707855809997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183039090622057887615493325 68639658983271707855809997)
          ·
            refine ⟨25739872118726890445928749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68639658983271707855809997 25739872118726890445928749)
            ·
              refine ⟨9652452044522583917223281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25739872118726890445928749 9652452044522583917223281)
              ·
                refine ⟨7239339033391937937917461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9652452044522583917223281 7239339033391937937917461)
                ·
                  refine ⟨339344017190247090839881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7239339033391937937917461 339344017190247090839881)
                  ·
                    rfl

theorem cell23_5947831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 6].length) (baseStart_5947831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947831 prefixEnd_5947831 := by exact prefixLift 5947831
  have htrace : WordTrace (prefixWord ++ tailWord_5947831) baseStart_5947831 baseEnd_5947831 := by
    simpa [prefixWord, tailWord_5947831, baseEnd_5947831] using wordTrace_append hprefix tailTrace_5947831
  have hstable : (prefixWord ++ tailWord_5947831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947831).length < 2 ^ (prefixWord ++ tailWord_5947831).sum := by decide
  have hdescent : baseEnd_5947831 < baseStart_5947831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947848 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 6]
def baseStart_5947848 : Nat := 118140960795 + 5947848 * 2 ^ 59
def prefixEnd_5947848 : Nat := 4983230072969 + 3 ^ 40 * 5947848 * 2
def baseEnd_5947848 : Nat := 339344987098150027894039

theorem tailTrace_5947848 : CollatzResearch.WordTrace tailWord_5947848 prefixEnd_5947848 339344987098150027894039 := by
  unfold tailWord_5947848
  simp only [CollatzResearch.WordTrace]
  refine ⟨108467919277984991205310099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144623892370646654940413465 108467919277984991205310099)
  ·
    refine ⟨162701878916977486807965149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108467919277984991205310099 162701878916977486807965149)
    ·
      refine ⟨61013204593866557552986931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162701878916977486807965149 61013204593866557552986931)
      ·
        refine ⟨91519806890799836329480397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61013204593866557552986931 91519806890799836329480397)
        ·
          refine ⟨34319927584049938623555149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91519806890799836329480397 34319927584049938623555149)
          ·
            refine ⟨12869972844018726983833181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34319927584049938623555149 12869972844018726983833181)
            ·
              refine ⟨4826239816507022618937443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12869972844018726983833181 4826239816507022618937443)
              ·
                refine ⟨7239359724760533928406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826239816507022618937443 7239359724760533928406165)
                ·
                  refine ⟨339344987098150027894039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7239359724760533928406165 339344987098150027894039)
                  ·
                    rfl

theorem cell23_5947848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 6].length) (baseStart_5947848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947848 prefixEnd_5947848 := by exact prefixLift 5947848
  have htrace : WordTrace (prefixWord ++ tailWord_5947848) baseStart_5947848 baseEnd_5947848 := by
    simpa [prefixWord, tailWord_5947848, baseEnd_5947848] using wordTrace_append hprefix tailTrace_5947848
  have hstable : (prefixWord ++ tailWord_5947848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947848).length < 2 ^ (prefixWord ++ tailWord_5947848).sum := by decide
  have hdescent : baseEnd_5947848 < baseStart_5947848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947885 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5947885 : Nat := 118140960795 + 5947885 * 2 ^ 59
def prefixEnd_5947885 : Nat := 4983230072969 + 3 ^ 40 * 5947885 * 2
def baseEnd_5947885 : Nat := 3054123882667566606283681

theorem tailTrace_5947885 : CollatzResearch.WordTrace tailWord_5947885 prefixEnd_5947885 3054123882667566606283681 := by
  unfold tailWord_5947885
  simp only [CollatzResearch.WordTrace]
  refine ⟨216937188056835937729717109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144624792037890625153144739 216937188056835937729717109)
  ·
    refine ⟨20337861380328369162160979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216937188056835937729717109 20337861380328369162160979)
    ·
      refine ⟨30506792070492553743241469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20337861380328369162160979 30506792070492553743241469)
      ·
        refine ⟨11440047026434707653715551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30506792070492553743241469 11440047026434707653715551)
        ·
          refine ⟨17160070539652061480573327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11440047026434707653715551 17160070539652061480573327)
          ·
            refine ⟨25740105809478092220859991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17160070539652061480573327 25740105809478092220859991)
            ·
              refine ⟨38610158714217138331289987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25740105809478092220859991 38610158714217138331289987)
              ·
                refine ⟨57915238071325707496934981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38610158714217138331289987 57915238071325707496934981)
                ·
                  refine ⟨10859107138373570155675309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57915238071325707496934981 10859107138373570155675309)
                  ·
                    refine ⟨4072165176890088808378241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10859107138373570155675309 4072165176890088808378241)
                    ·
                      refine ⟨3054123882667566606283681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072165176890088808378241 3054123882667566606283681)
                      ·
                        rfl

theorem cell23_5947885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5947885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947885 prefixEnd_5947885 := by exact prefixLift 5947885
  have htrace : WordTrace (prefixWord ++ tailWord_5947885) baseStart_5947885 baseEnd_5947885 := by
    simpa [prefixWord, tailWord_5947885, baseEnd_5947885] using wordTrace_append hprefix tailTrace_5947885
  have hstable : (prefixWord ++ tailWord_5947885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947885).length < 2 ^ (prefixWord ++ tailWord_5947885).sum := by decide
  have hdescent : baseEnd_5947885 < baseStart_5947885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947891 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 4, 4]
def baseStart_5947891 : Nat := 118140960795 + 5947891 * 2 ^ 59
def prefixEnd_5947891 : Nat := 4983230072969 + 3 ^ 40 * 5947891 * 2
def baseEnd_5947891 : Nat := 1018042321183831194269551

theorem tailTrace_5947891 : CollatzResearch.WordTrace tailWord_5947891 prefixEnd_5947891 1018042321183831194269551 := by
  unfold tailWord_5947891
  simp only [CollatzResearch.WordTrace]
  refine ⟨216937406894814200754435527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144624937929876133836290351 216937406894814200754435527)
  ·
    refine ⟨325406110342221301131653291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216937406894814200754435527 325406110342221301131653291)
    ·
      refine ⟨488109165513331951697479937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325406110342221301131653291 488109165513331951697479937)
      ·
        refine ⟨366081874134998963773109953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488109165513331951697479937 366081874134998963773109953)
        ·
          refine ⟨274561405601249222829832465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366081874134998963773109953 274561405601249222829832465)
          ·
            refine ⟨205921054200936917122374349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274561405601249222829832465 205921054200936917122374349)
            ·
              refine ⟨77220395325351343920890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205921054200936917122374349 77220395325351343920890381)
              ·
                refine ⟨28957648247006753970333893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77220395325351343920890381 28957648247006753970333893)
                ·
                  refine ⟨5429559046313766369437605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28957648247006753970333893 5429559046313766369437605)
                  ·
                    refine ⟨1018042321183831194269551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429559046313766369437605 1018042321183831194269551)
                    ·
                      rfl

theorem cell23_5947891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4].length) (baseStart_5947891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947891 prefixEnd_5947891 := by exact prefixLift 5947891
  have htrace : WordTrace (prefixWord ++ tailWord_5947891) baseStart_5947891 baseEnd_5947891 := by
    simpa [prefixWord, tailWord_5947891, baseEnd_5947891] using wordTrace_append hprefix tailTrace_5947891
  have hstable : (prefixWord ++ tailWord_5947891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947891).length < 2 ^ (prefixWord ++ tailWord_5947891).sum := by decide
  have hdescent : baseEnd_5947891 < baseStart_5947891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947901 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_5947901 : Nat := 118140960795 + 5947901 * 2 ^ 59
def prefixEnd_5947901 : Nat := 4983230072969 + 3 ^ 40 * 5947901 * 2
def baseEnd_5947901 : Nat := 3054132098358038543683607

theorem tailTrace_5947901 : CollatzResearch.WordTrace tailWord_5947901 prefixEnd_5947901 3054132098358038543683607 := by
  unfold tailWord_5947901
  simp only [CollatzResearch.WordTrace]
  refine ⟨216937771624777972462299557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144625181083185314974866371 216937771624777972462299557)
  ·
    refine ⟨40675832179645869836681167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216937771624777972462299557 40675832179645869836681167)
    ·
      refine ⟨61013748269468804755021751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40675832179645869836681167 61013748269468804755021751)
      ·
        refine ⟨91520622404203207132532627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61013748269468804755021751 91520622404203207132532627)
        ·
          refine ⟨137280933606304810698798941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91520622404203207132532627 137280933606304810698798941)
          ·
            refine ⟨51480350102364304012049603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137280933606304810698798941 51480350102364304012049603)
            ·
              refine ⟨77220525153546456018074405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51480350102364304012049603 77220525153546456018074405)
              ·
                refine ⟨14478848466289960503388951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77220525153546456018074405 14478848466289960503388951)
                ·
                  refine ⟨21718272699434940755083427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14478848466289960503388951 21718272699434940755083427)
                  ·
                    refine ⟨32577409049152411132625141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21718272699434940755083427 32577409049152411132625141)
                    ·
                      refine ⟨3054132098358038543683607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32577409049152411132625141 3054132098358038543683607)
                      ·
                        rfl

theorem cell23_5947901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_5947901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947901 prefixEnd_5947901 := by exact prefixLift 5947901
  have htrace : WordTrace (prefixWord ++ tailWord_5947901) baseStart_5947901 baseEnd_5947901 := by
    simpa [prefixWord, tailWord_5947901, baseEnd_5947901] using wordTrace_append hprefix tailTrace_5947901
  have hstable : (prefixWord ++ tailWord_5947901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947901).length < 2 ^ (prefixWord ++ tailWord_5947901).sum := by decide
  have hdescent : baseEnd_5947901 < baseStart_5947901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947915 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 4]
def baseStart_5947915 : Nat := 118140960795 + 5947915 * 2 ^ 59
def prefixEnd_5947915 : Nat := 4983230072969 + 3 ^ 40 * 5947915 * 2
def baseEnd_5947915 : Nat := 3054139287087201488908543

theorem tailTrace_5947915 : CollatzResearch.WordTrace tailWord_5947915 prefixEnd_5947915 3054139287087201488908543 := by
  unfold tailWord_5947915
  simp only [CollatzResearch.WordTrace]
  refine ⟨216938282246727252853309199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144625521497818168568872799 216938282246727252853309199)
  ·
    refine ⟨325407423370090879279963799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216938282246727252853309199 325407423370090879279963799)
    ·
      refine ⟨488111135055136318919945699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325407423370090879279963799 488111135055136318919945699)
      ·
        refine ⟨732166702582704478379918549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488111135055136318919945699 732166702582704478379918549)
        ·
          refine ⟨17160157091782136212029341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 732166702582704478379918549 17160157091782136212029341)
          ·
            refine ⟨6435058909418301079511003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17160157091782136212029341 6435058909418301079511003)
            ·
              refine ⟨9652588364127451619266505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435058909418301079511003 9652588364127451619266505)
              ·
                refine ⟨7239441273095588714449879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9652588364127451619266505 7239441273095588714449879)
                ·
                  refine ⟨10859161909643383071674819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7239441273095588714449879 10859161909643383071674819)
                  ·
                    refine ⟨16288742864465074607512229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10859161909643383071674819 16288742864465074607512229)
                    ·
                      refine ⟨3054139287087201488908543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16288742864465074607512229 3054139287087201488908543)
                      ·
                        rfl

theorem cell23_5947915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 4].length) (baseStart_5947915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947915 prefixEnd_5947915 := by exact prefixLift 5947915
  have htrace : WordTrace (prefixWord ++ tailWord_5947915) baseStart_5947915 baseEnd_5947915 := by
    simpa [prefixWord, tailWord_5947915, baseEnd_5947915] using wordTrace_append hprefix tailTrace_5947915
  have hstable : (prefixWord ++ tailWord_5947915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947915).length < 2 ^ (prefixWord ++ tailWord_5947915).sum := by decide
  have hdescent : baseEnd_5947915 < baseStart_5947915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947928 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5947928 : Nat := 118140960795 + 5947928 * 2 ^ 59
def prefixEnd_5947928 : Nat := 4983230072969 + 3 ^ 40 * 5947928 * 2
def baseEnd_5947928 : Nat := 3054145962335709938045983

theorem tailTrace_5947928 : CollatzResearch.WordTrace tailWord_5947928 prefixEnd_5947928 3054145962335709938045983 := by
  unfold tailWord_5947928
  simp only [CollatzResearch.WordTrace]
  refine ⟨108469378197840078036766219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144625837597120104049021625 108469378197840078036766219)
  ·
    refine ⟨162704067296760117055149329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108469378197840078036766219 162704067296760117055149329)
    ·
      refine ⟨122028050472570087791361997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162704067296760117055149329 122028050472570087791361997)
      ·
        refine ⟨45760518927213782921760749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122028050472570087791361997 45760518927213782921760749)
        ·
          refine ⟨17160194597705168595660281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45760518927213782921760749 17160194597705168595660281)
          ·
            refine ⟨12870145948278876446745211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17160194597705168595660281 12870145948278876446745211)
            ·
              refine ⟨19305218922418314670117817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12870145948278876446745211 19305218922418314670117817)
              ·
                refine ⟨14478914191813736002588363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19305218922418314670117817 14478914191813736002588363)
                ·
                  refine ⟨21718371287720604003882545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14478914191813736002588363 21718371287720604003882545)
                  ·
                    refine ⟨16288778465790453002911909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21718371287720604003882545 16288778465790453002911909)
                    ·
                      refine ⟨3054145962335709938045983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16288778465790453002911909 3054145962335709938045983)
                      ·
                        rfl

theorem cell23_5947928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5947928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947928 prefixEnd_5947928 := by exact prefixLift 5947928
  have htrace : WordTrace (prefixWord ++ tailWord_5947928) baseStart_5947928 baseEnd_5947928 := by
    simpa [prefixWord, tailWord_5947928, baseEnd_5947928] using wordTrace_append hprefix tailTrace_5947928
  have hstable : (prefixWord ++ tailWord_5947928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947928).length < 2 ^ (prefixWord ++ tailWord_5947928).sum := by decide
  have hdescent : baseEnd_5947928 < baseStart_5947928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947943 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5947943 : Nat := 118140960795 + 5947943 * 2 ^ 59
def prefixEnd_5947943 : Nat := 4983230072969 + 3 ^ 40 * 5947943 * 2
def baseEnd_5947943 : Nat := 3054153664545527379358415

theorem tailTrace_5947943 : CollatzResearch.WordTrace tailWord_5947943 prefixEnd_5947943 3054153664545527379358415 := by
  unfold tailWord_5947943
  simp only [CollatzResearch.WordTrace]
  refine ⟨216939303490625813635328483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144626202327083875756885655 216939303490625813635328483)
  ·
    refine ⟨325408955235938720452992725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216939303490625813635328483 325408955235938720452992725)
    ·
      refine ⟨7626772388342313760617017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 325408955235938720452992725 7626772388342313760617017)
      ·
        refine ⟨5720079291256735320462763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7626772388342313760617017 5720079291256735320462763)
        ·
          refine ⟨8580118936885102980694145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720079291256735320462763 8580118936885102980694145)
          ·
            refine ⟨6435089202663827235520609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8580118936885102980694145 6435089202663827235520609)
            ·
              refine ⟨4826316901997870426640457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6435089202663827235520609 4826316901997870426640457)
              ·
                refine ⟨3619737676498402819980343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826316901997870426640457 3619737676498402819980343)
                ·
                  refine ⟨5429606514747604229970515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619737676498402819980343 5429606514747604229970515)
                  ·
                    refine ⟨8144409772121406344955773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429606514747604229970515 8144409772121406344955773)
                    ·
                      refine ⟨3054153664545527379358415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8144409772121406344955773 3054153664545527379358415)
                      ·
                        rfl

theorem cell23_5947943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5947943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947943 prefixEnd_5947943 := by exact prefixLift 5947943
  have htrace : WordTrace (prefixWord ++ tailWord_5947943) baseStart_5947943 baseEnd_5947943 := by
    simpa [prefixWord, tailWord_5947943, baseEnd_5947943] using wordTrace_append hprefix tailTrace_5947943
  have hstable : (prefixWord ++ tailWord_5947943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947943).length < 2 ^ (prefixWord ++ tailWord_5947943).sum := by decide
  have hdescent : baseEnd_5947943 < baseStart_5947943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947948 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_5947948 : Nat := 118140960795 + 5947948 * 2 ^ 59
def prefixEnd_5947948 : Nat := 4983230072969 + 3 ^ 40 * 5947948 * 2
def baseEnd_5947948 : Nat := 3054156231948799859795891

theorem tailTrace_5947948 : CollatzResearch.WordTrace tailWord_5947948 prefixEnd_5947948 3054156231948799859795891 := by
  unfold tailWord_5947948
  simp only [CollatzResearch.WordTrace]
  refine ⟨108469742927803849744630249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144626323903738466326173665 108469742927803849744630249)
  ·
    refine ⟨81352307195852887308472687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108469742927803849744630249 81352307195852887308472687)
    ·
      refine ⟨122028460793779330962709031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81352307195852887308472687 122028460793779330962709031)
      ·
        refine ⟨183042691190668996444063547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122028460793779330962709031 183042691190668996444063547)
        ·
          refine ⟨274564036786003494666095321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183042691190668996444063547 274564036786003494666095321)
          ·
            refine ⟨205923027589502620999571491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274564036786003494666095321 205923027589502620999571491)
            ·
              refine ⟨308884541384253931499357237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205923027589502620999571491 308884541384253931499357237)
              ·
                refine ⟨28957925754773806078064741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308884541384253931499357237 28957925754773806078064741)
                ·
                  refine ⟨5429611079020088639637139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28957925754773806078064741 5429611079020088639637139)
                  ·
                    refine ⟨8144416618530132959455709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429611079020088639637139 8144416618530132959455709)
                    ·
                      refine ⟨3054156231948799859795891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8144416618530132959455709 3054156231948799859795891)
                      ·
                        rfl

theorem cell23_5947948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_5947948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947948 prefixEnd_5947948 := by exact prefixLift 5947948
  have htrace : WordTrace (prefixWord ++ tailWord_5947948) baseStart_5947948 baseEnd_5947948 := by
    simpa [prefixWord, tailWord_5947948, baseEnd_5947948] using wordTrace_append hprefix tailTrace_5947948
  have hstable : (prefixWord ++ tailWord_5947948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947948).length < 2 ^ (prefixWord ++ tailWord_5947948).sum := by decide
  have hdescent : baseEnd_5947948 < baseStart_5947948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947965 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5947965 : Nat := 118140960795 + 5947965 * 2 ^ 59
def prefixEnd_5947965 : Nat := 4983230072969 + 3 ^ 40 * 5947965 * 2
def baseEnd_5947965 : Nat := 3054164961119926293283313

theorem tailTrace_5947965 : CollatzResearch.WordTrace tailWord_5947965 prefixEnd_5947965 3054164961119926293283313 := by
  unfold tailWord_5947965
  simp only [CollatzResearch.WordTrace]
  refine ⟨216940105896546111392629349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144626737264364074261752899 216940105896546111392629349)
  ·
    refine ⟨40676269855602395886118003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216940105896546111392629349 40676269855602395886118003)
    ·
      refine ⟨61014404783403593829177005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40676269855602395886118003 61014404783403593829177005)
      ·
        refine ⟨22880401793776347685941377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61014404783403593829177005 22880401793776347685941377)
        ·
          refine ⟨17160301345332260764456033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22880401793776347685941377 17160301345332260764456033)
          ·
            refine ⟨12870226008999195573342025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17160301345332260764456033 12870226008999195573342025)
            ·
              refine ⟨9652669506749396680006519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12870226008999195573342025 9652669506749396680006519)
              ·
                refine ⟨14479004260124095020009779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9652669506749396680006519 14479004260124095020009779)
                ·
                  refine ⟨21718506390186142530014669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14479004260124095020009779 21718506390186142530014669)
                  ·
                    refine ⟨8144439896319803448755501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21718506390186142530014669 8144439896319803448755501)
                    ·
                      refine ⟨3054164961119926293283313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8144439896319803448755501 3054164961119926293283313)
                      ·
                        rfl

theorem cell23_5947965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5947965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947965 prefixEnd_5947965 := by exact prefixLift 5947965
  have htrace : WordTrace (prefixWord ++ tailWord_5947965) baseStart_5947965 baseEnd_5947965 := by
    simpa [prefixWord, tailWord_5947965, baseEnd_5947965] using wordTrace_append hprefix tailTrace_5947965
  have hstable : (prefixWord ++ tailWord_5947965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947965).length < 2 ^ (prefixWord ++ tailWord_5947965).sum := by decide
  have hdescent : baseEnd_5947965 < baseStart_5947965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947975 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_5947975 : Nat := 118140960795 + 5947975 * 2 ^ 59
def prefixEnd_5947975 : Nat := 4983230072969 + 3 ^ 40 * 5947975 * 2
def baseEnd_5947975 : Nat := 3054170095926471254158267

theorem tailTrace_5947975 : CollatzResearch.WordTrace tailWord_5947975 prefixEnd_5947975 3054170095926471254158267 := by
  unfold tailWord_5947975
  simp only [CollatzResearch.WordTrace]
  refine ⟨216940470626509883100493379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144626980417673255400328919 216940470626509883100493379)
  ·
    refine ⟨325410705939764824650740069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216940470626509883100493379 325410705939764824650740069)
    ·
      refine ⟨61014507363705904622013763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325410705939764824650740069 61014507363705904622013763)
      ·
        refine ⟨91521761045558856933020645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61014507363705904622013763 91521761045558856933020645)
        ·
          refine ⟨17160330196042285674941371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91521761045558856933020645 17160330196042285674941371)
          ·
            refine ⟨25740495294063428512412057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17160330196042285674941371 25740495294063428512412057)
            ·
              refine ⟨19305371470547571384309043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25740495294063428512412057 19305371470547571384309043)
              ·
                refine ⟨28958057205821357076463565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19305371470547571384309043 28958057205821357076463565)
                ·
                  refine ⟨10859271452183008903673837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28958057205821357076463565 10859271452183008903673837)
                  ·
                    refine ⟨4072226794568628338877689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10859271452183008903673837 4072226794568628338877689)
                    ·
                      refine ⟨3054170095926471254158267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072226794568628338877689 3054170095926471254158267)
                      ·
                        rfl

theorem cell23_5947975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_5947975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947975 prefixEnd_5947975 := by exact prefixLift 5947975
  have htrace : WordTrace (prefixWord ++ tailWord_5947975) baseStart_5947975 baseEnd_5947975 := by
    simpa [prefixWord, tailWord_5947975, baseEnd_5947975] using wordTrace_append hprefix tailTrace_5947975
  have hstable : (prefixWord ++ tailWord_5947975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947975).length < 2 ^ (prefixWord ++ tailWord_5947975).sum := by decide
  have hdescent : baseEnd_5947975 < baseStart_5947975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947991 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_5947991 : Nat := 118140960795 + 5947991 * 2 ^ 59
def prefixEnd_5947991 : Nat := 4983230072969 + 3 ^ 40 * 5947991 * 2
def baseEnd_5947991 : Nat := 3054178311616943191558193

theorem tailTrace_5947991 : CollatzResearch.WordTrace tailWord_5947991 prefixEnd_5947991 3054178311616943191558193 := by
  unfold tailWord_5947991
  simp only [CollatzResearch.WordTrace]
  refine ⟨216941054194451917833075827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144627369462967945222050551 216941054194451917833075827)
  ·
    refine ⟨325411581291677876749613741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216941054194451917833075827 325411581291677876749613741)
    ·
      refine ⟨122029342984379203781105153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325411581291677876749613741 122029342984379203781105153)
      ·
        refine ⟨91522007238284402835828865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122029342984379203781105153 91522007238284402835828865)
        ·
          refine ⟨68641505428713302126871649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91522007238284402835828865 68641505428713302126871649)
          ·
            refine ⟨51481129071534976595153737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68641505428713302126871649 51481129071534976595153737)
            ·
              refine ⟨38610846803651232446365303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51481129071534976595153737 38610846803651232446365303)
              ·
                refine ⟨57916270205476848669547955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38610846803651232446365303 57916270205476848669547955)
                ·
                  refine ⟨86874405308215273004321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57916270205476848669547955 86874405308215273004321933)
                  ·
                    refine ⟨32577901990580727376620725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86874405308215273004321933 32577901990580727376620725)
                    ·
                      refine ⟨3054178311616943191558193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32577901990580727376620725 3054178311616943191558193)
                      ·
                        rfl

theorem cell23_5947991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_5947991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947991 prefixEnd_5947991 := by exact prefixLift 5947991
  have htrace : WordTrace (prefixWord ++ tailWord_5947991) baseStart_5947991 baseEnd_5947991 := by
    simpa [prefixWord, tailWord_5947991, baseEnd_5947991] using wordTrace_append hprefix tailTrace_5947991
  have hstable : (prefixWord ++ tailWord_5947991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947991).length < 2 ^ (prefixWord ++ tailWord_5947991).sum := by decide
  have hdescent : baseEnd_5947991 < baseStart_5947991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5947992 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_5947992 : Nat := 118140960795 + 5947992 * 2 ^ 59
def prefixEnd_5947992 : Nat := 4983230072969 + 3 ^ 40 * 5947992 * 2
def baseEnd_5947992 : Nat := 3054178825097597687645689

theorem tailTrace_5947992 : CollatzResearch.WordTrace tailWord_5947992 prefixEnd_5947992 3054178825097597687645689 := by
  unfold tailWord_5947992
  simp only [CollatzResearch.WordTrace]
  refine ⟨108470545333724147501931115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144627393778298863335908153 108470545333724147501931115)
  ·
    refine ⟨162705818000586221252896673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108470545333724147501931115 162705818000586221252896673)
    ·
      refine ⟨122029363500439665939672505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162705818000586221252896673 122029363500439665939672505)
      ·
        refine ⟨91522022625329749454754379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122029363500439665939672505 91522022625329749454754379)
        ·
          refine ⟨137283033937994624182131569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91522022625329749454754379 137283033937994624182131569)
          ·
            refine ⟨102962275453495968136598677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137283033937994624182131569 102962275453495968136598677)
            ·
              refine ⟨4826356661882623506403063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102962275453495968136598677 4826356661882623506403063)
              ·
                refine ⟨7239534992823935259604595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826356661882623506403063 7239534992823935259604595)
                ·
                  refine ⟨10859302489235902889406893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7239534992823935259604595 10859302489235902889406893)
                  ·
                    refine ⟨4072238433463463583527585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10859302489235902889406893 4072238433463463583527585)
                    ·
                      refine ⟨3054178825097597687645689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072238433463463583527585 3054178825097597687645689)
                      ·
                        rfl

theorem cell23_5947992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_5947992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5947992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5947992 prefixEnd_5947992 := by exact prefixLift 5947992
  have htrace : WordTrace (prefixWord ++ tailWord_5947992) baseStart_5947992 baseEnd_5947992 := by
    simpa [prefixWord, tailWord_5947992, baseEnd_5947992] using wordTrace_append hprefix tailTrace_5947992
  have hstable : (prefixWord ++ tailWord_5947992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5947992).length < 2 ^ (prefixWord ++ tailWord_5947992).sum := by decide
  have hdescent : baseEnd_5947992 < baseStart_5947992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5947992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948048 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2]
def baseStart_5948048 : Nat := 118140960795 + 5948048 * 2 ^ 59
def prefixEnd_5948048 : Nat := 4983230072969 + 3 ^ 40 * 5948048 * 2
def baseEnd_5948048 : Nat := 3054207580014249468545431

theorem tailTrace_5948048 : CollatzResearch.WordTrace tailWord_5948048 prefixEnd_5948048 3054207580014249468545431 := by
  unfold tailWord_5948048
  simp only [CollatzResearch.WordTrace]
  refine ⟨108471566577622708283950399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144628755436830277711933865 108471566577622708283950399)
  ·
    refine ⟨162707349866434062425925599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108471566577622708283950399 162707349866434062425925599)
    ·
      refine ⟨244061024799651093638888399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162707349866434062425925599 244061024799651093638888399)
      ·
        refine ⟨366091537199476640458332599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244061024799651093638888399 366091537199476640458332599)
        ·
          refine ⟨549137305799214960687498899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366091537199476640458332599 549137305799214960687498899)
          ·
            refine ⟨823705958698822441031248349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549137305799214960687498899 823705958698822441031248349)
            ·
              refine ⟨308889734512058415386718131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823705958698822441031248349 308889734512058415386718131)
              ·
                refine ⟨463334601768087623080077197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308889734512058415386718131 463334601768087623080077197)
                ·
                  refine ⟨173750475663032858655028949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463334601768087623080077197 173750475663032858655028949)
                  ·
                    refine ⟨4072276773352332624727241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 173750475663032858655028949 4072276773352332624727241)
                    ·
                      refine ⟨3054207580014249468545431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072276773352332624727241 3054207580014249468545431)
                      ·
                        rfl

theorem cell23_5948048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2].length) (baseStart_5948048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948048 prefixEnd_5948048 := by exact prefixLift 5948048
  have htrace : WordTrace (prefixWord ++ tailWord_5948048) baseStart_5948048 baseEnd_5948048 := by
    simpa [prefixWord, tailWord_5948048, baseEnd_5948048] using wordTrace_append hprefix tailTrace_5948048
  have hstable : (prefixWord ++ tailWord_5948048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948048).length < 2 ^ (prefixWord ++ tailWord_5948048).sum := by decide
  have hdescent : baseEnd_5948048 < baseStart_5948048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948051 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_5948051 : Nat := 118140960795 + 5948051 * 2 ^ 59
def prefixEnd_5948051 : Nat := 4983230072969 + 3 ^ 40 * 5948051 * 2
def baseEnd_5948051 : Nat := 3054209120456212956807917

theorem tailTrace_5948051 : CollatzResearch.WordTrace tailWord_5948051 prefixEnd_5948051 3054209120456212956807917 := by
  unfold tailWord_5948051
  simp only [CollatzResearch.WordTrace]
  refine ⟨216943242574234548080260007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144628828382823032053506671 216943242574234548080260007)
  ·
    refine ⟨325414863861351822120390011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216943242574234548080260007 325414863861351822120390011)
    ·
      refine ⟨488122295792027733180585017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325414863861351822120390011 488122295792027733180585017)
      ·
        refine ⟨366091721844020799885438763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488122295792027733180585017 366091721844020799885438763)
        ·
          refine ⟨549137582766031199828158145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366091721844020799885438763 549137582766031199828158145)
          ·
            refine ⟨411853187074523399871118609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549137582766031199828158145 411853187074523399871118609)
            ·
              refine ⟨308889890305892549903338957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411853187074523399871118609 308889890305892549903338957)
              ·
                refine ⟨115833708864709706213752109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308889890305892549903338957 115833708864709706213752109)
                ·
                  refine ⟨43437640824266139830157041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115833708864709706213752109 43437640824266139830157041)
                  ·
                    refine ⟨32578230618199604872617781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43437640824266139830157041 32578230618199604872617781)
                    ·
                      refine ⟨3054209120456212956807917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32578230618199604872617781 3054209120456212956807917)
                      ·
                        rfl

theorem cell23_5948051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_5948051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948051 prefixEnd_5948051 := by exact prefixLift 5948051
  have htrace : WordTrace (prefixWord ++ tailWord_5948051) baseStart_5948051 baseEnd_5948051 := by
    simpa [prefixWord, tailWord_5948051, baseEnd_5948051] using wordTrace_append hprefix tailTrace_5948051
  have hstable : (prefixWord ++ tailWord_5948051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948051).length < 2 ^ (prefixWord ++ tailWord_5948051).sum := by decide
  have hdescent : baseEnd_5948051 < baseStart_5948051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948068 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_5948068 : Nat := 118140960795 + 5948068 * 2 ^ 59
def prefixEnd_5948068 : Nat := 4983230072969 + 3 ^ 40 * 5948068 * 2
def baseEnd_5948068 : Nat := 3054217849627339390295339

theorem tailTrace_5948068 : CollatzResearch.WordTrace tailWord_5948068 prefixEnd_5948068 3054217849627339390295339 := by
  unfold tailWord_5948068
  simp only [CollatzResearch.WordTrace]
  refine ⟨108471931307586479991814429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144629241743448639989085905 108471931307586479991814429)
  ·
    refine ⟨40676974240344929996930411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108471931307586479991814429 40676974240344929996930411)
    ·
      refine ⟨61015461360517394995395617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40676974240344929996930411 61015461360517394995395617)
      ·
        refine ⟨45761596020388046246546713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61015461360517394995395617 45761596020388046246546713)
        ·
          refine ⟨34321197015291034684910035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45761596020388046246546713 34321197015291034684910035)
          ·
            refine ⟨51481795522936552027365053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34321197015291034684910035 51481795522936552027365053)
            ·
              refine ⟨19305673321101207010261895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51481795522936552027365053 19305673321101207010261895)
              ·
                refine ⟨28958509981651810515392843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19305673321101207010261895 28958509981651810515392843)
                ·
                  refine ⟨43437764972477715773089265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28958509981651810515392843 43437764972477715773089265)
                  ·
                    refine ⟨32578323729358286829816949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43437764972477715773089265 32578323729358286829816949)
                    ·
                      refine ⟨3054217849627339390295339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32578323729358286829816949 3054217849627339390295339)
                      ·
                        rfl

theorem cell23_5948068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_5948068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948068 prefixEnd_5948068 := by exact prefixLift 5948068
  have htrace : WordTrace (prefixWord ++ tailWord_5948068) baseStart_5948068 baseEnd_5948068 := by
    simpa [prefixWord, tailWord_5948068, baseEnd_5948068] using wordTrace_append hprefix tailTrace_5948068
  have hstable : (prefixWord ++ tailWord_5948068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948068).length < 2 ^ (prefixWord ++ tailWord_5948068).sum := by decide
  have hdescent : baseEnd_5948068 < baseStart_5948068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948091 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_5948091 : Nat := 118140960795 + 5948091 * 2 ^ 59
def prefixEnd_5948091 : Nat := 4983230072969 + 3 ^ 40 * 5948091 * 2
def baseEnd_5948091 : Nat := 3054229659682392800307733

theorem tailTrace_5948091 : CollatzResearch.WordTrace tailWord_5948091 prefixEnd_5948091 3054229659682392800307733 := by
  unfold tailWord_5948091
  simp only [CollatzResearch.WordTrace]
  refine ⟨216944701494089634911716127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144629800996059756607810751 216944701494089634911716127)
  ·
    refine ⟨325417052241134452367574191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216944701494089634911716127 325417052241134452367574191)
    ·
      refine ⟨488125578361701678551361287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325417052241134452367574191 488125578361701678551361287)
      ·
        refine ⟨732188367542552517827041931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488125578361701678551361287 732188367542552517827041931)
        ·
          refine ⟨1098282551313828776740562897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732188367542552517827041931 1098282551313828776740562897)
          ·
            refine ⟨823711913485371582555422173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098282551313828776740562897 823711913485371582555422173)
            ·
              refine ⟨308891967557014343458283315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823711913485371582555422173 308891967557014343458283315)
              ·
                refine ⟨463337951335521515187424973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308891967557014343458283315 463337951335521515187424973)
                ·
                  refine ⟨173751731750820568195284365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463337951335521515187424973 173751731750820568195284365)
                  ·
                    refine ⟨65156899406557713073231637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173751731750820568195284365 65156899406557713073231637)
                    ·
                      refine ⟨3054229659682392800307733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65156899406557713073231637 3054229659682392800307733)
                      ·
                        rfl

theorem cell23_5948091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_5948091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948091 prefixEnd_5948091 := by exact prefixLift 5948091
  have htrace : WordTrace (prefixWord ++ tailWord_5948091) baseStart_5948091 baseEnd_5948091 := by
    simpa [prefixWord, tailWord_5948091, baseEnd_5948091] using wordTrace_append hprefix tailTrace_5948091
  have hstable : (prefixWord ++ tailWord_5948091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948091).length < 2 ^ (prefixWord ++ tailWord_5948091).sum := by decide
  have hdescent : baseEnd_5948091 < baseStart_5948091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948095 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_5948095 : Nat := 118140960795 + 5948095 * 2 ^ 59
def prefixEnd_5948095 : Nat := 4983230072969 + 3 ^ 40 * 5948095 * 2
def baseEnd_5948095 : Nat := 3054231713605010784657715

theorem tailTrace_5948095 : CollatzResearch.WordTrace tailWord_5948095 prefixEnd_5948095 3054231713605010784657715 := by
  unfold tailWord_5948095
  simp only [CollatzResearch.WordTrace]
  refine ⟨216944847386075143594861739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144629898257383429063241159 216944847386075143594861739)
  ·
    refine ⟨325417271079112715392292609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216944847386075143594861739 325417271079112715392292609)
    ·
      refine ⟨244062953309334536544219457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325417271079112715392292609 244062953309334536544219457)
      ·
        refine ⟨183047214982000902408164593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244062953309334536544219457 183047214982000902408164593)
        ·
          refine ⟨137285411236500676806123445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183047214982000902408164593 137285411236500676806123445)
          ·
            refine ⟨12870507303421938450574073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137285411236500676806123445 12870507303421938450574073)
            ·
              refine ⟨9652880477566453837930555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12870507303421938450574073 9652880477566453837930555)
              ·
                refine ⟨14479320716349680756895833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9652880477566453837930555 14479320716349680756895833)
                ·
                  refine ⟨10859490537262260567671875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14479320716349680756895833 10859490537262260567671875)
                  ·
                    refine ⟨16289235805893390851507813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10859490537262260567671875 16289235805893390851507813)
                    ·
                      refine ⟨3054231713605010784657715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16289235805893390851507813 3054231713605010784657715)
                      ·
                        rfl

theorem cell23_5948095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_5948095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948095 prefixEnd_5948095 := by exact prefixLift 5948095
  have htrace : WordTrace (prefixWord ++ tailWord_5948095) baseStart_5948095 baseEnd_5948095 := by
    simpa [prefixWord, tailWord_5948095, baseEnd_5948095] using wordTrace_append hprefix tailTrace_5948095
  have hstable : (prefixWord ++ tailWord_5948095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948095).length < 2 ^ (prefixWord ++ tailWord_5948095).sum := by decide
  have hdescent : baseEnd_5948095 < baseStart_5948095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948122 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_5948122 : Nat := 118140960795 + 5948122 * 2 ^ 59
def prefixEnd_5948122 : Nat := 4983230072969 + 3 ^ 40 * 5948122 * 2
def baseEnd_5948122 : Nat := 1018081859194227393006697

theorem tailTrace_5948122 : CollatzResearch.WordTrace tailWord_5948122 prefixEnd_5948122 1018081859194227393006697 := by
  unfold tailWord_5948122
  simp only [CollatzResearch.WordTrace]
  refine ⟨54236458039244331801523655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144630554771318218137396413 54236458039244331801523655)
  ·
    refine ⟨81354687058866497702285483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54236458039244331801523655 81354687058866497702285483)
    ·
      refine ⟨122032030588299746553428225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81354687058866497702285483 122032030588299746553428225)
      ·
        refine ⟨91524022941224809915071169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122032030588299746553428225 91524022941224809915071169)
        ·
          refine ⟨68643017205918607436303377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91524022941224809915071169 68643017205918607436303377)
          ·
            refine ⟨51482262904438955577227533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68643017205918607436303377 51482262904438955577227533)
            ·
              refine ⟨19305848589164608341460325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51482262904438955577227533 19305848589164608341460325)
              ·
                refine ⟨3619846610468364064023811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19305848589164608341460325 3619846610468364064023811)
                ·
                  refine ⟨5429769915702546096035717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619846610468364064023811 5429769915702546096035717)
                  ·
                    refine ⟨1018081859194227393006697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5429769915702546096035717 1018081859194227393006697)
                    ·
                      rfl

theorem cell23_5948122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_5948122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948122 prefixEnd_5948122 := by exact prefixLift 5948122
  have htrace : WordTrace (prefixWord ++ tailWord_5948122) baseStart_5948122 baseEnd_5948122 := by
    simpa [prefixWord, tailWord_5948122, baseEnd_5948122] using wordTrace_append hprefix tailTrace_5948122
  have hstable : (prefixWord ++ tailWord_5948122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948122).length < 2 ^ (prefixWord ++ tailWord_5948122).sum := by decide
  have hdescent : baseEnd_5948122 < baseStart_5948122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948128 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_5948128 : Nat := 118140960795 + 5948128 * 2 ^ 59
def prefixEnd_5948128 : Nat := 4983230072969 + 3 ^ 40 * 5948128 * 2
def baseEnd_5948128 : Nat := 3054248658466609155545063

theorem tailTrace_5948128 : CollatzResearch.WordTrace tailWord_5948128 prefixEnd_5948128 3054248658466609155545063 := by
  unfold tailWord_5948128
  simp only [CollatzResearch.WordTrace]
  refine ⟨108473025497477795115406519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144630700663303726820542025 108473025497477795115406519)
  ·
    refine ⟨162709538246216692673109779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108473025497477795115406519 162709538246216692673109779)
    ·
      refine ⟨244064307369325039009664669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162709538246216692673109779 244064307369325039009664669)
      ·
        refine ⟨91524115263496889628624251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244064307369325039009664669 91524115263496889628624251)
        ·
          refine ⟨137286172895245334442936377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91524115263496889628624251 137286172895245334442936377)
          ·
            refine ⟨102964629671434000832202283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137286172895245334442936377 102964629671434000832202283)
            ·
              refine ⟨154446944507151001248303425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102964629671434000832202283 154446944507151001248303425)
              ·
                refine ⟨115835208380363250936227569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154446944507151001248303425 115835208380363250936227569)
                ·
                  refine ⟨86876406285272438202170677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115835208380363250936227569 86876406285272438202170677)
                  ·
                    refine ⟨8144663089244291081453501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86876406285272438202170677 8144663089244291081453501)
                    ·
                      refine ⟨3054248658466609155545063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8144663089244291081453501 3054248658466609155545063)
                      ·
                        rfl

theorem cell23_5948128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_5948128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948128 prefixEnd_5948128 := by exact prefixLift 5948128
  have htrace : WordTrace (prefixWord ++ tailWord_5948128) baseStart_5948128 baseEnd_5948128 := by
    simpa [prefixWord, tailWord_5948128, baseEnd_5948128] using wordTrace_append hprefix tailTrace_5948128
  have hstable : (prefixWord ++ tailWord_5948128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948128).length < 2 ^ (prefixWord ++ tailWord_5948128).sum := by decide
  have hdescent : baseEnd_5948128 < baseStart_5948128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948230 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5948230 : Nat := 118140960795 + 5948230 * 2 ^ 59
def prefixEnd_5948230 : Nat := 4983230072969 + 3 ^ 40 * 5948230 * 2
def baseEnd_5948230 : Nat := 3054301033493367756469595

theorem tailTrace_5948230 : CollatzResearch.WordTrace tailWord_5948230 prefixEnd_5948230 3054301033493367756469595 := by
  unfold tailWord_5948230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779680351268314426594567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144633180827057374434017429 6779680351268314426594567)
  ·
    refine ⟨10169520526902471639891851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779680351268314426594567 10169520526902471639891851)
    ·
      refine ⟨15254280790353707459837777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169520526902471639891851 15254280790353707459837777)
      ·
        refine ⟨11440710592765280594878333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15254280790353707459837777 11440710592765280594878333)
        ·
          refine ⟨4290266472286980223079375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11440710592765280594878333 4290266472286980223079375)
          ·
            refine ⟨6435399708430470334619063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290266472286980223079375 6435399708430470334619063)
            ·
              refine ⟨9653099562645705501928595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435399708430470334619063 9653099562645705501928595)
              ·
                refine ⟨14479649343968558252892893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653099562645705501928595 14479649343968558252892893)
                ·
                  refine ⟨5429868503988209344834835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14479649343968558252892893 5429868503988209344834835)
                  ·
                    refine ⟨8144802755982314017252253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429868503988209344834835 8144802755982314017252253)
                    ·
                      refine ⟨3054301033493367756469595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8144802755982314017252253 3054301033493367756469595)
                      ·
                        rfl

theorem cell23_5948230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5948230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948230 prefixEnd_5948230 := by exact prefixLift 5948230
  have htrace : WordTrace (prefixWord ++ tailWord_5948230) baseStart_5948230 baseEnd_5948230 := by
    simpa [prefixWord, tailWord_5948230, baseEnd_5948230] using wordTrace_append hprefix tailTrace_5948230
  have hstable : (prefixWord ++ tailWord_5948230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948230).length < 2 ^ (prefixWord ++ tailWord_5948230).sum := by decide
  have hdescent : baseEnd_5948230 < baseStart_5948230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948236 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_5948236 : Nat := 118140960795 + 5948236 * 2 ^ 59
def prefixEnd_5948236 : Nat := 4983230072969 + 3 ^ 40 * 5948236 * 2
def baseEnd_5948236 : Nat := 3054304114377294732994567

theorem tailTrace_5948236 : CollatzResearch.WordTrace tailWord_5948236 prefixEnd_5948236 3054304114377294732994567 := by
  unfold tailWord_5948236
  simp only [CollatzResearch.WordTrace]
  refine ⟨108474995039282162337872281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144633326719042883117163041 108474995039282162337872281)
  ·
    refine ⟨81356246279461621753404211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108474995039282162337872281 81356246279461621753404211)
    ·
      refine ⟨122034369419192432630106317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81356246279461621753404211 122034369419192432630106317)
      ·
        refine ⟨45762888532197162236289869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122034369419192432630106317 45762888532197162236289869)
        ·
          refine ⟨17161083199573935838608701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45762888532197162236289869 17161083199573935838608701)
          ·
            refine ⟨6435406199840225939478263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17161083199573935838608701 6435406199840225939478263)
            ·
              refine ⟨9653109299760338909217395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435406199840225939478263 9653109299760338909217395)
              ·
                refine ⟨14479663949640508363826093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653109299760338909217395 14479663949640508363826093)
                ·
                  refine ⟨5429873981115190636434785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14479663949640508363826093 5429873981115190636434785)
                  ·
                    refine ⟨4072405485836392977326089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5429873981115190636434785 4072405485836392977326089)
                    ·
                      refine ⟨3054304114377294732994567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072405485836392977326089 3054304114377294732994567)
                      ·
                        rfl

theorem cell23_5948236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_5948236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948236 prefixEnd_5948236 := by exact prefixLift 5948236
  have htrace : WordTrace (prefixWord ++ tailWord_5948236) baseStart_5948236 baseEnd_5948236 := by
    simpa [prefixWord, tailWord_5948236, baseEnd_5948236] using wordTrace_append hprefix tailTrace_5948236
  have hstable : (prefixWord ++ tailWord_5948236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948236).length < 2 ^ (prefixWord ++ tailWord_5948236).sum := by decide
  have hdescent : baseEnd_5948236 < baseStart_5948236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948292 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_5948292 : Nat := 118140960795 + 5948292 * 2 ^ 59
def prefixEnd_5948292 : Nat := 4983230072969 + 3 ^ 40 * 5948292 * 2
def baseEnd_5948292 : Nat := 3054332869293946513894309

theorem tailTrace_5948292 : CollatzResearch.WordTrace tailWord_5948292 prefixEnd_5948292 3054332869293946513894309 := by
  unfold tailWord_5948292
  simp only [CollatzResearch.WordTrace]
  refine ⟨108476016283180723119891565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144634688377574297493188753 108476016283180723119891565)
  ·
    refine ⟨40678506106192771169959337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108476016283180723119891565 40678506106192771169959337)
    ·
      refine ⟨30508879579644578377469503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40678506106192771169959337 30508879579644578377469503)
      ·
        refine ⟨45763319369466867566204255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30508879579644578377469503 45763319369466867566204255)
        ·
          refine ⟨68644979054200301349306383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45763319369466867566204255 68644979054200301349306383)
          ·
            refine ⟨102967468581300452023959575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68644979054200301349306383 102967468581300452023959575)
            ·
              refine ⟨154451202871950678035939363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102967468581300452023959575 154451202871950678035939363)
              ·
                refine ⟨231676804307926017053909045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154451202871950678035939363 231676804307926017053909045)
                ·
                  refine ⟨21719700403868064098803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231676804307926017053909045 21719700403868064098803973)
                  ·
                    refine ⟨4072443825725262018525745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21719700403868064098803973 4072443825725262018525745)
                    ·
                      refine ⟨3054332869293946513894309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072443825725262018525745 3054332869293946513894309)
                      ·
                        rfl

theorem cell23_5948292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_5948292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948292 prefixEnd_5948292 := by exact prefixLift 5948292
  have htrace : WordTrace (prefixWord ++ tailWord_5948292) baseStart_5948292 baseEnd_5948292 := by
    simpa [prefixWord, tailWord_5948292, baseEnd_5948292] using wordTrace_append hprefix tailTrace_5948292
  have hstable : (prefixWord ++ tailWord_5948292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948292).length < 2 ^ (prefixWord ++ tailWord_5948292).sum := by decide
  have hdescent : baseEnd_5948292 < baseStart_5948292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948309 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_5948309 : Nat := 118140960795 + 5948309 * 2 ^ 59
def prefixEnd_5948309 : Nat := 4983230072969 + 3 ^ 40 * 5948309 * 2
def baseEnd_5948309 : Nat := 3054341598465072947381731

theorem tailTrace_5948309 : CollatzResearch.WordTrace tailWord_5948309 prefixEnd_5948309 3054341598465072947381731 := by
  unfold tailWord_5948309
  simp only [CollatzResearch.WordTrace]
  refine ⟨216952652607299858143151981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144635101738199905428767987 216952652607299858143151981)
  ·
    refine ⟨81357244727737446803681993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216952652607299858143151981 81357244727737446803681993)
    ·
      refine ⟨61017933545803085102761495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81357244727737446803681993 61017933545803085102761495)
      ·
        refine ⟨91526900318704627654142243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61017933545803085102761495 91526900318704627654142243)
        ·
          refine ⟨137290350478056941481213365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91526900318704627654142243 137290350478056941481213365)
          ·
            refine ⟨12870970357317838263863753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137290350478056941481213365 12870970357317838263863753)
            ·
              refine ⟨9653227767988378697897815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12870970357317838263863753 9653227767988378697897815)
              ·
                refine ⟨14479841651982568046846723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653227767988378697897815 14479841651982568046846723)
                ·
                  refine ⟨21719762477973852070270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14479841651982568046846723 21719762477973852070270085)
                  ·
                    refine ⟨4072455464620097263175641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21719762477973852070270085 4072455464620097263175641)
                    ·
                      refine ⟨3054341598465072947381731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072455464620097263175641 3054341598465072947381731)
                      ·
                        rfl

theorem cell23_5948309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_5948309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948309 prefixEnd_5948309 := by exact prefixLift 5948309
  have htrace : WordTrace (prefixWord ++ tailWord_5948309) baseStart_5948309 baseEnd_5948309 := by
    simpa [prefixWord, tailWord_5948309, baseEnd_5948309] using wordTrace_append hprefix tailTrace_5948309
  have hstable : (prefixWord ++ tailWord_5948309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948309).length < 2 ^ (prefixWord ++ tailWord_5948309).sum := by decide
  have hdescent : baseEnd_5948309 < baseStart_5948309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948385 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_5948385 : Nat := 118140960795 + 5948385 * 2 ^ 59
def prefixEnd_5948385 : Nat := 4983230072969 + 3 ^ 40 * 5948385 * 2
def baseEnd_5948385 : Nat := 3054380622994814650031381

theorem tailTrace_5948385 : CollatzResearch.WordTrace tailWord_5948385 prefixEnd_5948385 3054380622994814650031381 := by
  unfold tailWord_5948385
  simp only [CollatzResearch.WordTrace]
  refine ⟨216955424555024523122918609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144636949703349682081945739 216955424555024523122918609)
  ·
    refine ⟨162716568416268392342188957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216955424555024523122918609 162716568416268392342188957)
    ·
      refine ⟨61018713156100647128320859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162716568416268392342188957 61018713156100647128320859)
      ·
        refine ⟨91528069734150970692481289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61018713156100647128320859 91528069734150970692481289)
        ·
          refine ⟨68646052300613228019360967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91528069734150970692481289 68646052300613228019360967)
          ·
            refine ⟨102969078450919842029041451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68646052300613228019360967 102969078450919842029041451)
            ·
              refine ⟨154453617676379763043562177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102969078450919842029041451 154453617676379763043562177)
              ·
                refine ⟨115840213257284822282671633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154453617676379763043562177 115840213257284822282671633)
                ·
                  refine ⟨86880159942963616712003725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115840213257284822282671633 86880159942963616712003725)
                  ·
                    refine ⟨32580059978611356267001397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86880159942963616712003725 32580059978611356267001397)
                    ·
                      refine ⟨3054380622994814650031381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32580059978611356267001397 3054380622994814650031381)
                      ·
                        rfl

theorem cell23_5948385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_5948385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948385 prefixEnd_5948385 := by exact prefixLift 5948385
  have htrace : WordTrace (prefixWord ++ tailWord_5948385) baseStart_5948385 baseEnd_5948385 := by
    simpa [prefixWord, tailWord_5948385, baseEnd_5948385] using wordTrace_append hprefix tailTrace_5948385
  have hstable : (prefixWord ++ tailWord_5948385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948385).length < 2 ^ (prefixWord ++ tailWord_5948385).sum := by decide
  have hdescent : baseEnd_5948385 < baseStart_5948385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948392 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_5948392 : Nat := 118140960795 + 5948392 * 2 ^ 59
def prefixEnd_5948392 : Nat := 4983230072969 + 3 ^ 40 * 5948392 * 2
def baseEnd_5948392 : Nat := 1018128072453132040881283

theorem tailTrace_5948392 : CollatzResearch.WordTrace tailWord_5948392 prefixEnd_5948392 1018128072453132040881283 := by
  unfold tailWord_5948392
  simp only [CollatzResearch.WordTrace]
  refine ⟨108477839932999581659211715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144637119910666108878948953 108477839932999581659211715)
  ·
    refine ⟨162716759899499372488817573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108477839932999581659211715 162716759899499372488817573)
    ·
      refine ⟨30509392481156132341653295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162716759899499372488817573 30509392481156132341653295)
      ·
        refine ⟨45764088721734198512479943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30509392481156132341653295 45764088721734198512479943)
        ·
          refine ⟨68646133082601297768719915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45764088721734198512479943 68646133082601297768719915)
          ·
            refine ⟨102969199623901946653079873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68646133082601297768719915 102969199623901946653079873)
            ·
              refine ⟨77226899717926459989809905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102969199623901946653079873 77226899717926459989809905)
              ·
                refine ⟨57920174788444844992357429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77226899717926459989809905 57920174788444844992357429)
                ·
                  refine ⟨5430016386416704218033509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57920174788444844992357429 5430016386416704218033509)
                  ·
                    refine ⟨1018128072453132040881283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430016386416704218033509 1018128072453132040881283)
                    ·
                      rfl

theorem cell23_5948392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_5948392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948392 prefixEnd_5948392 := by exact prefixLift 5948392
  have htrace : WordTrace (prefixWord ++ tailWord_5948392) baseStart_5948392 baseEnd_5948392 := by
    simpa [prefixWord, tailWord_5948392, baseEnd_5948392] using wordTrace_append hprefix tailTrace_5948392
  have hstable : (prefixWord ++ tailWord_5948392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948392).length < 2 ^ (prefixWord ++ tailWord_5948392).sum := by decide
  have hdescent : baseEnd_5948392 < baseStart_5948392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948425 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_5948425 : Nat := 118140960795 + 5948425 * 2 ^ 59
def prefixEnd_5948425 : Nat := 4983230072969 + 3 ^ 40 * 5948425 * 2
def baseEnd_5948425 : Nat := 3054401162220994493531197

theorem tailTrace_5948425 : CollatzResearch.WordTrace tailWord_5948425 prefixEnd_5948425 3054401162220994493531197 := by
  unfold tailWord_5948425
  simp only [CollatzResearch.WordTrace]
  refine ⟨216956883474879609954374729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144637922316586406636249819 216956883474879609954374729)
  ·
    refine ⟨162717662606159707465781047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216956883474879609954374729 162717662606159707465781047)
    ·
      refine ⟨244076493909239561198671571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162717662606159707465781047 244076493909239561198671571)
      ·
        refine ⟨366114740863859341798007357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244076493909239561198671571 366114740863859341798007357)
        ·
          refine ⟨137293027823947253174252759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366114740863859341798007357 137293027823947253174252759)
          ·
            refine ⟨205939541735920879761379139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137293027823947253174252759 205939541735920879761379139)
            ·
              refine ⟨308909312603881319642068709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205939541735920879761379139 308909312603881319642068709)
              ·
                refine ⟨57920496113227747432887883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308909312603881319642068709 57920496113227747432887883)
                ·
                  refine ⟨86880744169841621149331825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57920496113227747432887883 86880744169841621149331825)
                  ·
                    refine ⟨65160558127381215861998869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86880744169841621149331825 65160558127381215861998869)
                    ·
                      refine ⟨3054401162220994493531197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65160558127381215861998869 3054401162220994493531197)
                      ·
                        rfl

theorem cell23_5948425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_5948425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948425 prefixEnd_5948425 := by exact prefixLift 5948425
  have htrace : WordTrace (prefixWord ++ tailWord_5948425) baseStart_5948425 baseEnd_5948425 := by
    simpa [prefixWord, tailWord_5948425, baseEnd_5948425] using wordTrace_append hprefix tailTrace_5948425
  have hstable : (prefixWord ++ tailWord_5948425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948425).length < 2 ^ (prefixWord ++ tailWord_5948425).sum := by decide
  have hdescent : baseEnd_5948425 < baseStart_5948425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948459 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 2, 3, 2]
def baseStart_5948459 : Nat := 118140960795 + 5948459 * 2 ^ 59
def prefixEnd_5948459 : Nat := 4983230072969 + 3 ^ 40 * 5948459 * 2
def baseEnd_5948459 : Nat := 3054418620563247360506041

theorem tailTrace_5948459 : CollatzResearch.WordTrace tailWord_5948459 prefixEnd_5948459 3054418620563247360506041 := by
  unfold tailWord_5948459
  simp only [CollatzResearch.WordTrace]
  refine ⟨216958123556756433761112431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144638749037837622507408287 216958123556756433761112431)
  ·
    refine ⟨325437185335134650641668647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216958123556756433761112431 325437185335134650641668647)
    ·
      refine ⟨488155778002701975962502971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325437185335134650641668647 488155778002701975962502971)
      ·
        refine ⟨732233667004052963943754457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488155778002701975962502971 732233667004052963943754457)
        ·
          refine ⟨549175250253039722957815843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732233667004052963943754457 549175250253039722957815843)
          ·
            refine ⟨823762875379559584436723765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549175250253039722957815843 823762875379559584436723765)
            ·
              refine ⟨77227769566833711040942853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 823762875379559584436723765 77227769566833711040942853)
              ·
                refine ⟨14480206793781320820176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77227769566833711040942853 14480206793781320820176785)
                ·
                  refine ⟨10860155095335990615132589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14480206793781320820176785 10860155095335990615132589)
                  ·
                    refine ⟨4072558160750996480674721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10860155095335990615132589 4072558160750996480674721)
                    ·
                      refine ⟨3054418620563247360506041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072558160750996480674721 3054418620563247360506041)
                      ·
                        rfl

theorem cell23_5948459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3, 2].length) (baseStart_5948459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948459 prefixEnd_5948459 := by exact prefixLift 5948459
  have htrace : WordTrace (prefixWord ++ tailWord_5948459) baseStart_5948459 baseEnd_5948459 := by
    simpa [prefixWord, tailWord_5948459, baseEnd_5948459] using wordTrace_append hprefix tailTrace_5948459
  have hstable : (prefixWord ++ tailWord_5948459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948459).length < 2 ^ (prefixWord ++ tailWord_5948459).sum := by decide
  have hdescent : baseEnd_5948459 < baseStart_5948459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948486 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5948486 : Nat := 118140960795 + 5948486 * 2 ^ 59
def prefixEnd_5948486 : Nat := 4983230072969 + 3 ^ 40 * 5948486 * 2
def baseEnd_5948486 : Nat := 1018144161513639584956139

theorem tailTrace_5948486 : CollatzResearch.WordTrace tailWord_5948486 prefixEnd_5948486 1018144161513639584956139 := by
  unfold tailWord_5948486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779972135239331792885791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144639405551772411581563541 6779972135239331792885791)
  ·
    refine ⟨10169958202858997689328687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779972135239331792885791 10169958202858997689328687)
    ·
      refine ⟨15254937304288496533993031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169958202858997689328687 15254937304288496533993031)
      ·
        refine ⟨22882405956432744800989547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254937304288496533993031 22882405956432744800989547)
        ·
          refine ⟨34323608934649117201484321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22882405956432744800989547 34323608934649117201484321)
          ·
            refine ⟨25742706700986837901113241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34323608934649117201484321 25742706700986837901113241)
            ·
              refine ⟨19307030025740128425834931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25742706700986837901113241 19307030025740128425834931)
              ·
                refine ⟨28960545038610192638752397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19307030025740128425834931 28960545038610192638752397)
                ·
                  refine ⟨10860204389478822239532149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28960545038610192638752397 10860204389478822239532149)
                  ·
                    refine ⟨1018144161513639584956139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10860204389478822239532149 1018144161513639584956139)
                    ·
                      rfl

theorem cell23_5948486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5948486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948486 prefixEnd_5948486 := by exact prefixLift 5948486
  have htrace : WordTrace (prefixWord ++ tailWord_5948486) baseStart_5948486 baseEnd_5948486 := by
    simpa [prefixWord, tailWord_5948486, baseEnd_5948486] using wordTrace_append hprefix tailTrace_5948486
  have hstable : (prefixWord ++ tailWord_5948486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948486).length < 2 ^ (prefixWord ++ tailWord_5948486).sum := by decide
  have hdescent : baseEnd_5948486 < baseStart_5948486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948493 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_5948493 : Nat := 118140960795 + 5948493 * 2 ^ 59
def prefixEnd_5948493 : Nat := 4983230072969 + 3 ^ 40 * 5948493 * 2
def baseEnd_5948493 : Nat := 3054436078905500227480885

theorem tailTrace_5948493 : CollatzResearch.WordTrace tailWord_5948493 prefixEnd_5948493 3054436078905500227480885 := by
  unfold tailWord_5948493
  simp only [CollatzResearch.WordTrace]
  refine ⟨216959363638633257567850133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144639575759088838378566755 216959363638633257567850133)
  ·
    refine ⟨10169970170560933948492975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216959363638633257567850133 10169970170560933948492975)
    ·
      refine ⟨15254955255841400922739463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169970170560933948492975 15254955255841400922739463)
      ·
        refine ⟨22882432883762101384109195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254955255841400922739463 22882432883762101384109195)
        ·
          refine ⟨34323649325643152076163793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22882432883762101384109195 34323649325643152076163793)
          ·
            refine ⟨25742736994232364057122845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34323649325643152076163793 25742736994232364057122845)
            ·
              refine ⟨9653526372837136521421067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25742736994232364057122845 9653526372837136521421067)
              ·
                refine ⟨14480289559255704782131601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653526372837136521421067 14480289559255704782131601)
                ·
                  refine ⟨10860217169441778586598701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14480289559255704782131601 10860217169441778586598701)
                  ·
                    refine ⟨4072581438540666969974513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10860217169441778586598701 4072581438540666969974513)
                    ·
                      refine ⟨3054436078905500227480885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072581438540666969974513 3054436078905500227480885)
                      ·
                        rfl

theorem cell23_5948493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_5948493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948493 prefixEnd_5948493 := by exact prefixLift 5948493
  have htrace : WordTrace (prefixWord ++ tailWord_5948493) baseStart_5948493 baseEnd_5948493 := by
    simpa [prefixWord, tailWord_5948493, baseEnd_5948493] using wordTrace_append hprefix tailTrace_5948493
  have hstable : (prefixWord ++ tailWord_5948493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948493).length < 2 ^ (prefixWord ++ tailWord_5948493).sum := by decide
  have hdescent : baseEnd_5948493 < baseStart_5948493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948533 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5948533 : Nat := 118140960795 + 5948533 * 2 ^ 59
def prefixEnd_5948533 : Nat := 4983230072969 + 3 ^ 40 * 5948533 * 2
def baseEnd_5948533 : Nat := 1018152206043893356993567

theorem tailTrace_5948533 : CollatzResearch.WordTrace tailWord_5948533 prefixEnd_5948533 1018152206043893356993567 := by
  unfold tailWord_5948533
  simp only [CollatzResearch.WordTrace]
  refine ⟨216960822558488344399306253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144640548372325562932870835 216960822558488344399306253)
  ·
    refine ⟨81360308459433129149739845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216960822558488344399306253 81360308459433129149739845)
    ·
      refine ⟨15255057836143711715576221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81360308459433129149739845 15255057836143711715576221)
      ·
        refine ⟨5720646688553891893341083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15255057836143711715576221 5720646688553891893341083)
        ·
          refine ⟨8580970032830837840011625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720646688553891893341083 8580970032830837840011625)
          ·
            refine ⟨6435727524623128380008719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8580970032830837840011625 6435727524623128380008719)
            ·
              refine ⟨9653591286934692570013079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435727524623128380008719 9653591286934692570013079)
              ·
                refine ⟨14480386930402038855019619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653591286934692570013079 14480386930402038855019619)
                ·
                  refine ⟨21720580395603058282529429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14480386930402038855019619 21720580395603058282529429)
                  ·
                    refine ⟨1018152206043893356993567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21720580395603058282529429 1018152206043893356993567)
                    ·
                      rfl

theorem cell23_5948533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5948533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948533 prefixEnd_5948533 := by exact prefixLift 5948533
  have htrace : WordTrace (prefixWord ++ tailWord_5948533) baseStart_5948533 baseEnd_5948533 := by
    simpa [prefixWord, tailWord_5948533, baseEnd_5948533] using wordTrace_append hprefix tailTrace_5948533
  have hstable : (prefixWord ++ tailWord_5948533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948533).length < 2 ^ (prefixWord ++ tailWord_5948533).sum := by decide
  have hdescent : baseEnd_5948533 < baseStart_5948533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948574 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5948574 : Nat := 118140960795 + 5948574 * 2 ^ 59
def prefixEnd_5948574 : Nat := 4983230072969 + 3 ^ 40 * 5948574 * 2
def baseEnd_5948574 : Nat := 3054477670838514410568013

theorem tailTrace_5948574 : CollatzResearch.WordTrace tailWord_5948574 prefixEnd_5948574 3054477670838514410568013 := by
  unfold tailWord_5948574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27120289743917476050193597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144641545300893205601032517 27120289743917476050193597)
  ·
    refine ⟨10170108653969053518822599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27120289743917476050193597 10170108653969053518822599)
    ·
      refine ⟨15255162980953580278233899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10170108653969053518822599 15255162980953580278233899)
      ·
        refine ⟨22882744471430370417350849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15255162980953580278233899 22882744471430370417350849)
        ·
          refine ⟨17162058353572777813013137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22882744471430370417350849 17162058353572777813013137)
          ·
            refine ⟨12871543765179583359759853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17162058353572777813013137 12871543765179583359759853)
            ·
              refine ⟨4826828911942343759909945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12871543765179583359759853 4826828911942343759909945)
              ·
                refine ⟨3620121683956757819932459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826828911942343759909945 3620121683956757819932459)
                ·
                  refine ⟨5430182525935136729898689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620121683956757819932459 5430182525935136729898689)
                  ·
                    refine ⟨4072636894451352547424017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5430182525935136729898689 4072636894451352547424017)
                    ·
                      refine ⟨3054477670838514410568013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072636894451352547424017 3054477670838514410568013)
                      ·
                        rfl

theorem cell23_5948574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5948574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948574 prefixEnd_5948574 := by exact prefixLift 5948574
  have htrace : WordTrace (prefixWord ++ tailWord_5948574) baseStart_5948574 baseEnd_5948574 := by
    simpa [prefixWord, tailWord_5948574, baseEnd_5948574] using wordTrace_append hprefix tailTrace_5948574
  have hstable : (prefixWord ++ tailWord_5948574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948574).length < 2 ^ (prefixWord ++ tailWord_5948574).sum := by decide
  have hdescent : baseEnd_5948574 < baseStart_5948574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948602 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_5948602 : Nat := 118140960795 + 5948602 * 2 ^ 59
def prefixEnd_5948602 : Nat := 4983230072969 + 3 ^ 40 * 5948602 * 2
def baseEnd_5948602 : Nat := 339388005366315589001987

theorem tailTrace_5948602 : CollatzResearch.WordTrace tailWord_5948602 prefixEnd_5948602 339388005366315589001987 := by
  unfold tailWord_5948602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54240834798809592295892015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144642226130158912789045373 54240834798809592295892015)
  ·
    refine ⟨81361252198214388443838023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54240834798809592295892015 81361252198214388443838023)
    ·
      refine ⟨122041878297321582665757035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81361252198214388443838023 122041878297321582665757035)
      ·
        refine ⟨183062817445982373998635553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122041878297321582665757035 183062817445982373998635553)
        ·
          refine ⟨137297113084486780498976665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183062817445982373998635553 137297113084486780498976665)
          ·
            refine ⟨102972834813365085374232499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137297113084486780498976665 102972834813365085374232499)
            ·
              refine ⟨154459252220047628061348749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102972834813365085374232499 154459252220047628061348749)
              ·
                refine ⟨57922219582517860523005781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154459252220047628061348749 57922219582517860523005781)
                ·
                  refine ⟨339388005366315589001987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57922219582517860523005781 339388005366315589001987)
                  ·
                    rfl

theorem cell23_5948602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_5948602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948602 prefixEnd_5948602 := by exact prefixLift 5948602
  have htrace : WordTrace (prefixWord ++ tailWord_5948602) baseStart_5948602 baseEnd_5948602 := by
    simpa [prefixWord, tailWord_5948602, baseEnd_5948602] using wordTrace_append hprefix tailTrace_5948602
  have hstable : (prefixWord ++ tailWord_5948602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948602).length < 2 ^ (prefixWord ++ tailWord_5948602).sum := by decide
  have hdescent : baseEnd_5948602 < baseStart_5948602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948696 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_5948696 : Nat := 118140960795 + 5948696 * 2 ^ 59
def prefixEnd_5948696 : Nat := 4983230072969 + 3 ^ 40 * 5948696 * 2
def baseEnd_5948696 : Nat := 1018180105159454311080817

theorem tailTrace_5948696 : CollatzResearch.WordTrace tailWord_5948696 prefixEnd_5948696 1018180105159454311080817 := by
  unfold tailWord_5948696
  simp only [CollatzResearch.WordTrace]
  refine ⟨108483383828448911618744971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144644511771265215491659961 108483383828448911618744971)
  ·
    refine ⟨162725075742673367428117457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108483383828448911618744971 162725075742673367428117457)
    ·
      refine ⟨122043806807005025571088093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162725075742673367428117457 122043806807005025571088093)
      ·
        refine ⟨45766427552626884589158035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122043806807005025571088093 45766427552626884589158035)
        ·
          refine ⟨68649641328940326883737053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45766427552626884589158035 68649641328940326883737053)
          ·
            refine ⟨25743615498352622581401395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68649641328940326883737053 25743615498352622581401395)
            ·
              refine ⟨38615423247528933872102093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25743615498352622581401395 38615423247528933872102093)
              ·
                refine ⟨14480783717823350202038285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38615423247528933872102093 14480783717823350202038285)
                ·
                  refine ⟨5430293894183756325764357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14480783717823350202038285 5430293894183756325764357)
                  ·
                    refine ⟨1018180105159454311080817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430293894183756325764357 1018180105159454311080817)
                    ·
                      rfl

theorem cell23_5948696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_5948696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948696 prefixEnd_5948696 := by exact prefixLift 5948696
  have htrace : WordTrace (prefixWord ++ tailWord_5948696) baseStart_5948696 baseEnd_5948696 := by
    simpa [prefixWord, tailWord_5948696, baseEnd_5948696] using wordTrace_append hprefix tailTrace_5948696
  have hstable : (prefixWord ++ tailWord_5948696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948696).length < 2 ^ (prefixWord ++ tailWord_5948696).sum := by decide
  have hdescent : baseEnd_5948696 < baseStart_5948696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948719 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_5948719 : Nat := 118140960795 + 5948719 * 2 ^ 59
def prefixEnd_5948719 : Nat := 4983230072969 + 3 ^ 40 * 5948719 * 2
def baseEnd_5948719 : Nat := 3054552125533416343254845

theorem tailTrace_5948719 : CollatzResearch.WordTrace tailWord_5948719 prefixEnd_5948719 3054552125533416343254845 := by
  unfold tailWord_5948719
  simp only [CollatzResearch.WordTrace]
  refine ⟨216967606535814498165577211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144645071023876332110384807 216967606535814498165577211)
  ·
    refine ⟨325451409803721747248365817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216967606535814498165577211 325451409803721747248365817)
    ·
      refine ⟨244088557352791310436274363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325451409803721747248365817 244088557352791310436274363)
      ·
        refine ⟨366132836029186965654411545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244088557352791310436274363 366132836029186965654411545)
        ·
          refine ⟨274599627021890224240808659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366132836029186965654411545 274599627021890224240808659)
          ·
            refine ⟨411899440532835336361212989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274599627021890224240808659 411899440532835336361212989)
            ·
              refine ⟨154462290199813251135454871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411899440532835336361212989 154462290199813251135454871)
              ·
                refine ⟨231693435299719876703182307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154462290199813251135454871 231693435299719876703182307)
                ·
                  refine ⟨347540152949579815054773461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231693435299719876703182307 347540152949579815054773461)
                  ·
                    refine ⟨8145472334755776915346253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 347540152949579815054773461 8145472334755776915346253)
                    ·
                      refine ⟨3054552125533416343254845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8145472334755776915346253 3054552125533416343254845)
                      ·
                        rfl

theorem cell23_5948719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_5948719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948719 prefixEnd_5948719 := by exact prefixLift 5948719
  have htrace : WordTrace (prefixWord ++ tailWord_5948719) baseStart_5948719 baseEnd_5948719 := by
    simpa [prefixWord, tailWord_5948719, baseEnd_5948719] using wordTrace_append hprefix tailTrace_5948719
  have hstable : (prefixWord ++ tailWord_5948719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948719).length < 2 ^ (prefixWord ++ tailWord_5948719).sum := by decide
  have hdescent : baseEnd_5948719 < baseStart_5948719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948739 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 5, 5]
def baseStart_5948739 : Nat := 118140960795 + 5948739 * 2 ^ 59
def prefixEnd_5948739 : Nat := 4983230072969 + 3 ^ 40 * 5948739 * 2
def baseEnd_5948739 : Nat := 1018187465048835421668251

theorem tailTrace_5948739 : CollatzResearch.WordTrace tailWord_5948739 prefixEnd_5948739 1018187465048835421668251 := by
  unfold tailWord_5948739
  simp only [CollatzResearch.WordTrace]
  refine ⟨216968335995742041581305271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144645557330494694387536847 216968335995742041581305271)
  ·
    refine ⟨325452503993613062371957907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216968335995742041581305271 325452503993613062371957907)
    ·
      refine ⟨488178755990419593557936861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325452503993613062371957907 488178755990419593557936861)
      ·
        refine ⟨183067033496407347584226323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488178755990419593557936861 183067033496407347584226323)
        ·
          refine ⟨274600550244611021376339485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183067033496407347584226323 274600550244611021376339485)
          ·
            refine ⟨102975206341729133016127307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274600550244611021376339485 102975206341729133016127307)
            ·
              refine ⟨154462809512593699524190961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102975206341729133016127307 154462809512593699524190961)
              ·
                refine ⟨115847107134445274643143221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154462809512593699524190961 115847107134445274643143221)
                ·
                  refine ⟨10860666293854244497794677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115847107134445274643143221 10860666293854244497794677)
                  ·
                    refine ⟨1018187465048835421668251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10860666293854244497794677 1018187465048835421668251)
                    ·
                      rfl

theorem cell23_5948739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 5].length) (baseStart_5948739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948739 prefixEnd_5948739 := by exact prefixLift 5948739
  have htrace : WordTrace (prefixWord ++ tailWord_5948739) baseStart_5948739 baseEnd_5948739 := by
    simpa [prefixWord, tailWord_5948739, baseEnd_5948739] using wordTrace_append hprefix tailTrace_5948739
  have hstable : (prefixWord ++ tailWord_5948739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948739).length < 2 ^ (prefixWord ++ tailWord_5948739).sum := by decide
  have hdescent : baseEnd_5948739 < baseStart_5948739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948740 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5948740 : Nat := 118140960795 + 5948740 * 2 ^ 59
def prefixEnd_5948740 : Nat := 4983230072969 + 3 ^ 40 * 5948740 * 2
def baseEnd_5948740 : Nat := 3054562908627160761092249

theorem tailTrace_5948740 : CollatzResearch.WordTrace tailWord_5948740 prefixEnd_5948740 3054562908627160761092249 := by
  unfold tailWord_5948740
  simp only [CollatzResearch.WordTrace]
  refine ⟨108484186234369209376045837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144645581645825612501394449 108484186234369209376045837)
  ·
    refine ⟨40681569837888453516017189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108484186234369209376045837 40681569837888453516017189)
    ·
      refine ⟨7627794344604085034253223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40681569837888453516017189 7627794344604085034253223)
      ·
        refine ⟨11441691516906127551379835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627794344604085034253223 11441691516906127551379835)
        ·
          refine ⟨17162537275359191327069753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11441691516906127551379835 17162537275359191327069753)
          ·
            refine ⟨12871902956519393495302315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17162537275359191327069753 12871902956519393495302315)
            ·
              refine ⟨19307854434779090242953473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12871902956519393495302315 19307854434779090242953473)
              ·
                refine ⟨14480890826084317682215105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19307854434779090242953473 14480890826084317682215105)
                ·
                  refine ⟨10860668119563238261661329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14480890826084317682215105 10860668119563238261661329)
                  ·
                    refine ⟨8145501089672428696245997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10860668119563238261661329 8145501089672428696245997)
                    ·
                      refine ⟨3054562908627160761092249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8145501089672428696245997 3054562908627160761092249)
                      ·
                        rfl

theorem cell23_5948740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5948740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948740 prefixEnd_5948740 := by exact prefixLift 5948740
  have htrace : WordTrace (prefixWord ++ tailWord_5948740) baseStart_5948740 baseEnd_5948740 := by
    simpa [prefixWord, tailWord_5948740, baseEnd_5948740] using wordTrace_append hprefix tailTrace_5948740
  have hstable : (prefixWord ++ tailWord_5948740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948740).length < 2 ^ (prefixWord ++ tailWord_5948740).sum := by decide
  have hdescent : baseEnd_5948740 < baseStart_5948740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948756 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_5948756 : Nat := 118140960795 + 5948756 * 2 ^ 59
def prefixEnd_5948756 : Nat := 4983230072969 + 3 ^ 40 * 5948756 * 2
def baseEnd_5948756 : Nat := 1018190374772544232830725

theorem tailTrace_5948756 : CollatzResearch.WordTrace tailWord_5948756 prefixEnd_5948756 1018190374772544232830725 := by
  unfold tailWord_5948756
  simp only [CollatzResearch.WordTrace]
  refine ⟨108484478018340226742337061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144645970691120302323116081 108484478018340226742337061)
  ·
    refine ⟨20340839628438792514188199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108484478018340226742337061 20340839628438792514188199)
    ·
      refine ⟨30511259442658188771282299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20340839628438792514188199 30511259442658188771282299)
      ·
        refine ⟨45766889163987283156923449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30511259442658188771282299 45766889163987283156923449)
        ·
          refine ⟨34325166872990462367692587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45766889163987283156923449 34325166872990462367692587)
          ·
            refine ⟨51487750309485693551538881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34325166872990462367692587 51487750309485693551538881)
            ·
              refine ⟨38615812732114270163654161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51487750309485693551538881 38615812732114270163654161)
              ·
                refine ⟨28961859549085702622740621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38615812732114270163654161 28961859549085702622740621)
                ·
                  refine ⟨10860697330907138483527733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28961859549085702622740621 10860697330907138483527733)
                  ·
                    refine ⟨1018190374772544232830725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10860697330907138483527733 1018190374772544232830725)
                    ·
                      rfl

theorem cell23_5948756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_5948756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948756 prefixEnd_5948756 := by exact prefixLift 5948756
  have htrace : WordTrace (prefixWord ++ tailWord_5948756) baseStart_5948756 baseEnd_5948756 := by
    simpa [prefixWord, tailWord_5948756, baseEnd_5948756] using wordTrace_append hprefix tailTrace_5948756
  have hstable : (prefixWord ++ tailWord_5948756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948756).length < 2 ^ (prefixWord ++ tailWord_5948756).sum := by decide
  have hdescent : baseEnd_5948756 < baseStart_5948756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948769 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_5948769 : Nat := 118140960795 + 5948769 * 2 ^ 59
def prefixEnd_5948769 : Nat := 4983230072969 + 3 ^ 40 * 5948769 * 2
def baseEnd_5948769 : Nat := 1018192599855380382543205

theorem tailTrace_5948769 : CollatzResearch.WordTrace tailWord_5948769 prefixEnd_5948769 1018192599855380382543205 := by
  unfold tailWord_5948769
  simp only [CollatzResearch.WordTrace]
  refine ⟨216969430185633356704897361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144646286790422237803264907 216969430185633356704897361)
  ·
    refine ⟨162727072639225017528673021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216969430185633356704897361 162727072639225017528673021)
    ·
      refine ⟨61022652239709381573252383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162727072639225017528673021 61022652239709381573252383)
      ·
        refine ⟨91533978359564072359878575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61022652239709381573252383 91533978359564072359878575)
        ·
          refine ⟨137300967539346108539817863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91533978359564072359878575 137300967539346108539817863)
          ·
            refine ⟨205951451309019162809726795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137300967539346108539817863 205951451309019162809726795)
            ·
              refine ⟨308927176963528744214590193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205951451309019162809726795 308927176963528744214590193)
              ·
                refine ⟨231695382722646558160942645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308927176963528744214590193 231695382722646558160942645)
                ·
                  refine ⟨21721442130248114827588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231695382722646558160942645 21721442130248114827588373)
                  ·
                    refine ⟨1018192599855380382543205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21721442130248114827588373 1018192599855380382543205)
                    ·
                      rfl

theorem cell23_5948769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_5948769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948769 prefixEnd_5948769 := by exact prefixLift 5948769
  have htrace : WordTrace (prefixWord ++ tailWord_5948769) baseStart_5948769 baseEnd_5948769 := by
    simpa [prefixWord, tailWord_5948769, baseEnd_5948769] using wordTrace_append hprefix tailTrace_5948769
  have hstable : (prefixWord ++ tailWord_5948769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948769).length < 2 ^ (prefixWord ++ tailWord_5948769).sum := by decide
  have hdescent : baseEnd_5948769 < baseStart_5948769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948780 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_5948780 : Nat := 118140960795 + 5948780 * 2 ^ 59
def prefixEnd_5948780 : Nat := 4983230072969 + 3 ^ 40 * 5948780 * 2
def baseEnd_5948780 : Nat := 3054583447853340604592065

theorem tailTrace_5948780 : CollatzResearch.WordTrace tailWord_5948780 prefixEnd_5948780 3054583447853340604592065 := by
  unfold tailWord_5948780
  simp only [CollatzResearch.WordTrace]
  refine ⟨108484915694296752791773897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144646554259062337055698529 108484915694296752791773897)
  ·
    refine ⟨81363686770722564593830423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108484915694296752791773897 81363686770722564593830423)
    ·
      refine ⟨122045530156083846890745635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81363686770722564593830423 122045530156083846890745635)
      ·
        refine ⟨183068295234125770336118453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122045530156083846890745635 183068295234125770336118453)
        ·
          refine ⟨17162652678199290969011105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183068295234125770336118453 17162652678199290969011105)
          ·
            refine ⟨12871989508649468226758329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17162652678199290969011105 12871989508649468226758329)
            ·
              refine ⟨9653992131487101170068747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12871989508649468226758329 9653992131487101170068747)
              ·
                refine ⟨14480988197230651755103121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653992131487101170068747 14480988197230651755103121)
                ·
                  refine ⟨10860741147922988816327341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14480988197230651755103121 10860741147922988816327341)
                  ·
                    refine ⟨4072777930471120806122753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10860741147922988816327341 4072777930471120806122753)
                    ·
                      refine ⟨3054583447853340604592065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072777930471120806122753 3054583447853340604592065)
                      ·
                        rfl

theorem cell23_5948780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_5948780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948780 prefixEnd_5948780 := by exact prefixLift 5948780
  have htrace : WordTrace (prefixWord ++ tailWord_5948780) baseStart_5948780 baseEnd_5948780 := by
    simpa [prefixWord, tailWord_5948780, baseEnd_5948780] using wordTrace_append hprefix tailTrace_5948780
  have hstable : (prefixWord ++ tailWord_5948780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948780).length < 2 ^ (prefixWord ++ tailWord_5948780).sum := by decide
  have hdescent : baseEnd_5948780 < baseStart_5948780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948786 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_5948786 : Nat := 118140960795 + 5948786 * 2 ^ 59
def prefixEnd_5948786 : Nat := 4983230072969 + 3 ^ 40 * 5948786 * 2
def baseEnd_5948786 : Nat := 1018195509579089193705679

theorem tailTrace_5948786 : CollatzResearch.WordTrace tailWord_5948786 prefixEnd_5948786 1018195509579089193705679 := by
  unfold tailWord_5948786
  simp only [CollatzResearch.WordTrace]
  refine ⟨54242512556642942152066553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144646700151047845738844141 54242512556642942152066553)
  ·
    refine ⟨40681884417482206614049915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54242512556642942152066553 40681884417482206614049915)
    ·
      refine ⟨61022826626223309921074873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40681884417482206614049915 61022826626223309921074873)
      ·
        refine ⟨45767119969667482440806155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61022826626223309921074873 45767119969667482440806155)
        ·
          refine ⟨68650679954501223661209233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45767119969667482440806155 68650679954501223661209233)
          ·
            refine ⟨51488009965875917745906925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68650679954501223661209233 51488009965875917745906925)
            ·
              refine ⟨19308003737203469154715097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51488009965875917745906925 19308003737203469154715097)
              ·
                refine ⟨14481002802902601866036323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19308003737203469154715097 14481002802902601866036323)
                ·
                  refine ⟨21721504204353902799054485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14481002802902601866036323 21721504204353902799054485)
                  ·
                    refine ⟨1018195509579089193705679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21721504204353902799054485 1018195509579089193705679)
                    ·
                      rfl

theorem cell23_5948786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_5948786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948786 prefixEnd_5948786 := by exact prefixLift 5948786
  have htrace : WordTrace (prefixWord ++ tailWord_5948786) baseStart_5948786 baseEnd_5948786 := by
    simpa [prefixWord, tailWord_5948786, baseEnd_5948786] using wordTrace_append hprefix tailTrace_5948786
  have hstable : (prefixWord ++ tailWord_5948786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948786).length < 2 ^ (prefixWord ++ tailWord_5948786).sum := by decide
  have hdescent : baseEnd_5948786 < baseStart_5948786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948798 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5948798 : Nat := 118140960795 + 5948798 * 2 ^ 59
def prefixEnd_5948798 : Nat := 4983230072969 + 3 ^ 40 * 5948798 * 2
def baseEnd_5948798 : Nat := 1018197563501707178055661

theorem tailTrace_5948798 : CollatzResearch.WordTrace tailWord_5948798 prefixEnd_5948798 1018197563501707178055661 := by
  unfold tailWord_5948798
  simp only [CollatzResearch.WordTrace]
  refine ⟨27121310987816036832212881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144646991935018863105135365 27121310987816036832212881)
  ·
    refine ⟨20340983240862027624159661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27121310987816036832212881 20340983240862027624159661)
    ·
      refine ⟨7627868715323260359059873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20340983240862027624159661 7627868715323260359059873)
      ·
        refine ⟨5720901536492445269294905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627868715323260359059873 5720901536492445269294905)
        ·
          refine ⟨4290676152369333951971179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720901536492445269294905 4290676152369333951971179)
          ·
            refine ⟨6436014228554000927956769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290676152369333951971179 6436014228554000927956769)
            ·
              refine ⟨4827010671415500695967577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436014228554000927956769 4827010671415500695967577)
              ·
                refine ⟨3620258003561625521975683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827010671415500695967577 3620258003561625521975683)
                ·
                  refine ⟨5430387005342438282963525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620258003561625521975683 5430387005342438282963525)
                  ·
                    refine ⟨1018197563501707178055661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430387005342438282963525 1018197563501707178055661)
                    ·
                      rfl

theorem cell23_5948798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5948798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948798 prefixEnd_5948798 := by exact prefixLift 5948798
  have htrace : WordTrace (prefixWord ++ tailWord_5948798) baseStart_5948798 baseEnd_5948798 := by
    simpa [prefixWord, tailWord_5948798, baseEnd_5948798] using wordTrace_append hprefix tailTrace_5948798
  have hstable : (prefixWord ++ tailWord_5948798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948798).length < 2 ^ (prefixWord ++ tailWord_5948798).sum := by decide
  have hdescent : baseEnd_5948798 < baseStart_5948798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948803 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 2, 4]
def baseStart_5948803 : Nat := 118140960795 + 5948803 * 2 ^ 59
def prefixEnd_5948803 : Nat := 4983230072969 + 3 ^ 40 * 5948803 * 2
def baseEnd_5948803 : Nat := 1018198419302798004868153

theorem tailTrace_5948803 : CollatzResearch.WordTrace tailWord_5948803 prefixEnd_5948803 1018198419302798004868153 := by
  unfold tailWord_5948803
  simp only [CollatzResearch.WordTrace]
  refine ⟨216970670267510180511635063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144647113511673453674423375 216970670267510180511635063)
  ·
    refine ⟨325456005401265270767452595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216970670267510180511635063 325456005401265270767452595)
    ·
      refine ⟨488184008101897906151178893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325456005401265270767452595 488184008101897906151178893)
      ·
        refine ⟨183069003038211714806692085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488184008101897906151178893 183069003038211714806692085)
        ·
          refine ⟨17162719034832348263127383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183069003038211714806692085 17162719034832348263127383)
          ·
            refine ⟨25744078552248522394691075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17162719034832348263127383 25744078552248522394691075)
            ·
              refine ⟨38616117828372783592036613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25744078552248522394691075 38616117828372783592036613)
              ·
                refine ⟨7240522092819896923506865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38616117828372783592036613 7240522092819896923506865)
                ·
                  refine ⟨5430391569614922692630149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240522092819896923506865 5430391569614922692630149)
                  ·
                    refine ⟨1018198419302798004868153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430391569614922692630149 1018198419302798004868153)
                    ·
                      rfl

theorem cell23_5948803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 4].length) (baseStart_5948803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948803 prefixEnd_5948803 := by exact prefixLift 5948803
  have htrace : WordTrace (prefixWord ++ tailWord_5948803) baseStart_5948803 baseEnd_5948803 := by
    simpa [prefixWord, tailWord_5948803, baseEnd_5948803] using wordTrace_append hprefix tailTrace_5948803
  have hstable : (prefixWord ++ tailWord_5948803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948803).length < 2 ^ (prefixWord ++ tailWord_5948803).sum := by decide
  have hdescent : baseEnd_5948803 < baseStart_5948803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948804 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_5948804 : Nat := 118140960795 + 5948804 * 2 ^ 59
def prefixEnd_5948804 : Nat := 4983230072969 + 3 ^ 40 * 5948804 * 2
def baseEnd_5948804 : Nat := 3054595771389048510691955

theorem tailTrace_5948804 : CollatzResearch.WordTrace tailWord_5948804 prefixEnd_5948804 3054595771389048510691955 := by
  unfold tailWord_5948804
  simp only [CollatzResearch.WordTrace]
  refine ⟨108485353370253278841210733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144647137827004371788280977 108485353370253278841210733)
  ·
    refine ⟨40682007513844979565454025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108485353370253278841210733 40682007513844979565454025)
    ·
      refine ⟨30511505635383734674090519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40682007513844979565454025 30511505635383734674090519)
      ·
        refine ⟨45767258453075602011135779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30511505635383734674090519 45767258453075602011135779)
        ·
          refine ⟨68650887679613403016703669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45767258453075602011135779 68650887679613403016703669)
          ·
            refine ⟨6436020719963756532815969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68650887679613403016703669 6436020719963756532815969)
            ·
              refine ⟨4827015539972817399611977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436020719963756532815969 4827015539972817399611977)
              ·
                refine ⟨3620261654979613049708983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827015539972817399611977 3620261654979613049708983)
                ·
                  refine ⟨5430392482469419574563475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620261654979613049708983 5430392482469419574563475)
                  ·
                    refine ⟨8145588723704129361845213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5430392482469419574563475 8145588723704129361845213)
                    ·
                      refine ⟨3054595771389048510691955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8145588723704129361845213 3054595771389048510691955)
                      ·
                        rfl

theorem cell23_5948804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_5948804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948804 prefixEnd_5948804 := by exact prefixLift 5948804
  have htrace : WordTrace (prefixWord ++ tailWord_5948804) baseStart_5948804 baseEnd_5948804 := by
    simpa [prefixWord, tailWord_5948804, baseEnd_5948804] using wordTrace_append hprefix tailTrace_5948804
  have hstable : (prefixWord ++ tailWord_5948804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948804).length < 2 ^ (prefixWord ++ tailWord_5948804).sum := by decide
  have hdescent : baseEnd_5948804 < baseStart_5948804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948820 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5948820 : Nat := 118140960795 + 5948820 * 2 ^ 59
def prefixEnd_5948820 : Nat := 4983230072969 + 3 ^ 40 * 5948820 * 2
def baseEnd_5948820 : Nat := 1018201329026506816030627

theorem tailTrace_5948820 : CollatzResearch.WordTrace tailWord_5948820 prefixEnd_5948820 1018201329026506816030627 := by
  unfold tailWord_5948820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108485645154224296207501957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144647526872299061610002609 108485645154224296207501957)
  ·
    refine ⟨20341058466417055538906617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108485645154224296207501957 20341058466417055538906617)
    ·
      refine ⟨15255793849812791654179963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20341058466417055538906617 15255793849812791654179963)
      ·
        refine ⟨22883690774719187481269945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15255793849812791654179963 22883690774719187481269945)
        ·
          refine ⟨17162768081039390610952459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22883690774719187481269945 17162768081039390610952459)
          ·
            refine ⟨25744152121559085916428689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17162768081039390610952459 25744152121559085916428689)
            ·
              refine ⟨19308114091169314437321517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25744152121559085916428689 19308114091169314437321517)
              ·
                refine ⟨7240542784188492913995569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19308114091169314437321517 7240542784188492913995569)
                ·
                  refine ⟨5430407088141369685496677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240542784188492913995569 5430407088141369685496677)
                  ·
                    refine ⟨1018201329026506816030627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430407088141369685496677 1018201329026506816030627)
                    ·
                      rfl

theorem cell23_5948820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5948820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948820 prefixEnd_5948820 := by exact prefixLift 5948820
  have htrace : WordTrace (prefixWord ++ tailWord_5948820) baseStart_5948820 baseEnd_5948820 := by
    simpa [prefixWord, tailWord_5948820, baseEnd_5948820] using wordTrace_append hprefix tailTrace_5948820
  have hstable : (prefixWord ++ tailWord_5948820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948820).length < 2 ^ (prefixWord ++ tailWord_5948820).sum := by decide
  have hdescent : baseEnd_5948820 < baseStart_5948820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948896 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_5948896 : Nat := 118140960795 + 5948896 * 2 ^ 59
def prefixEnd_5948896 : Nat := 4983230072969 + 3 ^ 40 * 5948896 * 2
def baseEnd_5948896 : Nat := 3054643011609262150741531

theorem tailTrace_5948896 : CollatzResearch.WordTrace tailWord_5948896 prefixEnd_5948896 3054643011609262150741531 := by
  unfold tailWord_5948896
  simp only [CollatzResearch.WordTrace]
  refine ⟨108487031128086628697385271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144649374837448838263180361 108487031128086628697385271)
  ·
    refine ⟨162730546692129943046077907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108487031128086628697385271 162730546692129943046077907)
    ·
      refine ⟨244095820038194914569116861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162730546692129943046077907 244095820038194914569116861)
      ·
        refine ⟨91535932514323092963418823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244095820038194914569116861 91535932514323092963418823)
        ·
          refine ⟨137303898771484639445128235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91535932514323092963418823 137303898771484639445128235)
          ·
            refine ⟨205955848157226959167692353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137303898771484639445128235 205955848157226959167692353)
            ·
              refine ⟨154466886117920219375769265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205955848157226959167692353 154466886117920219375769265)
              ·
                refine ⟨115850164588440164531826949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154466886117920219375769265 115850164588440164531826949)
                ·
                  refine ⟨21721905860332530849717553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115850164588440164531826949 21721905860332530849717553)
                  ·
                    refine ⟨16291429395249398137288165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21721905860332530849717553 16291429395249398137288165)
                    ·
                      refine ⟨3054643011609262150741531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16291429395249398137288165 3054643011609262150741531)
                      ·
                        rfl

theorem cell23_5948896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_5948896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948896 prefixEnd_5948896 := by exact prefixLift 5948896
  have htrace : WordTrace (prefixWord ++ tailWord_5948896) baseStart_5948896 baseEnd_5948896 := by
    simpa [prefixWord, tailWord_5948896, baseEnd_5948896] using wordTrace_append hprefix tailTrace_5948896
  have hstable : (prefixWord ++ tailWord_5948896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948896).length < 2 ^ (prefixWord ++ tailWord_5948896).sum := by decide
  have hdescent : baseEnd_5948896 < baseStart_5948896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948903 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5948903 : Nat := 118140960795 + 5948903 * 2 ^ 59
def prefixEnd_5948903 : Nat := 4983230072969 + 3 ^ 40 * 5948903 * 2
def baseEnd_5948903 : Nat := 3054646605973843623353999

theorem tailTrace_5948903 : CollatzResearch.WordTrace tailWord_5948903 prefixEnd_5948903 3054646605973843623353999 := by
  unfold tailWord_5948903
  simp only [CollatzResearch.WordTrace]
  refine ⟨216974317567147897590275363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144649545044765265060183575 216974317567147897590275363)
  ·
    refine ⟨325461476350721846385413045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216974317567147897590275363 325461476350721846385413045)
    ·
      refine ⟨30512013407880173098632473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325461476350721846385413045 30512013407880173098632473)
      ·
        refine ⟨22884010055910129823974355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30512013407880173098632473 22884010055910129823974355)
        ·
          refine ⟨34326015083865194735961533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22884010055910129823974355 34326015083865194735961533)
          ·
            refine ⟨12872255656449448025985575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34326015083865194735961533 12872255656449448025985575)
            ·
              refine ⟨19308383484674172038978363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12872255656449448025985575 19308383484674172038978363)
              ·
                refine ⟨28962575227011258058467545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19308383484674172038978363 28962575227011258058467545)
                ·
                  refine ⟨21721931420258443543850659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28962575227011258058467545 21721931420258443543850659)
                  ·
                    refine ⟨32582897130387665315775989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21721931420258443543850659 32582897130387665315775989)
                    ·
                      refine ⟨3054646605973843623353999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32582897130387665315775989 3054646605973843623353999)
                      ·
                        rfl

theorem cell23_5948903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5948903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948903 prefixEnd_5948903 := by exact prefixLift 5948903
  have htrace : WordTrace (prefixWord ++ tailWord_5948903) baseStart_5948903 baseEnd_5948903 := by
    simpa [prefixWord, tailWord_5948903, baseEnd_5948903] using wordTrace_append hprefix tailTrace_5948903
  have hstable : (prefixWord ++ tailWord_5948903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948903).length < 2 ^ (prefixWord ++ tailWord_5948903).sum := by decide
  have hdescent : baseEnd_5948903 < baseStart_5948903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948936 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_5948936 : Nat := 118140960795 + 5948936 * 2 ^ 59
def prefixEnd_5948936 : Nat := 4983230072969 + 3 ^ 40 * 5948936 * 2
def baseEnd_5948936 : Nat := 1018221183611813998080449

theorem tailTrace_5948936 : CollatzResearch.WordTrace tailWord_5948936 prefixEnd_5948936 1018221183611813998080449 := by
  unfold tailWord_5948936
  simp only [CollatzResearch.WordTrace]
  refine ⟨108487760588014172113113331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144650347450685562817484441 108487760588014172113113331)
  ·
    refine ⟨162731640882021258169669997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108487760588014172113113331 162731640882021258169669997)
    ·
      refine ⟨61024365330757971813626249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162731640882021258169669997 61024365330757971813626249)
      ·
        refine ⟨45768273998068478860219687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61024365330757971813626249 45768273998068478860219687)
        ·
          refine ⟨68652410997102718290329531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45768273998068478860219687 68652410997102718290329531)
          ·
            refine ⟨102978616495654077435494297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68652410997102718290329531 102978616495654077435494297)
            ·
              refine ⟨77233962371740558076620723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102978616495654077435494297 77233962371740558076620723)
              ·
                refine ⟨115850943557610837114931085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77233962371740558076620723 115850943557610837114931085)
                ·
                  refine ⟨43444103834104063918099157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115850943557610837114931085 43444103834104063918099157)
                  ·
                    refine ⟨1018221183611813998080449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43444103834104063918099157 1018221183611813998080449)
                    ·
                      rfl

theorem cell23_5948936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_5948936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948936 prefixEnd_5948936 := by exact prefixLift 5948936
  have htrace : WordTrace (prefixWord ++ tailWord_5948936) baseStart_5948936 baseEnd_5948936 := by
    simpa [prefixWord, tailWord_5948936, baseEnd_5948936] using wordTrace_append hprefix tailTrace_5948936
  have hstable : (prefixWord ++ tailWord_5948936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948936).length < 2 ^ (prefixWord ++ tailWord_5948936).sum := by decide
  have hdescent : baseEnd_5948936 < baseStart_5948936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948974 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_5948974 : Nat := 118140960795 + 5948974 * 2 ^ 59
def prefixEnd_5948974 : Nat := 4983230072969 + 3 ^ 40 * 5948974 * 2
def baseEnd_5948974 : Nat := 339409229233368093951797

theorem tailTrace_5948974 : CollatzResearch.WordTrace tailWord_5948974 prefixEnd_5948974 339409229233368093951797 := by
  unfold tailWord_5948974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122113393736334589513747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144651271433260451144073317 27122113393736334589513747)
  ·
    refine ⟨40683170090604501884270621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27122113393736334589513747 40683170090604501884270621)
    ·
      refine ⟨15256188783976688206601483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40683170090604501884270621 15256188783976688206601483)
      ·
        refine ⟨22884283175965032309902225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15256188783976688206601483 22884283175965032309902225)
        ·
          refine ⟨17163212381973774232426669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22884283175965032309902225 17163212381973774232426669)
          ·
            refine ⟨6436204643240165337160001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17163212381973774232426669 6436204643240165337160001)
            ·
              refine ⟨4827153482430124002870001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436204643240165337160001 4827153482430124002870001)
              ·
                refine ⟨3620365111822593002152501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827153482430124002870001 3620365111822593002152501)
                ·
                  refine ⟨339409229233368093951797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620365111822593002152501 339409229233368093951797)
                  ·
                    rfl

theorem cell23_5948974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_5948974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948974 prefixEnd_5948974 := by exact prefixLift 5948974
  have htrace : WordTrace (prefixWord ++ tailWord_5948974) baseStart_5948974 baseEnd_5948974 := by
    simpa [prefixWord, tailWord_5948974, baseEnd_5948974] using wordTrace_append hprefix tailTrace_5948974
  have hstable : (prefixWord ++ tailWord_5948974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948974).length < 2 ^ (prefixWord ++ tailWord_5948974).sum := by decide
  have hdescent : baseEnd_5948974 < baseStart_5948974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5948976 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_5948976 : Nat := 118140960795 + 5948976 * 2 ^ 59
def prefixEnd_5948976 : Nat := 4983230072969 + 3 ^ 40 * 5948976 * 2
def baseEnd_5948976 : Nat := 3054684090061621837741163

theorem tailTrace_5948976 : CollatzResearch.WordTrace tailWord_5948976 prefixEnd_5948976 3054684090061621837741163 := by
  unfold tailWord_5948976
  simp only [CollatzResearch.WordTrace]
  refine ⟨108488490047941715528841391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144651320063922287371788521 108488490047941715528841391)
  ·
    refine ⟨162732735071912573293262087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108488490047941715528841391 162732735071912573293262087)
    ·
      refine ⟨244099102607868859939893131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162732735071912573293262087 244099102607868859939893131)
      ·
        refine ⟨366148653911803289909839697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244099102607868859939893131 366148653911803289909839697)
        ·
          refine ⟨274611490433852467432379773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366148653911803289909839697 274611490433852467432379773)
          ·
            refine ⟨102979308912694675287142415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274611490433852467432379773 102979308912694675287142415)
            ·
              refine ⟨154468963369042012930713623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102979308912694675287142415 154468963369042012930713623)
              ·
                refine ⟨231703445053563019396070435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154468963369042012930713623 231703445053563019396070435)
                ·
                  refine ⟨347555167580344529094105653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231703445053563019396070435 347555167580344529094105653)
                  ·
                    refine ⟨32583296960657299602572405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 347555167580344529094105653 32583296960657299602572405)
                    ·
                      refine ⟨3054684090061621837741163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32583296960657299602572405 3054684090061621837741163)
                      ·
                        rfl

theorem cell23_5948976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_5948976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5948976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5948976 prefixEnd_5948976 := by exact prefixLift 5948976
  have htrace : WordTrace (prefixWord ++ tailWord_5948976) baseStart_5948976 baseEnd_5948976 := by
    simpa [prefixWord, tailWord_5948976, baseEnd_5948976] using wordTrace_append hprefix tailTrace_5948976
  have hstable : (prefixWord ++ tailWord_5948976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5948976).length < 2 ^ (prefixWord ++ tailWord_5948976).sum := by decide
  have hdescent : baseEnd_5948976 < baseStart_5948976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5948976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949010 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_5949010 : Nat := 118140960795 + 5949010 * 2 ^ 59
def prefixEnd_5949010 : Nat := 4983230072969 + 3 ^ 40 * 5949010 * 2
def baseEnd_5949010 : Nat := 3054701548403874704716007

theorem tailTrace_5949010 : CollatzResearch.WordTrace tailWord_5949010 prefixEnd_5949010 3054701548403874704716007 := by
  unfold tailWord_5949010
  simp only [CollatzResearch.WordTrace]
  refine ⟨54244555044440063716105121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144652146785173503242946989 54244555044440063716105121)
  ·
    refine ⟨40683416283330047787078841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54244555044440063716105121 40683416283330047787078841)
    ·
      refine ⟨30512562212497535840309131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40683416283330047787078841 30512562212497535840309131)
      ·
        refine ⟨45768843318746303760463697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30512562212497535840309131 45768843318746303760463697)
        ·
          refine ⟨34326632489059727820347773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45768843318746303760463697 34326632489059727820347773)
          ·
            refine ⟨12872487183397397932630415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34326632489059727820347773 12872487183397397932630415)
            ·
              refine ⟨19308730775096096898945623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12872487183397397932630415 19308730775096096898945623)
              ·
                refine ⟨28963096162644145348418435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19308730775096096898945623 28963096162644145348418435)
                ·
                  refine ⟨43444644243966218022627653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28963096162644145348418435 43444644243966218022627653)
                  ·
                    refine ⟨8145870795743665879242685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43444644243966218022627653 8145870795743665879242685)
                    ·
                      refine ⟨3054701548403874704716007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8145870795743665879242685 3054701548403874704716007)
                      ·
                        rfl

theorem cell23_5949010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_5949010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949010 prefixEnd_5949010 := by exact prefixLift 5949010
  have htrace : WordTrace (prefixWord ++ tailWord_5949010) baseStart_5949010 baseEnd_5949010 := by
    simpa [prefixWord, tailWord_5949010, baseEnd_5949010] using wordTrace_append hprefix tailTrace_5949010
  have hstable : (prefixWord ++ tailWord_5949010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949010).length < 2 ^ (prefixWord ++ tailWord_5949010).sum := by decide
  have hdescent : baseEnd_5949010 < baseStart_5949010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949050 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_5949050 : Nat := 118140960795 + 5949050 * 2 ^ 59
def prefixEnd_5949050 : Nat := 4983230072969 + 3 ^ 40 * 5949050 * 2
def baseEnd_5949050 : Nat := 3054722087630054548215823

theorem tailTrace_5949050 : CollatzResearch.WordTrace tailWord_5949050 prefixEnd_5949050 3054722087630054548215823 := by
  unfold tailWord_5949050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54244919774403835423969151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144653119398410227797251069 54244919774403835423969151)
  ·
    refine ⟨81367379661605753135953727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54244919774403835423969151 81367379661605753135953727)
    ·
      refine ⟨122051069492408629703930591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81367379661605753135953727 122051069492408629703930591)
      ·
        refine ⟨183076604238612944555895887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122051069492408629703930591 183076604238612944555895887)
        ·
          refine ⟨274614906357919416833843831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183076604238612944555895887 274614906357919416833843831)
          ·
            refine ⟨411922359536879125250765747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274614906357919416833843831 411922359536879125250765747)
            ·
              refine ⟨617883539305318687876148621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411922359536879125250765747 617883539305318687876148621)
              ·
                refine ⟨231706327239494507953555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617883539305318687876148621 231706327239494507953555733)
                ·
                  refine ⟨10861234089351305060322925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231706327239494507953555733 10861234089351305060322925)
                  ·
                    refine ⟨4072962783506739397621097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861234089351305060322925 4072962783506739397621097)
                    ·
                      refine ⟨3054722087630054548215823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072962783506739397621097 3054722087630054548215823)
                      ·
                        rfl

theorem cell23_5949050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_5949050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949050 prefixEnd_5949050 := by exact prefixLift 5949050
  have htrace : WordTrace (prefixWord ++ tailWord_5949050) baseStart_5949050 baseEnd_5949050 := by
    simpa [prefixWord, tailWord_5949050, baseEnd_5949050] using wordTrace_append hprefix tailTrace_5949050
  have hstable : (prefixWord ++ tailWord_5949050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949050).length < 2 ^ (prefixWord ++ tailWord_5949050).sum := by decide
  have hdescent : baseEnd_5949050 < baseStart_5949050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949057 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5949057 : Nat := 118140960795 + 5949057 * 2 ^ 59
def prefixEnd_5949057 : Nat := 4983230072969 + 3 ^ 40 * 5949057 * 2
def baseEnd_5949057 : Nat := 3054725681994636020828291

theorem tailTrace_5949057 : CollatzResearch.WordTrace tailWord_5949057 prefixEnd_5949057 3054725681994636020828291 := by
  unfold tailWord_5949057
  simp only [CollatzResearch.WordTrace]
  refine ⟨216979934408589981891381425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144653289605726654594254283 216979934408589981891381425)
  ·
    refine ⟨162734950806442486418536069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216979934408589981891381425 162734950806442486418536069)
    ·
      refine ⟨30512803276207966203475513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162734950806442486418536069 30512803276207966203475513)
      ·
        refine ⟨22884602457155974652606635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30512803276207966203475513 22884602457155974652606635)
        ·
          refine ⟨34326903685733961978909953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22884602457155974652606635 34326903685733961978909953)
          ·
            refine ⟨25745177764300471484182465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34326903685733961978909953 25745177764300471484182465)
            ·
              refine ⟨19308883323225353613136849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25745177764300471484182465 19308883323225353613136849)
              ·
                refine ⟨14481662492419015209852637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19308883323225353613136849 14481662492419015209852637)
                ·
                  refine ⟨5430623434657130703694739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14481662492419015209852637 5430623434657130703694739)
                  ·
                    refine ⟨8145935151985696055542109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5430623434657130703694739 8145935151985696055542109)
                    ·
                      refine ⟨3054725681994636020828291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8145935151985696055542109 3054725681994636020828291)
                      ·
                        rfl

theorem cell23_5949057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5949057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949057 prefixEnd_5949057 := by exact prefixLift 5949057
  have htrace : WordTrace (prefixWord ++ tailWord_5949057) baseStart_5949057 baseEnd_5949057 := by
    simpa [prefixWord, tailWord_5949057, baseEnd_5949057] using wordTrace_append hprefix tailTrace_5949057
  have hstable : (prefixWord ++ tailWord_5949057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949057).length < 2 ^ (prefixWord ++ tailWord_5949057).sum := by decide
  have hdescent : baseEnd_5949057 < baseStart_5949057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949084 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5949084 : Nat := 118140960795 + 5949084 * 2 ^ 59
def prefixEnd_5949084 : Nat := 4983230072969 + 3 ^ 40 * 5949084 * 2
def baseEnd_5949084 : Nat := 3054739545972307415190667

theorem tailTrace_5949084 : CollatzResearch.WordTrace tailWord_5949084 prefixEnd_5949084 3054739545972307415190667 := by
  unfold tailWord_5949084
  simp only [CollatzResearch.WordTrace]
  refine ⟨108490459589746082751307153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144653946119661443668409537 108490459589746082751307153)
  ·
    refine ⟨81367844692309562063480365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108490459589746082751307153 81367844692309562063480365)
    ·
      refine ⟨30512941759616085773805137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81367844692309562063480365 30512941759616085773805137)
      ·
        refine ⟨22884706319712064330353853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30512941759616085773805137 22884706319712064330353853)
        ·
          refine ⟨8581764869892024123882695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22884706319712064330353853 8581764869892024123882695)
          ·
            refine ⟨12872647304838036185824043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8581764869892024123882695 12872647304838036185824043)
            ·
              refine ⟨19308970957257054278736065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12872647304838036185824043 19308970957257054278736065)
              ·
                refine ⟨14481728217942790709052049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19308970957257054278736065 14481728217942790709052049)
                ·
                  refine ⟨10861296163457093031789037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14481728217942790709052049 10861296163457093031789037)
                  ·
                    refine ⟨4072986061296409886920889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861296163457093031789037 4072986061296409886920889)
                    ·
                      refine ⟨3054739545972307415190667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4072986061296409886920889 3054739545972307415190667)
                      ·
                        rfl

theorem cell23_5949084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5949084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949084 prefixEnd_5949084 := by exact prefixLift 5949084
  have htrace : WordTrace (prefixWord ++ tailWord_5949084) baseStart_5949084 baseEnd_5949084 := by
    simpa [prefixWord, tailWord_5949084, baseEnd_5949084] using wordTrace_append hprefix tailTrace_5949084
  have hstable : (prefixWord ++ tailWord_5949084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949084).length < 2 ^ (prefixWord ++ tailWord_5949084).sum := by decide
  have hdescent : baseEnd_5949084 < baseStart_5949084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949093 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_5949093 : Nat := 118140960795 + 5949093 * 2 ^ 59
def prefixEnd_5949093 : Nat := 4983230072969 + 3 ^ 40 * 5949093 * 2
def baseEnd_5949093 : Nat := 3054744167298197879978125

theorem tailTrace_5949093 : CollatzResearch.WordTrace tailWord_5949093 prefixEnd_5949093 3054744167298197879978125 := by
  unfold tailWord_5949093
  simp only [CollatzResearch.WordTrace]
  refine ⟨216981247436459560039691933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144654164957639706693127955 216981247436459560039691933)
  ·
    refine ⟨81367967788672335014884475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216981247436459560039691933 81367967788672335014884475)
    ·
      refine ⟨122051951683008502522326713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81367967788672335014884475 122051951683008502522326713)
      ·
        refine ⟨91538963762256376891745035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122051951683008502522326713 91538963762256376891745035)
        ·
          refine ⟨137308445643384565337617553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91538963762256376891745035 137308445643384565337617553)
          ·
            refine ⟨102981334232538424003213165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137308445643384565337617553 102981334232538424003213165)
            ·
              refine ⟨38618000337201909001204937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102981334232538424003213165 38618000337201909001204937)
              ·
                refine ⟨28963500252901431750903703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38618000337201909001204937 28963500252901431750903703)
                ·
                  refine ⟨43445250379352147626355555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28963500252901431750903703 43445250379352147626355555)
                  ·
                    refine ⟨65167875569028221439533333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43445250379352147626355555 65167875569028221439533333)
                    ·
                      refine ⟨3054744167298197879978125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65167875569028221439533333 3054744167298197879978125)
                      ·
                        rfl

theorem cell23_5949093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_5949093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949093 prefixEnd_5949093 := by exact prefixLift 5949093
  have htrace : WordTrace (prefixWord ++ tailWord_5949093) baseStart_5949093 baseEnd_5949093 := by
    simpa [prefixWord, tailWord_5949093, baseEnd_5949093] using wordTrace_append hprefix tailTrace_5949093
  have hstable : (prefixWord ++ tailWord_5949093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949093).length < 2 ^ (prefixWord ++ tailWord_5949093).sum := by decide
  have hdescent : baseEnd_5949093 < baseStart_5949093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949103 : List Nat := [1, 1, 2, 1, 2, 4, 4, 8]
def baseStart_5949103 : Nat := 118140960795 + 5949103 * 2 ^ 59
def prefixEnd_5949103 : Nat := 4983230072969 + 3 ^ 40 * 5949103 * 2
def baseEnd_5949103 : Nat := 113138863040916401513077

theorem tailTrace_5949103 : CollatzResearch.WordTrace tailWord_5949103 prefixEnd_5949103 113138863040916401513077 := by
  unfold tailWord_5949103
  simp only [CollatzResearch.WordTrace]
  refine ⟨216981612166423331747555963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144654408110948887831703975 216981612166423331747555963)
  ·
    refine ⟨325472418249634997621333945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216981612166423331747555963 325472418249634997621333945)
    ·
      refine ⟨244104313687226248216000459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325472418249634997621333945 244104313687226248216000459)
      ·
        refine ⟨366156470530839372324000689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244104313687226248216000459 366156470530839372324000689)
        ·
          refine ⟨274617352898129529243000517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366156470530839372324000689 274617352898129529243000517)
          ·
            refine ⟨51490753668399286733062597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274617352898129529243000517 51490753668399286733062597)
            ·
              refine ⟨9654516312824866262449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51490753668399286733062597 9654516312824866262449237)
              ·
                refine ⟨113138863040916401513077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9654516312824866262449237 113138863040916401513077)
                ·
                  rfl

theorem cell23_5949103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 8].length) (baseStart_5949103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949103 prefixEnd_5949103 := by exact prefixLift 5949103
  have htrace : WordTrace (prefixWord ++ tailWord_5949103) baseStart_5949103 baseEnd_5949103 := by
    simpa [prefixWord, tailWord_5949103, baseEnd_5949103] using wordTrace_append hprefix tailTrace_5949103
  have hstable : (prefixWord ++ tailWord_5949103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949103).length < 2 ^ (prefixWord ++ tailWord_5949103).sum := by decide
  have hdescent : baseEnd_5949103 < baseStart_5949103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949134 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_5949134 : Nat := 118140960795 + 5949134 * 2 ^ 59
def prefixEnd_5949134 : Nat := 4983230072969 + 3 ^ 40 * 5949134 * 2
def baseEnd_5949134 : Nat := 3054765220005032219565437

theorem tailTrace_5949134 : CollatzResearch.WordTrace tailWord_5949134 prefixEnd_5949134 3054765220005032219565437 := by
  unfold tailWord_5949134
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122842853663878005241807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144655161886207349361289637 27122842853663878005241807)
  ·
    refine ⟨40684264280495817007862711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27122842853663878005241807 40684264280495817007862711)
    ·
      refine ⟨61026396420743725511794067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40684264280495817007862711 61026396420743725511794067)
      ·
        refine ⟨91539594631115588267691101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61026396420743725511794067 91539594631115588267691101)
        ·
          refine ⟨34327347986668345600384163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91539594631115588267691101 34327347986668345600384163)
          ·
            refine ⟨51491021980002518400576245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34327347986668345600384163 51491021980002518400576245)
            ·
              refine ⟨4827283310625236100054023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51491021980002518400576245 4827283310625236100054023)
              ·
                refine ⟨7240924965937854150081035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827283310625236100054023 7240924965937854150081035)
                ·
                  refine ⟨10861387448906781225121553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7240924965937854150081035 10861387448906781225121553)
                  ·
                    refine ⟨8146040586680085918841165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10861387448906781225121553 8146040586680085918841165)
                    ·
                      refine ⟨3054765220005032219565437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146040586680085918841165 3054765220005032219565437)
                      ·
                        rfl

theorem cell23_5949134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_5949134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949134 prefixEnd_5949134 := by exact prefixLift 5949134
  have htrace : WordTrace (prefixWord ++ tailWord_5949134) baseStart_5949134 baseEnd_5949134 := by
    simpa [prefixWord, tailWord_5949134, baseEnd_5949134] using wordTrace_append hprefix tailTrace_5949134
  have hstable : (prefixWord ++ tailWord_5949134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949134).length < 2 ^ (prefixWord ++ tailWord_5949134).sum := by decide
  have hdescent : baseEnd_5949134 < baseStart_5949134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949142 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5949142 : Nat := 118140960795 + 5949142 * 2 ^ 59
def prefixEnd_5949142 : Nat := 4983230072969 + 3 ^ 40 * 5949142 * 2
def baseEnd_5949142 : Nat := 3054769327850268188265401

theorem tailTrace_5949142 : CollatzResearch.WordTrace tailWord_5949142 prefixEnd_5949142 3054769327850268188265401 := by
  unfold tailWord_5949142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561439663330127588014105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144655356408854694272150453 13561439663330127588014105)
  ·
    refine ⟨10171079747497595691010579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13561439663330127588014105 10171079747497595691010579)
    ·
      refine ⟨15256619621246393536515869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10171079747497595691010579 15256619621246393536515869)
      ·
        refine ⟨5721232357967397576193451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15256619621246393536515869 5721232357967397576193451)
        ·
          refine ⟨8581848536951096364290177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721232357967397576193451 8581848536951096364290177)
          ·
            refine ⟨6436386402713322273217633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8581848536951096364290177 6436386402713322273217633)
            ·
              refine ⟨4827289802034991704913225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436386402713322273217633 4827289802034991704913225)
              ·
                refine ⟨3620467351526243778684919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827289802034991704913225 3620467351526243778684919)
                ·
                  refine ⟨5430701027289365668027379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620467351526243778684919 5430701027289365668027379)
                  ·
                    refine ⟨8146051540934048502041069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5430701027289365668027379 8146051540934048502041069)
                    ·
                      refine ⟨3054769327850268188265401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146051540934048502041069 3054769327850268188265401)
                      ·
                        rfl

theorem cell23_5949142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5949142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949142 prefixEnd_5949142 := by exact prefixLift 5949142
  have htrace : WordTrace (prefixWord ++ tailWord_5949142) baseStart_5949142 baseEnd_5949142 := by
    simpa [prefixWord, tailWord_5949142, baseEnd_5949142] using wordTrace_append hprefix tailTrace_5949142
  have hstable : (prefixWord ++ tailWord_5949142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949142).length < 2 ^ (prefixWord ++ tailWord_5949142).sum := by decide
  have hdescent : baseEnd_5949142 < baseStart_5949142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949157 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5949157 : Nat := 118140960795 + 5949157 * 2 ^ 59
def prefixEnd_5949157 : Nat := 4983230072969 + 3 ^ 40 * 5949157 * 2
def baseEnd_5949157 : Nat := 3054777030060085629577831

theorem tailTrace_5949157 : CollatzResearch.WordTrace tailWord_5949157 prefixEnd_5949157 3054777030060085629577831 := by
  unfold tailWord_5949157
  simp only [CollatzResearch.WordTrace]
  refine ⟨216983581708227698970021725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144655721138818465980014483 216983581708227698970021725)
  ·
    refine ⟨81368843140585387113758147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216983581708227698970021725 81368843140585387113758147)
    ·
      refine ⟨122053264710878080670637221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81368843140585387113758147 122053264710878080670637221)
      ·
        refine ⟨22884987133289640125744479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122053264710878080670637221 22884987133289640125744479)
        ·
          refine ⟨34327480699934460188616719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22884987133289640125744479 34327480699934460188616719)
          ·
            refine ⟨51491221049901690282925079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34327480699934460188616719 51491221049901690282925079)
            ·
              refine ⟨77236831574852535424387619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51491221049901690282925079 77236831574852535424387619)
              ·
                refine ⟨115855247362278803136581429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77236831574852535424387619 115855247362278803136581429)
                ·
                  refine ⟨10861429440213637794054509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115855247362278803136581429 10861429440213637794054509)
                  ·
                    refine ⟨4073036040080114172770441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861429440213637794054509 4073036040080114172770441)
                    ·
                      refine ⟨3054777030060085629577831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073036040080114172770441 3054777030060085629577831)
                      ·
                        rfl

theorem cell23_5949157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5949157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949157 prefixEnd_5949157 := by exact prefixLift 5949157
  have htrace : WordTrace (prefixWord ++ tailWord_5949157) baseStart_5949157 baseEnd_5949157 := by
    simpa [prefixWord, tailWord_5949157, baseEnd_5949157] using wordTrace_append hprefix tailTrace_5949157
  have hstable : (prefixWord ++ tailWord_5949157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949157).length < 2 ^ (prefixWord ++ tailWord_5949157).sum := by decide
  have hdescent : baseEnd_5949157 < baseStart_5949157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949163 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 8]
def baseStart_5949163 : Nat := 118140960795 + 5949163 * 2 ^ 59
def prefixEnd_5949163 : Nat := 4983230072969 + 3 ^ 40 * 5949163 * 2
def baseEnd_5949163 : Nat := 1018260036981337535367601

theorem tailTrace_5949163 : CollatzResearch.WordTrace tailWord_5949163 prefixEnd_5949163 1018260036981337535367601 := by
  unfold tailWord_5949163
  simp only [CollatzResearch.WordTrace]
  refine ⟨216983800546205961994740143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144655867030803974663160095 216983800546205961994740143)
  ·
    refine ⟨325475700819308942992110215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216983800546205961994740143 325475700819308942992110215)
    ·
      refine ⟨488213551228963414488165323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325475700819308942992110215 488213551228963414488165323)
      ·
        refine ⟨732320326843445121732247985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488213551228963414488165323 732320326843445121732247985)
        ·
          refine ⟨549240245132583841299185989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732320326843445121732247985 549240245132583841299185989)
          ·
            refine ⟨102982545962359470243597373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 549240245132583841299185989 102982545962359470243597373)
            ·
              refine ⟨38618454735884801341349015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102982545962359470243597373 38618454735884801341349015)
              ·
                refine ⟨57927682103827202012023523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38618454735884801341349015 57927682103827202012023523)
                ·
                  refine ⟨86891523155740803018035285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57927682103827202012023523 86891523155740803018035285)
                  ·
                    refine ⟨1018260036981337535367601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86891523155740803018035285 1018260036981337535367601)
                    ·
                      rfl

theorem cell23_5949163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_5949163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949163 prefixEnd_5949163 := by exact prefixLift 5949163
  have htrace : WordTrace (prefixWord ++ tailWord_5949163) baseStart_5949163 baseEnd_5949163 := by
    simpa [prefixWord, tailWord_5949163, baseEnd_5949163] using wordTrace_append hprefix tailTrace_5949163
  have hstable : (prefixWord ++ tailWord_5949163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949163).length < 2 ^ (prefixWord ++ tailWord_5949163).sum := by decide
  have hdescent : baseEnd_5949163 < baseStart_5949163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949170 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5949170 : Nat := 118140960795 + 5949170 * 2 ^ 59
def prefixEnd_5949170 : Nat := 4983230072969 + 3 ^ 40 * 5949170 * 2
def baseEnd_5949170 : Nat := 3054783705308594078715271

theorem tailTrace_5949170 : CollatzResearch.WordTrace tailWord_5949170 prefixEnd_5949170 3054783705308594078715271 := by
  unfold tailWord_5949170
  simp only [CollatzResearch.WordTrace]
  refine ⟨54246013964295150547561241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144656037238120401460163309 54246013964295150547561241)
  ·
    refine ⟨40684510473221362910670931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54246013964295150547561241 40684510473221362910670931)
    ·
      refine ⟨61026765709832044366006397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40684510473221362910670931 61026765709832044366006397)
      ·
        refine ⟨22885037141187016637252399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61026765709832044366006397 22885037141187016637252399)
        ·
          refine ⟨34327555711780524955878599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22885037141187016637252399 34327555711780524955878599)
          ·
            refine ⟨51491333567670787433817899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34327555711780524955878599 51491333567670787433817899)
            ·
              refine ⟨77237000351506181150726849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51491333567670787433817899 77237000351506181150726849)
              ·
                refine ⟨57927750263629635863045137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77237000351506181150726849 57927750263629635863045137)
                ·
                  refine ⟨43445812697722226897283853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57927750263629635863045137 43445812697722226897283853)
                  ·
                    refine ⟨16292179761645835086481445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43445812697722226897283853 16292179761645835086481445)
                    ·
                      refine ⟨3054783705308594078715271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16292179761645835086481445 3054783705308594078715271)
                      ·
                        rfl

theorem cell23_5949170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5949170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949170 prefixEnd_5949170 := by exact prefixLift 5949170
  have htrace : WordTrace (prefixWord ++ tailWord_5949170) baseStart_5949170 baseEnd_5949170 := by
    simpa [prefixWord, tailWord_5949170, baseEnd_5949170] using wordTrace_append hprefix tailTrace_5949170
  have hstable : (prefixWord ++ tailWord_5949170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949170).length < 2 ^ (prefixWord ++ tailWord_5949170).sum := by decide
  have hdescent : baseEnd_5949170 < baseStart_5949170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949174 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5949174 : Nat := 118140960795 + 5949174 * 2 ^ 59
def prefixEnd_5949174 : Nat := 4983230072969 + 3 ^ 40 * 5949174 * 2
def baseEnd_5949174 : Nat := 3054785759231212063065253

theorem tailTrace_5949174 : CollatzResearch.WordTrace tailWord_5949174 prefixEnd_5949174 3054785759231212063065253 := by
  unfold tailWord_5949174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561512609322881929586911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144656134499444073915593717 13561512609322881929586911)
  ·
    refine ⟨20342268913984322894380367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13561512609322881929586911 20342268913984322894380367)
    ·
      refine ⟨30513403370976484341570551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20342268913984322894380367 30513403370976484341570551)
      ·
        refine ⟨45770105056464726512355827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30513403370976484341570551 45770105056464726512355827)
        ·
          refine ⟨68655157584697089768533741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45770105056464726512355827 68655157584697089768533741)
          ·
            refine ⟨25745684094261408663200153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68655157584697089768533741 25745684094261408663200153)
            ·
              refine ⟨19309263070696056497400115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25745684094261408663200153 19309263070696056497400115)
              ·
                refine ⟨28963894606044084746100173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19309263070696056497400115 28963894606044084746100173)
                ·
                  refine ⟨10861460477266531779787565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28963894606044084746100173 10861460477266531779787565)
                  ·
                    refine ⟨4073047678974949417420337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861460477266531779787565 4073047678974949417420337)
                    ·
                      refine ⟨3054785759231212063065253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073047678974949417420337 3054785759231212063065253)
                      ·
                        rfl

theorem cell23_5949174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5949174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949174 prefixEnd_5949174 := by exact prefixLift 5949174
  have htrace : WordTrace (prefixWord ++ tailWord_5949174) baseStart_5949174 baseEnd_5949174 := by
    simpa [prefixWord, tailWord_5949174, baseEnd_5949174] using wordTrace_append hprefix tailTrace_5949174
  have hstable : (prefixWord ++ tailWord_5949174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949174).length < 2 ^ (prefixWord ++ tailWord_5949174).sum := by decide
  have hdescent : baseEnd_5949174 < baseStart_5949174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949187 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 1, 4, 2]
def baseStart_5949187 : Nat := 118140960795 + 5949187 * 2 ^ 59
def prefixEnd_5949187 : Nat := 4983230072969 + 3 ^ 40 * 5949187 * 2
def baseEnd_5949187 : Nat := 3054792434479720512202693

theorem tailTrace_5949187 : CollatzResearch.WordTrace tailWord_5949187 prefixEnd_5949187 3054792434479720512202693 := by
  unfold tailWord_5949187
  simp only [CollatzResearch.WordTrace]
  refine ⟨216984675898119014093613815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144656450598746009395742543 216984675898119014093613815)
  ·
    refine ⟨325477013847178521140420723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216984675898119014093613815 325477013847178521140420723)
    ·
      refine ⟨488215520770767781710631085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325477013847178521140420723 488215520770767781710631085)
      ·
        refine ⟨183080820289037918141486657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488215520770767781710631085 183080820289037918141486657)
        ·
          refine ⟨137310615216778438606114993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183080820289037918141486657 137310615216778438606114993)
          ·
            refine ⟨102982961412583828954586245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137310615216778438606114993 102982961412583828954586245)
            ·
              refine ⟨19309305264859467928984921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102982961412583828954586245 19309305264859467928984921)
              ·
                refine ⟨14481978948644600946738691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19309305264859467928984921 14481978948644600946738691)
                ·
                  refine ⟨21722968422966901420108037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14481978948644600946738691 21722968422966901420108037)
                  ·
                    refine ⟨4073056579306294016270257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21722968422966901420108037 4073056579306294016270257)
                    ·
                      refine ⟨3054792434479720512202693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073056579306294016270257 3054792434479720512202693)
                      ·
                        rfl

theorem cell23_5949187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_5949187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949187 prefixEnd_5949187 := by exact prefixLift 5949187
  have htrace : WordTrace (prefixWord ++ tailWord_5949187) baseStart_5949187 baseEnd_5949187 := by
    simpa [prefixWord, tailWord_5949187, baseEnd_5949187] using wordTrace_append hprefix tailTrace_5949187
  have hstable : (prefixWord ++ tailWord_5949187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949187).length < 2 ^ (prefixWord ++ tailWord_5949187).sum := by decide
  have hdescent : baseEnd_5949187 < baseStart_5949187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949191 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5949191 : Nat := 118140960795 + 5949191 * 2 ^ 59
def prefixEnd_5949191 : Nat := 4983230072969 + 3 ^ 40 * 5949191 * 2
def baseEnd_5949191 : Nat := 3054794488402338496552675

theorem tailTrace_5949191 : CollatzResearch.WordTrace tailWord_5949191 prefixEnd_5949191 3054794488402338496552675 := by
  unfold tailWord_5949191
  simp only [CollatzResearch.WordTrace]
  refine ⟨216984821790104522776759427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144656547860069681851172951 216984821790104522776759427)
  ·
    refine ⟨325477232685156784165139141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216984821790104522776759427 325477232685156784165139141)
    ·
      refine ⟨61026981128466897030963589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325477232685156784165139141 61026981128466897030963589)
      ·
        refine ⟨11442558961587543193305673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61026981128466897030963589 11442558961587543193305673)
        ·
          refine ⟨8581919221190657394979255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11442558961587543193305673 8581919221190657394979255)
          ·
            refine ⟨12872878831785986092468883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8581919221190657394979255 12872878831785986092468883)
            ·
              refine ⟨19309318247678979138703325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12872878831785986092468883 19309318247678979138703325)
              ·
                refine ⟨7240994342879617177013747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19309318247678979138703325 7240994342879617177013747)
                ·
                  refine ⟨10861491514319425765520621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7240994342879617177013747 10861491514319425765520621)
                  ·
                    refine ⟨4073059317869784662070233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861491514319425765520621 4073059317869784662070233)
                    ·
                      refine ⟨3054794488402338496552675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073059317869784662070233 3054794488402338496552675)
                      ·
                        rfl

theorem cell23_5949191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5949191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949191 prefixEnd_5949191 := by exact prefixLift 5949191
  have htrace : WordTrace (prefixWord ++ tailWord_5949191) baseStart_5949191 baseEnd_5949191 := by
    simpa [prefixWord, tailWord_5949191, baseEnd_5949191] using wordTrace_append hprefix tailTrace_5949191
  have hstable : (prefixWord ++ tailWord_5949191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949191).length < 2 ^ (prefixWord ++ tailWord_5949191).sum := by decide
  have hdescent : baseEnd_5949191 < baseStart_5949191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949193 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 11]
def baseStart_5949193 : Nat := 118140960795 + 5949193 * 2 ^ 59
def prefixEnd_5949193 : Nat := 4983230072969 + 3 ^ 40 * 5949193 * 2
def baseEnd_5949193 : Nat := 339421723929294165414185

theorem tailTrace_5949193 : CollatzResearch.WordTrace tailWord_5949193 prefixEnd_5949193 339421723929294165414185 := by
  unfold tailWord_5949193
  simp only [CollatzResearch.WordTrace]
  refine ⟨216984894736097277118332233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144656596490731518078888155 216984894736097277118332233)
  ·
    refine ⟨162738671052072957838749175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216984894736097277118332233 162738671052072957838749175)
    ·
      refine ⟨244108006578109436758123763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162738671052072957838749175 244108006578109436758123763)
      ·
        refine ⟨366162009867164155137185645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244108006578109436758123763 366162009867164155137185645)
        ·
          refine ⟨137310753700186558176444617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366162009867164155137185645 137310753700186558176444617)
          ·
            refine ⟨102983065275139918632333463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137310753700186558176444617 102983065275139918632333463)
            ·
              refine ⟨154474597912709877948500195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102983065275139918632333463 154474597912709877948500195)
              ·
                refine ⟨231711896869064816922750293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154474597912709877948500195 231711896869064816922750293)
                ·
                  refine ⟨339421723929294165414185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 231711896869064816922750293 339421723929294165414185)
                  ·
                    rfl

theorem cell23_5949193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_5949193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949193 prefixEnd_5949193 := by exact prefixLift 5949193
  have htrace : WordTrace (prefixWord ++ tailWord_5949193) baseStart_5949193 baseEnd_5949193 := by
    simpa [prefixWord, tailWord_5949193, baseEnd_5949193] using wordTrace_append hprefix tailTrace_5949193
  have hstable : (prefixWord ++ tailWord_5949193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949193).length < 2 ^ (prefixWord ++ tailWord_5949193).sum := by decide
  have hdescent : baseEnd_5949193 < baseStart_5949193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949203 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_5949203 : Nat := 118140960795 + 5949203 * 2 ^ 59
def prefixEnd_5949203 : Nat := 4983230072969 + 3 ^ 40 * 5949203 * 2
def baseEnd_5949203 : Nat := 3054800650170192449602619

theorem tailTrace_5949203 : CollatzResearch.WordTrace tailWord_5949203 prefixEnd_5949203 3054800650170192449602619 := by
  unfold tailWord_5949203
  simp only [CollatzResearch.WordTrace]
  refine ⟨216985259466061048826196263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144656839644040699217464175 216985259466061048826196263)
  ·
    refine ⟨325477889199091573239294395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216985259466061048826196263 325477889199091573239294395)
    ·
      refine ⟨488216833798637359858941593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325477889199091573239294395 488216833798637359858941593)
      ·
        refine ⟨366162625348978019894206195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488216833798637359858941593 366162625348978019894206195)
        ·
          refine ⟨549243938023467029841309293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366162625348978019894206195 549243938023467029841309293)
          ·
            refine ⟨205966476758800136190490985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549243938023467029841309293 205966476758800136190490985)
            ·
              refine ⟨154474857569100102142868239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205966476758800136190490985 154474857569100102142868239)
              ·
                refine ⟨231712286353650153214302359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154474857569100102142868239 231712286353650153214302359)
                ·
                  refine ⟨347568429530475229821453539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231712286353650153214302359 347568429530475229821453539)
                  ·
                    refine ⟨521352644295712844732180309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347568429530475229821453539 521352644295712844732180309)
                    ·
                      refine ⟨3054800650170192449602619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 521352644295712844732180309 3054800650170192449602619)
                      ·
                        rfl

theorem cell23_5949203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_5949203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949203 prefixEnd_5949203 := by exact prefixLift 5949203
  have htrace : WordTrace (prefixWord ++ tailWord_5949203) baseStart_5949203 baseEnd_5949203 := by
    simpa [prefixWord, tailWord_5949203, baseEnd_5949203] using wordTrace_append hprefix tailTrace_5949203
  have hstable : (prefixWord ++ tailWord_5949203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949203).length < 2 ^ (prefixWord ++ tailWord_5949203).sum := by decide
  have hdescent : baseEnd_5949203 < baseStart_5949203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949210 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_5949210 : Nat := 118140960795 + 5949210 * 2 ^ 59
def prefixEnd_5949210 : Nat := 4983230072969 + 3 ^ 40 * 5949210 * 2
def baseEnd_5949210 : Nat := 339422693837197102468343

theorem tailTrace_5949210 : CollatzResearch.WordTrace tailWord_5949210 prefixEnd_5949210 339422693837197102468343 := by
  unfold tailWord_5949210
  simp only [CollatzResearch.WordTrace]
  refine ⟨54246378694258922255425271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144657009851357126014467389 54246378694258922255425271)
  ·
    refine ⟨81369568041388383383137907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54246378694258922255425271 81369568041388383383137907)
    ·
      refine ⟨122054352062082575074706861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81369568041388383383137907 122054352062082575074706861)
      ·
        refine ⟨45770382023280965653015073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122054352062082575074706861 45770382023280965653015073)
        ·
          refine ⟨34327786517460724239761305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45770382023280965653015073 34327786517460724239761305)
          ·
            refine ⟨25745839888095543179820979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34327786517460724239761305 25745839888095543179820979)
            ·
              refine ⟨38618759832143314769731469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25745839888095543179820979 38618759832143314769731469)
              ·
                refine ⟨14482034937053743038649301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38618759832143314769731469 14482034937053743038649301)
                ·
                  refine ⟨339422693837197102468343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14482034937053743038649301 339422693837197102468343)
                  ·
                    rfl

theorem cell23_5949210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_5949210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949210 prefixEnd_5949210 := by exact prefixLift 5949210
  have htrace : WordTrace (prefixWord ++ tailWord_5949210) baseStart_5949210 baseEnd_5949210 := by
    simpa [prefixWord, tailWord_5949210, baseEnd_5949210] using wordTrace_append hprefix tailTrace_5949210
  have hstable : (prefixWord ++ tailWord_5949210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949210).length < 2 ^ (prefixWord ++ tailWord_5949210).sum := by decide
  have hdescent : baseEnd_5949210 < baseStart_5949210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949240 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_5949240 : Nat := 118140960795 + 5949240 * 2 ^ 59
def prefixEnd_5949240 : Nat := 4983230072969 + 3 ^ 40 * 5949240 * 2
def baseEnd_5949240 : Nat := 1018273216318136268279983

theorem tailTrace_5949240 : CollatzResearch.WordTrace tailWord_5949240 prefixEnd_5949240 1018273216318136268279983 := by
  unfold tailWord_5949240
  simp only [CollatzResearch.WordTrace]
  refine ⟨108493304483463502072646587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144657739311284669430195449 108493304483463502072646587)
  ·
    refine ⟨162739956725195253108969881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108493304483463502072646587 162739956725195253108969881)
    ·
      refine ⟨122054967543896439831727411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162739956725195253108969881 122054967543896439831727411)
      ·
        refine ⟨183082451315844659747591117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122054967543896439831727411 183082451315844659747591117)
        ·
          refine ⟨68655919243441747405346669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183082451315844659747591117 68655919243441747405346669)
          ·
            refine ⟨25745969716290655277005001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68655919243441747405346669 25745969716290655277005001)
            ·
              refine ⟨19309477287217991457753751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25745969716290655277005001 19309477287217991457753751)
              ·
                refine ⟨28964215930826987186630627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19309477287217991457753751 28964215930826987186630627)
                ·
                  refine ⟨43446323896240480779945941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28964215930826987186630627 43446323896240480779945941)
                  ·
                    refine ⟨1018273216318136268279983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43446323896240480779945941 1018273216318136268279983)
                    ·
                      rfl

theorem cell23_5949240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_5949240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949240 prefixEnd_5949240 := by exact prefixLift 5949240
  have htrace : WordTrace (prefixWord ++ tailWord_5949240) baseStart_5949240 baseEnd_5949240 := by
    simpa [prefixWord, tailWord_5949240, baseEnd_5949240] using wordTrace_append hprefix tailTrace_5949240
  have hstable : (prefixWord ++ tailWord_5949240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949240).length < 2 ^ (prefixWord ++ tailWord_5949240).sum := by decide
  have hdescent : baseEnd_5949240 < baseStart_5949240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949287 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5949287 : Nat := 118140960795 + 5949287 * 2 ^ 59
def prefixEnd_5949287 : Nat := 4983230072969 + 3 ^ 40 * 5949287 * 2
def baseEnd_5949287 : Nat := 1018281260848390040317411

theorem tailTrace_5949287 : CollatzResearch.WordTrace tailWord_5949287 prefixEnd_5949287 1018281260848390040317411 := by
  unfold tailWord_5949287
  simp only [CollatzResearch.WordTrace]
  refine ⟨216988323197756731172254115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144658882131837820781502743 216988323197756731172254115)
  ·
    refine ⟨325482484796635096758381173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216988323197756731172254115 325482484796635096758381173)
    ·
      refine ⟨30513982949684540321098235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325482484796635096758381173 30513982949684540321098235)
      ·
        refine ⟨45770974424526810481647353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30513982949684540321098235 45770974424526810481647353)
        ·
          refine ⟨34328230818395107861235515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45770974424526810481647353 34328230818395107861235515)
          ·
            refine ⟨51492346227592661791853273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34328230818395107861235515 51492346227592661791853273)
            ·
              refine ⟨38619259670694496343889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51492346227592661791853273 38619259670694496343889955)
              ·
                refine ⟨57928889506041744515834933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38619259670694496343889955 57928889506041744515834933)
                ·
                  refine ⟨5430833391191413548359525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57928889506041744515834933 5430833391191413548359525)
                  ·
                    refine ⟨1018281260848390040317411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430833391191413548359525 1018281260848390040317411)
                    ·
                      rfl

theorem cell23_5949287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5949287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949287 prefixEnd_5949287 := by exact prefixLift 5949287
  have htrace : WordTrace (prefixWord ++ tailWord_5949287) baseStart_5949287 baseEnd_5949287 := by
    simpa [prefixWord, tailWord_5949287, baseEnd_5949287] using wordTrace_append hprefix tailTrace_5949287
  have hstable : (prefixWord ++ tailWord_5949287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949287).length < 2 ^ (prefixWord ++ tailWord_5949287).sum := by decide
  have hdescent : baseEnd_5949287 < baseStart_5949287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949294 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5949294 : Nat := 118140960795 + 5949294 * 2 ^ 59
def prefixEnd_5949294 : Nat := 4983230072969 + 3 ^ 40 * 5949294 * 2
def baseEnd_5949294 : Nat := 3054847376909751593564701

theorem tailTrace_5949294 : CollatzResearch.WordTrace tailWord_5949294 prefixEnd_5949294 3054847376909751593564701 := by
  unfold tailWord_5949294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27123572313591421420969867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144659052339154247578505957 27123572313591421420969867)
  ·
    refine ⟨40685358470387132131454801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27123572313591421420969867 40685358470387132131454801)
    ·
      refine ⟨30514018852790349098591101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40685358470387132131454801 30514018852790349098591101)
      ·
        refine ⟨11442757069796380911971663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30514018852790349098591101 11442757069796380911971663)
        ·
          refine ⟨17164135604694571367957495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11442757069796380911971663 17164135604694571367957495)
          ·
            refine ⟨25746203407041857051936243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17164135604694571367957495 25746203407041857051936243)
            ·
              refine ⟨38619305110562785577904365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25746203407041857051936243 38619305110562785577904365)
              ·
                refine ⟨14482239416461044591714137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38619305110562785577904365 14482239416461044591714137)
                ·
                  refine ⟨10861679562345783443785603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14482239416461044591714137 10861679562345783443785603)
                  ·
                    refine ⟨16292519343518675165678405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10861679562345783443785603 16292519343518675165678405)
                    ·
                      refine ⟨3054847376909751593564701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16292519343518675165678405 3054847376909751593564701)
                      ·
                        rfl

theorem cell23_5949294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5949294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949294 prefixEnd_5949294 := by exact prefixLift 5949294
  have htrace : WordTrace (prefixWord ++ tailWord_5949294) baseStart_5949294 baseEnd_5949294 := by
    simpa [prefixWord, tailWord_5949294, baseEnd_5949294] using wordTrace_append hprefix tailTrace_5949294
  have hstable : (prefixWord ++ tailWord_5949294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949294).length < 2 ^ (prefixWord ++ tailWord_5949294).sum := by decide
  have hdescent : baseEnd_5949294 < baseStart_5949294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949317 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 6]
def baseStart_5949317 : Nat := 118140960795 + 5949317 * 2 ^ 59
def prefixEnd_5949317 : Nat := 4983230072969 + 3 ^ 40 * 5949317 * 2
def baseEnd_5949317 : Nat := 339428798551645000397455

theorem tailTrace_5949317 : CollatzResearch.WordTrace tailWord_5949317 prefixEnd_5949317 339428798551645000397455 := by
  unfold tailWord_5949317
  simp only [CollatzResearch.WordTrace]
  refine ⟨216989417387648046295846205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144659611591765364197230803 216989417387648046295846205)
  ·
    refine ⟨81371031520368017360942327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216989417387648046295846205 81371031520368017360942327)
    ·
      refine ⟨122056547280552026041413491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81371031520368017360942327 122056547280552026041413491)
      ·
        refine ⟨183084820920828039062120237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122056547280552026041413491 183084820920828039062120237)
        ·
          refine ⟨68656807845310514648295089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183084820920828039062120237 68656807845310514648295089)
          ·
            refine ⟨51492605883982885986221317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68656807845310514648295089 51492605883982885986221317)
            ·
              refine ⟨9654863603246791122416497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51492605883982885986221317 9654863603246791122416497)
              ·
                refine ⟨7241147702435093341812373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9654863603246791122416497 7241147702435093341812373)
                ·
                  refine ⟨339428798551645000397455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7241147702435093341812373 339428798551645000397455)
                  ·
                    rfl

theorem cell23_5949317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_5949317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949317 prefixEnd_5949317 := by exact prefixLift 5949317
  have htrace : WordTrace (prefixWord ++ tailWord_5949317) baseStart_5949317 baseEnd_5949317 := by
    simpa [prefixWord, tailWord_5949317, baseEnd_5949317] using wordTrace_append hprefix tailTrace_5949317
  have hstable : (prefixWord ++ tailWord_5949317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949317).length < 2 ^ (prefixWord ++ tailWord_5949317).sum := by decide
  have hdescent : baseEnd_5949317 < baseStart_5949317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949347 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 1, 5]
def baseStart_5949347 : Nat := 118140960795 + 5949347 * 2 ^ 59
def prefixEnd_5949347 : Nat := 4983230072969 + 3 ^ 40 * 5949347 * 2
def baseEnd_5949347 : Nat := 1018291530461479962067319

theorem tailTrace_5949347 : CollatzResearch.WordTrace tailWord_5949347 prefixEnd_5949347 1018291530461479962067319 := by
  unfold tailWord_5949347
  simp only [CollatzResearch.WordTrace]
  refine ⟨216990511577539361419438295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144660341051692907612958863 216990511577539361419438295)
  ·
    refine ⟨325485767366309042129157443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216990511577539361419438295 325485767366309042129157443)
    ·
      refine ⟨488228651049463563193736165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325485767366309042129157443 488228651049463563193736165)
      ·
        refine ⟨91542872071774418098825531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 488228651049463563193736165 91542872071774418098825531)
        ·
          refine ⟨137314308107661627148238297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91542872071774418098825531 137314308107661627148238297)
          ·
            refine ⟨102985731080746220361178723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137314308107661627148238297 102985731080746220361178723)
            ·
              refine ⟨154478596621119330541768085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102985731080746220361178723 154478596621119330541768085)
              ·
                refine ⟨7241184216614968619145379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154478596621119330541768085 7241184216614968619145379)
                ·
                  refine ⟨10861776324922452928718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241184216614968619145379 10861776324922452928718069)
                  ·
                    refine ⟨1018291530461479962067319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10861776324922452928718069 1018291530461479962067319)
                    ·
                      rfl

theorem cell23_5949347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 5].length) (baseStart_5949347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949347 prefixEnd_5949347 := by exact prefixLift 5949347
  have htrace : WordTrace (prefixWord ++ tailWord_5949347) baseStart_5949347 baseEnd_5949347 := by
    simpa [prefixWord, tailWord_5949347, baseEnd_5949347] using wordTrace_append hprefix tailTrace_5949347
  have hstable : (prefixWord ++ tailWord_5949347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949347).length < 2 ^ (prefixWord ++ tailWord_5949347).sum := by decide
  have hdescent : baseEnd_5949347 < baseStart_5949347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949387 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5]
def baseStart_5949387 : Nat := 118140960795 + 5949387 * 2 ^ 59
def prefixEnd_5949387 : Nat := 4983230072969 + 3 ^ 40 * 5949387 * 2
def baseEnd_5949387 : Nat := 3054895130610619729701773

theorem tailTrace_5949387 : CollatzResearch.WordTrace tailWord_5949387 prefixEnd_5949387 3054895130610619729701773 := by
  unfold tailWord_5949387
  simp only [CollatzResearch.WordTrace]
  refine ⟨216991970497394448250894415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144661313664929632167262943 216991970497394448250894415)
  ·
    refine ⟨325487955746091672376341623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216991970497394448250894415 325487955746091672376341623)
    ·
      refine ⟨488231933619137508564512435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325487955746091672376341623 488231933619137508564512435)
      ·
        refine ⟨732347900428706262846768653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488231933619137508564512435 732347900428706262846768653)
        ·
          refine ⟨274630462660764848567538245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732347900428706262846768653 274630462660764848567538245)
          ·
            refine ⟨51493211748893409106413421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274630462660764848567538245 51493211748893409106413421)
            ·
              refine ⟨19309954405835028414905033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51493211748893409106413421 19309954405835028414905033)
              ·
                refine ⟨14482465804376271311178775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19309954405835028414905033 14482465804376271311178775)
                ·
                  refine ⟨21723698706564406966768163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14482465804376271311178775 21723698706564406966768163)
                  ·
                    refine ⟨32585548059846610450152245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21723698706564406966768163 32585548059846610450152245)
                    ·
                      refine ⟨3054895130610619729701773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32585548059846610450152245 3054895130610619729701773)
                      ·
                        rfl

theorem cell23_5949387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_5949387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949387 prefixEnd_5949387 := by exact prefixLift 5949387
  have htrace : WordTrace (prefixWord ++ tailWord_5949387) baseStart_5949387 baseEnd_5949387 := by
    simpa [prefixWord, tailWord_5949387, baseEnd_5949387] using wordTrace_append hprefix tailTrace_5949387
  have hstable : (prefixWord ++ tailWord_5949387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949387).length < 2 ^ (prefixWord ++ tailWord_5949387).sum := by decide
  have hdescent : baseEnd_5949387 < baseStart_5949387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949398 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5949398 : Nat := 118140960795 + 5949398 * 2 ^ 59
def prefixEnd_5949398 : Nat := 4983230072969 + 3 ^ 40 * 5949398 * 2
def baseEnd_5949398 : Nat := 1018300259632606395554741

theorem tailTrace_5949398 : CollatzResearch.WordTrace tailWord_5949398 prefixEnd_5949398 1018300259632606395554741 := by
  unfold tailWord_5949398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13562023231272162320596553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144661581133569731419696565 13562023231272162320596553)
  ·
    refine ⟨10171517423454121740447415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13562023231272162320596553 10171517423454121740447415)
    ·
      refine ⟨15257276135181182610671123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10171517423454121740447415 15257276135181182610671123)
      ·
        refine ⟨22885914202771773916006685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15257276135181182610671123 22885914202771773916006685)
        ·
          refine ⟨8582217826039415218502507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22885914202771773916006685 8582217826039415218502507)
          ·
            refine ⟨12873326739059122827753761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8582217826039415218502507 12873326739059122827753761)
            ·
              refine ⟨9654995054294342120815321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12873326739059122827753761 9654995054294342120815321)
              ·
                refine ⟨7241246290720756590611491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9654995054294342120815321 7241246290720756590611491)
                ·
                  refine ⟨10861869436081134885917237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241246290720756590611491 10861869436081134885917237)
                  ·
                    refine ⟨1018300259632606395554741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10861869436081134885917237 1018300259632606395554741)
                    ·
                      rfl

theorem cell23_5949398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5949398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949398 prefixEnd_5949398 := by exact prefixLift 5949398
  have htrace : WordTrace (prefixWord ++ tailWord_5949398) baseStart_5949398 baseEnd_5949398 := by
    simpa [prefixWord, tailWord_5949398, baseEnd_5949398] using wordTrace_append hprefix tailTrace_5949398
  have hstable : (prefixWord ++ tailWord_5949398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949398).length < 2 ^ (prefixWord ++ tailWord_5949398).sum := by decide
  have hdescent : baseEnd_5949398 < baseStart_5949398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949401 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_5949401 : Nat := 118140960795 + 5949401 * 2 ^ 59
def prefixEnd_5949401 : Nat := 4983230072969 + 3 ^ 40 * 5949401 * 2
def baseEnd_5949401 : Nat := 3054902319339782674926709

theorem tailTrace_5949401 : CollatzResearch.WordTrace tailWord_5949401 prefixEnd_5949401 3054902319339782674926709 := by
  unfold tailWord_5949401
  simp only [CollatzResearch.WordTrace]
  refine ⟨216992481119343728641904057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144661654079562485761269371 216992481119343728641904057)
  ·
    refine ⟨162744360839507796481428043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216992481119343728641904057 162744360839507796481428043)
    ·
      refine ⟨244116541259261694722142065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162744360839507796481428043 244116541259261694722142065)
      ·
        refine ⟨183087405944446271041606549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244116541259261694722142065 183087405944446271041606549)
        ·
          refine ⟨8582222153645918955075307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183087405944446271041606549 8582222153645918955075307)
          ·
            refine ⟨12873333230468878432612961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8582222153645918955075307 12873333230468878432612961)
            ·
              refine ⟨9654999922851658824459721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12873333230468878432612961 9654999922851658824459721)
              ·
                refine ⟨7241249942138744118344791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9654999922851658824459721 7241249942138744118344791)
                ·
                  refine ⟨10861874913208116177517187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241249942138744118344791 10861874913208116177517187)
                  ·
                    refine ⟨16292812369812174266275781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10861874913208116177517187 16292812369812174266275781)
                    ·
                      refine ⟨3054902319339782674926709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16292812369812174266275781 3054902319339782674926709)
                      ·
                        rfl

theorem cell23_5949401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_5949401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949401 prefixEnd_5949401 := by exact prefixLift 5949401
  have htrace : WordTrace (prefixWord ++ tailWord_5949401) baseStart_5949401 baseEnd_5949401 := by
    simpa [prefixWord, tailWord_5949401, baseEnd_5949401] using wordTrace_append hprefix tailTrace_5949401
  have hstable : (prefixWord ++ tailWord_5949401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949401).length < 2 ^ (prefixWord ++ tailWord_5949401).sum := by decide
  have hdescent : baseEnd_5949401 < baseStart_5949401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949407 : List Nat := [1, 1, 2, 3, 4, 2, 1, 9]
def baseStart_5949407 : Nat := 118140960795 + 5949407 * 2 ^ 59
def prefixEnd_5949407 : Nat := 4983230072969 + 3 ^ 40 * 5949407 * 2
def baseEnd_5949407 : Nat := 113144644452729987090803

theorem tailTrace_5949407 : CollatzResearch.WordTrace tailWord_5949407 prefixEnd_5949407 113144644452729987090803 := by
  unfold tailWord_5949407
  simp only [CollatzResearch.WordTrace]
  refine ⟨216992699957321991666622475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144661799971547994444414983 216992699957321991666622475)
  ·
    refine ⟨325489049935982987499933713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216992699957321991666622475 325489049935982987499933713)
    ·
      refine ⟨244116787451987240624950285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325489049935982987499933713 244116787451987240624950285)
      ·
        refine ⟨91543795294495215234356357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244116787451987240624950285 91543795294495215234356357)
        ·
          refine ⟨17164461617717852856441817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91543795294495215234356357 17164461617717852856441817)
          ·
            refine ⟨12873346213288389642331363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17164461617717852856441817 12873346213288389642331363)
            ·
              refine ⟨19310019319932584463497045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12873346213288389642331363 19310019319932584463497045)
              ·
                refine ⟨113144644452729987090803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19310019319932584463497045 113144644452729987090803)
                ·
                  rfl

theorem cell23_5949407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 9].length) (baseStart_5949407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949407 prefixEnd_5949407 := by exact prefixLift 5949407
  have htrace : WordTrace (prefixWord ++ tailWord_5949407) baseStart_5949407 baseEnd_5949407 := by
    simpa [prefixWord, tailWord_5949407, baseEnd_5949407] using wordTrace_append hprefix tailTrace_5949407
  have hstable : (prefixWord ++ tailWord_5949407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949407).length < 2 ^ (prefixWord ++ tailWord_5949407).sum := by decide
  have hdescent : baseEnd_5949407 < baseStart_5949407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949451 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 3]
def baseStart_5949451 : Nat := 118140960795 + 5949451 * 2 ^ 59
def prefixEnd_5949451 : Nat := 4983230072969 + 3 ^ 40 * 5949451 * 2
def baseEnd_5949451 : Nat := 3054927993372507479301479

theorem tailTrace_5949451 : CollatzResearch.WordTrace tailWord_5949451 prefixEnd_5949451 3054927993372507479301479 := by
  unfold tailWord_5949451
  simp only [CollatzResearch.WordTrace]
  refine ⟨216994304769162587181224207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144662869846108391454149471 216994304769162587181224207)
  ·
    refine ⟨325491457153743880771836311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216994304769162587181224207 325491457153743880771836311)
    ·
      refine ⟨488237185730615821157754467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325491457153743880771836311 488237185730615821157754467)
      ·
        refine ⟨732355778595923731736631701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488237185730615821157754467 732355778595923731736631701)
        ·
          refine ⟨34329177121683924925154611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 732355778595923731736631701 34329177121683924925154611)
          ·
            refine ⟨51493765682525887387731917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34329177121683924925154611 51493765682525887387731917)
            ·
              refine ⟨19310162130947207770399469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51493765682525887387731917 19310162130947207770399469)
              ·
                refine ⟨7241310799105202913899801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19310162130947207770399469 7241310799105202913899801)
                ·
                  refine ⟨5430983099328902185424851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7241310799105202913899801 5430983099328902185424851)
                  ·
                    refine ⟨8146474648993353278137277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5430983099328902185424851 8146474648993353278137277)
                    ·
                      refine ⟨3054927993372507479301479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146474648993353278137277 3054927993372507479301479)
                      ·
                        rfl

theorem cell23_5949451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 3].length) (baseStart_5949451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949451 prefixEnd_5949451 := by exact prefixLift 5949451
  have htrace : WordTrace (prefixWord ++ tailWord_5949451) baseStart_5949451 baseEnd_5949451 := by
    simpa [prefixWord, tailWord_5949451, baseEnd_5949451] using wordTrace_append hprefix tailTrace_5949451
  have hstable : (prefixWord ++ tailWord_5949451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949451).length < 2 ^ (prefixWord ++ tailWord_5949451).sum := by decide
  have hdescent : baseEnd_5949451 < baseStart_5949451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949491 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 4, 2, 2]
def baseStart_5949491 : Nat := 118140960795 + 5949491 * 2 ^ 59
def prefixEnd_5949491 : Nat := 4983230072969 + 3 ^ 40 * 5949491 * 2
def baseEnd_5949491 : Nat := 3054948532598687322801295

theorem tailTrace_5949491 : CollatzResearch.WordTrace tailWord_5949491 prefixEnd_5949491 3054948532598687322801295 := by
  unfold tailWord_5949491
  simp only [CollatzResearch.WordTrace]
  refine ⟨216995763689017674012680327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144663842459345116008453551 216995763689017674012680327)
  ·
    refine ⟨325493645533526511019020491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216995763689017674012680327 325493645533526511019020491)
    ·
      refine ⟨488240468300289766528530737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325493645533526511019020491 488240468300289766528530737)
      ·
        refine ⟨366180351225217324896398053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488240468300289766528530737 366180351225217324896398053)
        ·
          refine ⟨68658815854728248418074635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366180351225217324896398053 68658815854728248418074635)
          ·
            refine ⟨102988223782092372627111953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68658815854728248418074635 102988223782092372627111953)
            ·
              refine ⟨77241167836569279470333965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102988223782092372627111953 77241167836569279470333965)
              ·
                refine ⟨28965437938713479801375237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77241167836569279470333965 28965437938713479801375237)
                ·
                  refine ⟨5431019613508777462757857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28965437938713479801375237 5431019613508777462757857)
                  ·
                    refine ⟨4073264710131583097068393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5431019613508777462757857 4073264710131583097068393)
                    ·
                      refine ⟨3054948532598687322801295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073264710131583097068393 3054948532598687322801295)
                      ·
                        rfl

theorem cell23_5949491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2, 2].length) (baseStart_5949491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949491 prefixEnd_5949491 := by exact prefixLift 5949491
  have htrace : WordTrace (prefixWord ++ tailWord_5949491) baseStart_5949491 baseEnd_5949491 := by
    simpa [prefixWord, tailWord_5949491, baseEnd_5949491] using wordTrace_append hprefix tailTrace_5949491
  have hstable : (prefixWord ++ tailWord_5949491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949491).length < 2 ^ (prefixWord ++ tailWord_5949491).sum := by decide
  have hdescent : baseEnd_5949491 < baseStart_5949491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949504 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_5949504 : Nat := 118140960795 + 5949504 * 2 ^ 59
def prefixEnd_5949504 : Nat := 4983230072969 + 3 ^ 40 * 5949504 * 2
def baseEnd_5949504 : Nat := 3054955207847195771938735

theorem tailTrace_5949504 : CollatzResearch.WordTrace tailWord_5949504 prefixEnd_5949504 3054955207847195771938735 := by
  unfold tailWord_5949504
  simp only [CollatzResearch.WordTrace]
  refine ⟨108498118918985288616451783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144664158558647051488602377 108498118918985288616451783)
  ·
    refine ⟨162747178378477932924677675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108498118918985288616451783 162747178378477932924677675)
    ·
      refine ⟨244120767567716899387016513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162747178378477932924677675 244120767567716899387016513)
      ·
        refine ⟨183090575675787674540262385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244120767567716899387016513 183090575675787674540262385)
        ·
          refine ⟨137317931756840755905196789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183090575675787674540262385 137317931756840755905196789)
          ·
            refine ⟨12873556102203820866112199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137317931756840755905196789 12873556102203820866112199)
            ·
              refine ⟨19310334153305731299168299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12873556102203820866112199 19310334153305731299168299)
              ·
                refine ⟨28965501229958596948752449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19310334153305731299168299 28965501229958596948752449)
                ·
                  refine ⟨21724125922468947711564337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28965501229958596948752449 21724125922468947711564337)
                  ·
                    refine ⟨16293094441851710783673253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21724125922468947711564337 16293094441851710783673253)
                    ·
                      refine ⟨3054955207847195771938735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16293094441851710783673253 3054955207847195771938735)
                      ·
                        rfl

theorem cell23_5949504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_5949504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949504 prefixEnd_5949504 := by exact prefixLift 5949504
  have htrace : WordTrace (prefixWord ++ tailWord_5949504) baseStart_5949504 baseEnd_5949504 := by
    simpa [prefixWord, tailWord_5949504, baseEnd_5949504] using wordTrace_append hprefix tailTrace_5949504
  have hstable : (prefixWord ++ tailWord_5949504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949504).length < 2 ^ (prefixWord ++ tailWord_5949504).sum := by decide
  have hdescent : baseEnd_5949504 < baseStart_5949504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949524 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_5949524 : Nat := 118140960795 + 5949524 * 2 ^ 59
def prefixEnd_5949524 : Nat := 4983230072969 + 3 ^ 40 * 5949524 * 2
def baseEnd_5949524 : Nat := 3054965477460285693688643

theorem tailTrace_5949524 : CollatzResearch.WordTrace tailWord_5949524 prefixEnd_5949524 3054965477460285693688643 := by
  unfold tailWord_5949524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108498483648949060324315813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144664644865265413765754417 108498483648949060324315813)
  ·
    refine ⟨20343465684177948810809215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108498483648949060324315813 20343465684177948810809215)
    ·
      refine ⟨30515198526266923216213823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20343465684177948810809215 30515198526266923216213823)
      ·
        refine ⟨45772797789400384824320735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30515198526266923216213823 45772797789400384824320735)
        ·
          refine ⟨68659196684100577236481103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45772797789400384824320735 68659196684100577236481103)
          ·
            refine ⟨102988795026150865854721655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68659196684100577236481103 102988795026150865854721655)
            ·
              refine ⟨154483192539226298782082483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102988795026150865854721655 154483192539226298782082483)
              ·
                refine ⟨231724788808839448173123725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154483192539226298782082483 231724788808839448173123725)
                ·
                  refine ⟨86896795803314793064921397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231724788808839448173123725 86896795803314793064921397)
                  ·
                    refine ⟨8146574606560761849836381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86896795803314793064921397 8146574606560761849836381)
                    ·
                      refine ⟨3054965477460285693688643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146574606560761849836381 3054965477460285693688643)
                      ·
                        rfl

theorem cell23_5949524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_5949524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949524 prefixEnd_5949524 := by exact prefixLift 5949524
  have htrace : WordTrace (prefixWord ++ tailWord_5949524) baseStart_5949524 baseEnd_5949524 := by
    simpa [prefixWord, tailWord_5949524, baseEnd_5949524] using wordTrace_append hprefix tailTrace_5949524
  have hstable : (prefixWord ++ tailWord_5949524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949524).length < 2 ^ (prefixWord ++ tailWord_5949524).sum := by decide
  have hdescent : baseEnd_5949524 < baseStart_5949524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949564 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_5949564 : Nat := 118140960795 + 5949564 * 2 ^ 59
def prefixEnd_5949564 : Nat := 4983230072969 + 3 ^ 40 * 5949564 * 2
def baseEnd_5949564 : Nat := 3054986016686465537188459

theorem tailTrace_5949564 : CollatzResearch.WordTrace tailWord_5949564 prefixEnd_5949564 3054986016686465537188459 := by
  unfold tailWord_5949564
  simp only [CollatzResearch.WordTrace]
  refine ⟨108499213108876603740043873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144665617478502138320058497 108499213108876603740043873)
  ·
    refine ⟨81374409831657452805032905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108499213108876603740043873 81374409831657452805032905)
    ·
      refine ⟨61030807373743089603774679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81374409831657452805032905 61030807373743089603774679)
      ·
        refine ⟨91546211060614634405662019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61030807373743089603774679 91546211060614634405662019)
        ·
          refine ⟨137319316590921951608493029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91546211060614634405662019 137319316590921951608493029)
          ·
            refine ⟨25747371860797865926592443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137319316590921951608493029 25747371860797865926592443)
            ·
              refine ⟨38621057791196798889888665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25747371860797865926592443 38621057791196798889888665)
              ·
                refine ⟨28965793343397599167416499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38621057791196798889888665 28965793343397599167416499)
                ·
                  refine ⟨43448690015096398751124749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28965793343397599167416499 43448690015096398751124749)
                  ·
                    refine ⟨16293258755661149531671781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43448690015096398751124749 16293258755661149531671781)
                    ·
                      refine ⟨3054986016686465537188459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16293258755661149531671781 3054986016686465537188459)
                      ·
                        rfl

theorem cell23_5949564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_5949564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949564 prefixEnd_5949564 := by exact prefixLift 5949564
  have htrace : WordTrace (prefixWord ++ tailWord_5949564) baseStart_5949564 baseEnd_5949564 := by
    simpa [prefixWord, tailWord_5949564, baseEnd_5949564] using wordTrace_append hprefix tailTrace_5949564
  have hstable : (prefixWord ++ tailWord_5949564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949564).length < 2 ^ (prefixWord ++ tailWord_5949564).sum := by decide
  have hdescent : baseEnd_5949564 < baseStart_5949564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949584 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_5949584 : Nat := 118140960795 + 5949584 * 2 ^ 59
def prefixEnd_5949584 : Nat := 4983230072969 + 3 ^ 40 * 5949584 * 2
def baseEnd_5949584 : Nat := 3054996286299555458938367

theorem tailTrace_5949584 : CollatzResearch.WordTrace tailWord_5949584 prefixEnd_5949584 3054996286299555458938367 := by
  unfold tailWord_5949584
  simp only [CollatzResearch.WordTrace]
  refine ⟨108499577838840375447907903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144666103785120500597210537 108499577838840375447907903)
  ·
    refine ⟨162749366758260563171861855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108499577838840375447907903 162749366758260563171861855)
    ·
      refine ⟨244124050137390844757792783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162749366758260563171861855 244124050137390844757792783)
      ·
        refine ⟨366186075206086267136689175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244124050137390844757792783 366186075206086267136689175)
        ·
          refine ⟨549279112809129400705033763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366186075206086267136689175 549279112809129400705033763)
          ·
            refine ⟨823918669213694101057550645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549279112809129400705033763 823918669213694101057550645)
            ·
              refine ⟨77242375238783821974145373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 823918669213694101057550645 77242375238783821974145373)
              ·
                refine ⟨28965890714543933240304515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77242375238783821974145373 28965890714543933240304515)
                ·
                  refine ⟨43448836071815899860456773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28965890714543933240304515 43448836071815899860456773)
                  ·
                    refine ⟨8146656763465481223835645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43448836071815899860456773 8146656763465481223835645)
                    ·
                      refine ⟨3054996286299555458938367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146656763465481223835645 3054996286299555458938367)
                      ·
                        rfl

theorem cell23_5949584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_5949584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949584 prefixEnd_5949584 := by exact prefixLift 5949584
  have htrace : WordTrace (prefixWord ++ tailWord_5949584) baseStart_5949584 baseEnd_5949584 := by
    simpa [prefixWord, tailWord_5949584, baseEnd_5949584] using wordTrace_append hprefix tailTrace_5949584
  have hstable : (prefixWord ++ tailWord_5949584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949584).length < 2 ^ (prefixWord ++ tailWord_5949584).sum := by decide
  have hdescent : baseEnd_5949584 < baseStart_5949584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949601 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5949601 : Nat := 118140960795 + 5949601 * 2 ^ 59
def prefixEnd_5949601 : Nat := 4983230072969 + 3 ^ 40 * 5949601 * 2
def baseEnd_5949601 : Nat := 3055005015470681892425789

theorem tailTrace_5949601 : CollatzResearch.WordTrace tailWord_5949601 prefixEnd_5949601 3055005015470681892425789 := by
  unfold tailWord_5949601
  simp only [CollatzResearch.WordTrace]
  refine ⟨216999775718619162799184657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144666517145746108532789771 216999775718619162799184657)
  ·
    refine ⟨162749831788964372099388493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216999775718619162799184657 162749831788964372099388493)
    ·
      refine ⟨61031186920861639537270685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162749831788964372099388493 61031186920861639537270685)
      ·
        refine ⟨22886695095323114826476507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61031186920861639537270685 22886695095323114826476507)
        ·
          refine ⟨34330042642984672239714761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22886695095323114826476507 34330042642984672239714761)
          ·
            refine ⟨25747531982238504179786071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34330042642984672239714761 25747531982238504179786071)
            ·
              refine ⟨38621297973357756269679107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25747531982238504179786071 38621297973357756269679107)
              ·
                refine ⟨57931946960036634404518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38621297973357756269679107 57931946960036634404518661)
                ·
                  refine ⟨10862240055006868950847249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57931946960036634404518661 10862240055006868950847249)
                  ·
                    refine ⟨8146680041255151713135437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10862240055006868950847249 8146680041255151713135437)
                    ·
                      refine ⟨3055005015470681892425789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146680041255151713135437 3055005015470681892425789)
                      ·
                        rfl

theorem cell23_5949601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5949601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949601 prefixEnd_5949601 := by exact prefixLift 5949601
  have htrace : WordTrace (prefixWord ++ tailWord_5949601) baseStart_5949601 baseEnd_5949601 := by
    simpa [prefixWord, tailWord_5949601, baseEnd_5949601] using wordTrace_append hprefix tailTrace_5949601
  have hstable : (prefixWord ++ tailWord_5949601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949601).length < 2 ^ (prefixWord ++ tailWord_5949601).sum := by decide
  have hdescent : baseEnd_5949601 < baseStart_5949601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949631 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 3]
def baseStart_5949631 : Nat := 118140960795 + 5949631 * 2 ^ 59
def prefixEnd_5949631 : Nat := 4983230072969 + 3 ^ 40 * 5949631 * 2
def baseEnd_5949631 : Nat := 3055020419890316775050651

theorem tailTrace_5949631 : CollatzResearch.WordTrace tailWord_5949631 prefixEnd_5949631 3055020419890316775050651 := by
  unfold tailWord_5949631
  simp only [CollatzResearch.WordTrace]
  refine ⟨217000869908510477922776747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144667246605673651948517831 217000869908510477922776747)
  ·
    refine ⟨325501304862765716884165121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217000869908510477922776747 325501304862765716884165121)
    ·
      refine ⟨244125978647074287663123841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325501304862765716884165121 244125978647074287663123841)
      ·
        refine ⟨183094483985305715747342881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244125978647074287663123841 183094483985305715747342881)
        ·
          refine ⟨137320862988979286810507161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183094483985305715747342881 137320862988979286810507161)
          ·
            refine ⟨102990647241734465107880371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137320862988979286810507161 102990647241734465107880371)
            ·
              refine ⟨154485970862601697661820557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102990647241734465107880371 154485970862601697661820557)
              ·
                refine ⟨57932239073475636623182709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154485970862601697661820557 57932239073475636623182709)
                ·
                  refine ⟨5431147413138340933423379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57932239073475636623182709 5431147413138340933423379)
                  ·
                    refine ⟨8146721119707511400135069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5431147413138340933423379 8146721119707511400135069)
                    ·
                      refine ⟨3055020419890316775050651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146721119707511400135069 3055020419890316775050651)
                      ·
                        rfl

theorem cell23_5949631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_5949631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949631 prefixEnd_5949631 := by exact prefixLift 5949631
  have htrace : WordTrace (prefixWord ++ tailWord_5949631) baseStart_5949631 baseEnd_5949631 := by
    simpa [prefixWord, tailWord_5949631, baseEnd_5949631] using wordTrace_append hprefix tailTrace_5949631
  have hstable : (prefixWord ++ tailWord_5949631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949631).length < 2 ^ (prefixWord ++ tailWord_5949631).sum := by decide
  have hdescent : baseEnd_5949631 < baseStart_5949631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949658 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_5949658 : Nat := 118140960795 + 5949658 * 2 ^ 59
def prefixEnd_5949658 : Nat := 4983230072969 + 3 ^ 40 * 5949658 * 2
def baseEnd_5949658 : Nat := 3055034283867988169413027

theorem tailTrace_5949658 : CollatzResearch.WordTrace tailWord_5949658 prefixEnd_5949658 3055034283867988169413027 := by
  unfold tailWord_5949658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54250463669853165383502407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144667903119608441022673085 54250463669853165383502407)
  ·
    refine ⟨81375695504779748075253611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54250463669853165383502407 81375695504779748075253611)
    ·
      refine ⟨122063543257169622112880417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81375695504779748075253611 122063543257169622112880417)
      ·
        refine ⟨91547657442877216584660313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122063543257169622112880417 91547657442877216584660313)
        ·
          refine ⟨68660743082157912438495235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91547657442877216584660313 68660743082157912438495235)
          ·
            refine ⟨102991114623236868657742853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68660743082157912438495235 102991114623236868657742853)
            ·
              refine ⟨19310833991856912873326785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102991114623236868657742853 19310833991856912873326785)
              ·
                refine ⟨14483125493892684654995089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19310833991856912873326785 14483125493892684654995089)
                ·
                  refine ⟨10862344120419513491246317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14483125493892684654995089 10862344120419513491246317)
                  ·
                    refine ⟨4073379045157317559217369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10862344120419513491246317 4073379045157317559217369)
                    ·
                      refine ⟨3055034283867988169413027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073379045157317559217369 3055034283867988169413027)
                      ·
                        rfl

theorem cell23_5949658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_5949658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949658 prefixEnd_5949658 := by exact prefixLift 5949658
  have htrace : WordTrace (prefixWord ++ tailWord_5949658) baseStart_5949658 baseEnd_5949658 := by
    simpa [prefixWord, tailWord_5949658, baseEnd_5949658] using wordTrace_append hprefix tailTrace_5949658
  have hstable : (prefixWord ++ tailWord_5949658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949658).length < 2 ^ (prefixWord ++ tailWord_5949658).sum := by decide
  have hdescent : baseEnd_5949658 < baseStart_5949658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949664 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_5949664 : Nat := 118140960795 + 5949664 * 2 ^ 59
def prefixEnd_5949664 : Nat := 4983230072969 + 3 ^ 40 * 5949664 * 2
def baseEnd_5949664 : Nat := 1018345788250638381979333

theorem tailTrace_5949664 : CollatzResearch.WordTrace tailWord_5949664 prefixEnd_5949664 1018345788250638381979333 := by
  unfold tailWord_5949664
  simp only [CollatzResearch.WordTrace]
  refine ⟨108501036758695462279364023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144668049011593949705818697 108501036758695462279364023)
  ·
    refine ⟨162751555138043193419046035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108501036758695462279364023 162751555138043193419046035)
    ·
      refine ⟨244127332707064790128569053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162751555138043193419046035 244127332707064790128569053)
      ·
        refine ⟨91547749765149296298213395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244127332707064790128569053 91547749765149296298213395)
        ·
          refine ⟨137321624647723944447320093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91547749765149296298213395 137321624647723944447320093)
          ·
            refine ⟨51495609242896479167745035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137321624647723944447320093 51495609242896479167745035)
            ·
              refine ⟨77243413864344718751617553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51495609242896479167745035 77243413864344718751617553)
              ·
                refine ⟨57932560398258539063713165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77243413864344718751617553 57932560398258539063713165)
                ·
                  refine ⟨21724710149346952148892437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57932560398258539063713165 21724710149346952148892437)
                  ·
                    refine ⟨1018345788250638381979333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21724710149346952148892437 1018345788250638381979333)
                    ·
                      rfl

theorem cell23_5949664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_5949664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949664 prefixEnd_5949664 := by exact prefixLift 5949664
  have htrace : WordTrace (prefixWord ++ tailWord_5949664) baseStart_5949664 baseEnd_5949664 := by
    simpa [prefixWord, tailWord_5949664, baseEnd_5949664] using wordTrace_append hprefix tailTrace_5949664
  have hstable : (prefixWord ++ tailWord_5949664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949664).length < 2 ^ (prefixWord ++ tailWord_5949664).sum := by decide
  have hdescent : baseEnd_5949664 < baseStart_5949664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949665 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_5949665 : Nat := 118140960795 + 5949665 * 2 ^ 59
def prefixEnd_5949665 : Nat := 4983230072969 + 3 ^ 40 * 5949665 * 2
def baseEnd_5949665 : Nat := 3055037878232569642025495

theorem tailTrace_5949665 : CollatzResearch.WordTrace tailWord_5949665 prefixEnd_5949665 3055037878232569642025495 := by
  unfold tailWord_5949665
  simp only [CollatzResearch.WordTrace]
  refine ⟨217002109990387301729514449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144668073326924867819676299 217002109990387301729514449)
  ·
    refine ⟨162751582492790476297135837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217002109990387301729514449 162751582492790476297135837)
    ·
      refine ⟨61031843434796428611425939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162751582492790476297135837 61031843434796428611425939)
      ·
        refine ⟨91547765152194642917138909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61031843434796428611425939 91547765152194642917138909)
        ·
          refine ⟨34330411932072991093927091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91547765152194642917138909 34330411932072991093927091)
          ·
            refine ⟨51495617898109486640890637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34330411932072991093927091 51495617898109486640890637)
            ·
              refine ⟨19310856711791057490333989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51495617898109486640890637 19310856711791057490333989)
              ·
                refine ⟨3620785633460823279437623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19310856711791057490333989 3620785633460823279437623)
                ·
                  refine ⟨5431178450191234919156435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620785633460823279437623 5431178450191234919156435)
                  ·
                    refine ⟨8146767675286852378734653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5431178450191234919156435 8146767675286852378734653)
                    ·
                      refine ⟨3055037878232569642025495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146767675286852378734653 3055037878232569642025495)
                      ·
                        rfl

theorem cell23_5949665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_5949665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949665 prefixEnd_5949665 := by exact prefixLift 5949665
  have htrace : WordTrace (prefixWord ++ tailWord_5949665) baseStart_5949665 baseEnd_5949665 := by
    simpa [prefixWord, tailWord_5949665, baseEnd_5949665] using wordTrace_append hprefix tailTrace_5949665
  have hstable : (prefixWord ++ tailWord_5949665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949665).length < 2 ^ (prefixWord ++ tailWord_5949665).sum := by decide
  have hdescent : baseEnd_5949665 < baseStart_5949665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949698 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_5949698 : Nat := 118140960795 + 5949698 * 2 ^ 59
def prefixEnd_5949698 : Nat := 4983230072969 + 3 ^ 40 * 5949698 * 2
def baseEnd_5949698 : Nat := 1018351607698056004304281

theorem tailTrace_5949698 : CollatzResearch.WordTrace tailWord_5949698 prefixEnd_5949698 1018351607698056004304281 := by
  unfold tailWord_5949698
  simp only [CollatzResearch.WordTrace]
  refine ⟨54250828399816937091366437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144668875732845165576977165 54250828399816937091366437)
  ·
    refine ⟨10172030324965675704631207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54250828399816937091366437 10172030324965675704631207)
    ·
      refine ⟨15258045487448513556946811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10172030324965675704631207 15258045487448513556946811)
      ·
        refine ⟨22887068231172770335420217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258045487448513556946811 22887068231172770335420217)
        ·
          refine ⟨17165301173379577751565163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22887068231172770335420217 17165301173379577751565163)
          ·
            refine ⟨25747951760069366627347745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17165301173379577751565163 25747951760069366627347745)
            ·
              refine ⟨19310963820052024970510809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25747951760069366627347745 19310963820052024970510809)
              ·
                refine ⟨14483222865039018727883107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19310963820052024970510809 14483222865039018727883107)
                ·
                  refine ⟨21724834297558528091824661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14483222865039018727883107 21724834297558528091824661)
                  ·
                    refine ⟨1018351607698056004304281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21724834297558528091824661 1018351607698056004304281)
                    ·
                      rfl

theorem cell23_5949698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_5949698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949698 prefixEnd_5949698 := by exact prefixLift 5949698
  have htrace : WordTrace (prefixWord ++ tailWord_5949698) baseStart_5949698 baseEnd_5949698 := by
    simpa [prefixWord, tailWord_5949698, baseEnd_5949698] using wordTrace_append hprefix tailTrace_5949698
  have hstable : (prefixWord ++ tailWord_5949698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949698).length < 2 ^ (prefixWord ++ tailWord_5949698).sum := by decide
  have hdescent : baseEnd_5949698 < baseStart_5949698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949705 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 1, 1, 4]
def baseStart_5949705 : Nat := 118140960795 + 5949705 * 2 ^ 59
def prefixEnd_5949705 : Nat := 4983230072969 + 3 ^ 40 * 5949705 * 2
def baseEnd_5949705 : Nat := 3055058417458749485525311

theorem tailTrace_5949705 : CollatzResearch.WordTrace tailWord_5949705 prefixEnd_5949705 3055058417458749485525311 := by
  unfold tailWord_5949705
  simp only [CollatzResearch.WordTrace]
  refine ⟨217003568910242388560970569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144669045940161592373980379 217003568910242388560970569)
  ·
    refine ⟨162752676682681791420727927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217003568910242388560970569 162752676682681791420727927)
    ·
      refine ⟨244129015024022687131091891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162752676682681791420727927 244129015024022687131091891)
      ·
        refine ⟨366193522536034030696637837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244129015024022687131091891 366193522536034030696637837)
        ·
          refine ⟨137322570951012761511239189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366193522536034030696637837 137322570951012761511239189)
          ·
            refine ⟨6436995513328723195839337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137322570951012761511239189 6436995513328723195839337)
            ·
              refine ⟨4827746634996542396879503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436995513328723195839337 4827746634996542396879503)
              ·
                refine ⟨7241619952494813595319255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827746634996542396879503 7241619952494813595319255)
                ·
                  refine ⟨10862429928742220392978883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241619952494813595319255 10862429928742220392978883)
                  ·
                    refine ⟨16293644893113330589468325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10862429928742220392978883 16293644893113330589468325)
                    ·
                      refine ⟨3055058417458749485525311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16293644893113330589468325 3055058417458749485525311)
                      ·
                        rfl

theorem cell23_5949705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 1, 4].length) (baseStart_5949705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949705 prefixEnd_5949705 := by exact prefixLift 5949705
  have htrace : WordTrace (prefixWord ++ tailWord_5949705) baseStart_5949705 baseEnd_5949705 := by
    simpa [prefixWord, tailWord_5949705, baseEnd_5949705] using wordTrace_append hprefix tailTrace_5949705
  have hstable : (prefixWord ++ tailWord_5949705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949705).length < 2 ^ (prefixWord ++ tailWord_5949705).sum := by decide
  have hdescent : baseEnd_5949705 < baseStart_5949705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949708 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_5949708 : Nat := 118140960795 + 5949708 * 2 ^ 59
def prefixEnd_5949708 : Nat := 4983230072969 + 3 ^ 40 * 5949708 * 2
def baseEnd_5949708 : Nat := 3055059957900712973787797

theorem tailTrace_5949708 : CollatzResearch.WordTrace tailWord_5949708 prefixEnd_5949708 3055059957900712973787797 := by
  unfold tailWord_5949708
  simp only [CollatzResearch.WordTrace]
  refine ⟨108501839164615760036664889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144669118886154346715553185 108501839164615760036664889)
  ·
    refine ⟨81376379373461820027498667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108501839164615760036664889 81376379373461820027498667)
    ·
      refine ⟨122064569060192730041248001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81376379373461820027498667 122064569060192730041248001)
      ·
        refine ⟨91548426795144547530936001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122064569060192730041248001 91548426795144547530936001)
        ·
          refine ⟨68661320096358410648202001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91548426795144547530936001 68661320096358410648202001)
          ·
            refine ⟨51495990072268807986151501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68661320096358410648202001 51495990072268807986151501)
            ·
              refine ⟨19310996277100802994806813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51495990072268807986151501 19310996277100802994806813)
              ·
                refine ⟨7241623603912801123052555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19310996277100802994806813 7241623603912801123052555)
                ·
                  refine ⟨10862435405869201684578833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241623603912801123052555 10862435405869201684578833)
                  ·
                    refine ⟨8146826554401901263434125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10862435405869201684578833 8146826554401901263434125)
                    ·
                      refine ⟨3055059957900712973787797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146826554401901263434125 3055059957900712973787797)
                      ·
                        rfl

theorem cell23_5949708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_5949708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949708 prefixEnd_5949708 := by exact prefixLift 5949708
  have htrace : WordTrace (prefixWord ++ tailWord_5949708) baseStart_5949708 baseEnd_5949708 := by
    simpa [prefixWord, tailWord_5949708, baseEnd_5949708] using wordTrace_append hprefix tailTrace_5949708
  have hstable : (prefixWord ++ tailWord_5949708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949708).length < 2 ^ (prefixWord ++ tailWord_5949708).sum := by decide
  have hdescent : baseEnd_5949708 < baseStart_5949708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949722 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_5949722 : Nat := 118140960795 + 5949722 * 2 ^ 59
def prefixEnd_5949722 : Nat := 4983230072969 + 3 ^ 40 * 5949722 * 2
def baseEnd_5949722 : Nat := 3055067146629875919012733

theorem tailTrace_5949722 : CollatzResearch.WordTrace tailWord_5949722 prefixEnd_5949722 3055067146629875919012733 := by
  unfold tailWord_5949722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54251047237795200116084855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144669459300787200309559613 54251047237795200116084855)
  ·
    refine ⟨81376570856692800174127283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54251047237795200116084855 81376570856692800174127283)
    ·
      refine ⟨122064856285039200261190925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81376570856692800174127283 122064856285039200261190925)
      ·
        refine ⟨45774321106889700097946597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122064856285039200261190925 45774321106889700097946597)
        ·
          refine ⟨8582685207541818768364987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45774321106889700097946597 8582685207541818768364987)
          ·
            refine ⟨12874027811312728152547481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8582685207541818768364987 12874027811312728152547481)
            ·
              refine ⟨9655520858484546114410611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12874027811312728152547481 9655520858484546114410611)
              ·
                refine ⟨14483281287726819171615917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9655520858484546114410611 14483281287726819171615917)
                ·
                  refine ⟨5431230482897557189355969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14483281287726819171615917 5431230482897557189355969)
                  ·
                    refine ⟨4073422862173167892016977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5431230482897557189355969 4073422862173167892016977)
                    ·
                      refine ⟨3055067146629875919012733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073422862173167892016977 3055067146629875919012733)
                      ·
                        rfl

theorem cell23_5949722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_5949722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949722 prefixEnd_5949722 := by exact prefixLift 5949722
  have htrace : WordTrace (prefixWord ++ tailWord_5949722) baseStart_5949722 baseEnd_5949722 := by
    simpa [prefixWord, tailWord_5949722, baseEnd_5949722] using wordTrace_append hprefix tailTrace_5949722
  have hstable : (prefixWord ++ tailWord_5949722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949722).length < 2 ^ (prefixWord ++ tailWord_5949722).sum := by decide
  have hdescent : baseEnd_5949722 < baseStart_5949722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949744 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_5949744 : Nat := 118140960795 + 5949744 * 2 ^ 59
def prefixEnd_5949744 : Nat := 4983230072969 + 3 ^ 40 * 5949744 * 2
def baseEnd_5949744 : Nat := 3055078443204274832937631

theorem tailTrace_5949744 : CollatzResearch.WordTrace tailWord_5949744 prefixEnd_5949744 3055078443204274832937631 := by
  unfold tailWord_5949744
  simp only [CollatzResearch.WordTrace]
  refine ⟨108502495678550549110820143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144669994238067398814426857 108502495678550549110820143)
  ·
    refine ⟨162753743517825823666230215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108502495678550549110820143 162753743517825823666230215)
    ·
      refine ⟨244130615276738735499345323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162753743517825823666230215 244130615276738735499345323)
      ·
        refine ⟨366195922915108103249017985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244130615276738735499345323 366195922915108103249017985)
        ·
          refine ⟨274646942186331077436763489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366195922915108103249017985 274646942186331077436763489)
          ·
            refine ⟨205985206639748308077572617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274646942186331077436763489 205985206639748308077572617)
            ·
              refine ⟨154488904979811231058179463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205985206639748308077572617 154488904979811231058179463)
              ·
                refine ⟨231733357469716846587269195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154488904979811231058179463 231733357469716846587269195)
                ·
                  refine ⟨347600036204575269880903793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231733357469716846587269195 347600036204575269880903793)
                  ·
                    refine ⟨260700027153431452410677845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347600036204575269880903793 260700027153431452410677845)
                    ·
                      refine ⟨3055078443204274832937631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260700027153431452410677845 3055078443204274832937631)
                      ·
                        rfl

theorem cell23_5949744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_5949744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949744 prefixEnd_5949744 := by exact prefixLift 5949744
  have htrace : WordTrace (prefixWord ++ tailWord_5949744) baseStart_5949744 baseEnd_5949744 := by
    simpa [prefixWord, tailWord_5949744, baseEnd_5949744] using wordTrace_append hprefix tailTrace_5949744
  have hstable : (prefixWord ++ tailWord_5949744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949744).length < 2 ^ (prefixWord ++ tailWord_5949744).sum := by decide
  have hdescent : baseEnd_5949744 < baseStart_5949744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949745 : List Nat := [1, 2, 2, 3, 5, 1, 2, 7]
def baseStart_5949745 : Nat := 118140960795 + 5949745 * 2 ^ 59
def prefixEnd_5949745 : Nat := 4983230072969 + 3 ^ 40 * 5949745 * 2
def baseEnd_5949745 : Nat := 113151072469812197371301

theorem tailTrace_5949745 : CollatzResearch.WordTrace tailWord_5949745 prefixEnd_5949745 113151072469812197371301 := by
  unfold tailWord_5949745
  simp only [CollatzResearch.WordTrace]
  refine ⟨217005027830097475392426689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144670018553398316928284459 217005027830097475392426689)
  ·
    refine ⟨162753770872573106544320017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217005027830097475392426689 162753770872573106544320017)
    ·
      refine ⟨122065328154429829908240013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162753770872573106544320017 122065328154429829908240013)
      ·
        refine ⟨45774498057911186215590005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122065328154429829908240013 45774498057911186215590005)
        ·
          refine ⟨4291359192929173707711563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45774498057911186215590005 4291359192929173707711563)
          ·
            refine ⟨6437038789393760561567345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291359192929173707711563 6437038789393760561567345)
            ·
              refine ⟨4827779092045320421175509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437038789393760561567345 4827779092045320421175509)
              ·
                refine ⟨113151072469812197371301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4827779092045320421175509 113151072469812197371301)
                ·
                  rfl

theorem cell23_5949745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 7].length) (baseStart_5949745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949745 prefixEnd_5949745 := by exact prefixLift 5949745
  have htrace : WordTrace (prefixWord ++ tailWord_5949745) baseStart_5949745 baseEnd_5949745 := by
    simpa [prefixWord, tailWord_5949745, baseEnd_5949745] using wordTrace_append hprefix tailTrace_5949745
  have hstable : (prefixWord ++ tailWord_5949745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949745).length < 2 ^ (prefixWord ++ tailWord_5949745).sum := by decide
  have hdescent : baseEnd_5949745 < baseStart_5949745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949791 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_5949791 : Nat := 118140960795 + 5949791 * 2 ^ 59
def prefixEnd_5949791 : Nat := 4983230072969 + 3 ^ 40 * 5949791 * 2
def baseEnd_5949791 : Nat := 3055102576795036149049915

theorem tailTrace_5949791 : CollatzResearch.WordTrace tailWord_5949791 prefixEnd_5949791 3055102576795036149049915 := by
  unfold tailWord_5949791
  simp only [CollatzResearch.WordTrace]
  refine ⟨217006705587930825248601227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144671137058620550165734151 217006705587930825248601227)
  ·
    refine ⟨325510058381896237872901841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217006705587930825248601227 325510058381896237872901841)
    ·
      refine ⟨244132543786422178404676381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325510058381896237872901841 244132543786422178404676381)
      ·
        refine ⟨91549703919908316901753643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244132543786422178404676381 91549703919908316901753643)
        ·
          refine ⟨137324555879862475352630465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91549703919908316901753643 137324555879862475352630465)
          ·
            refine ⟨102993416909896856514472849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137324555879862475352630465 102993416909896856514472849)
            ·
              refine ⟨77245062682422642385854637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102993416909896856514472849 77245062682422642385854637)
              ·
                refine ⟨28966898505908490894695489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77245062682422642385854637 28966898505908490894695489)
                ·
                  refine ⟨21725173879431368171021617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28966898505908490894695489 21725173879431368171021617)
                  ·
                    refine ⟨16293880409573526128266213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21725173879431368171021617 16293880409573526128266213)
                    ·
                      refine ⟨3055102576795036149049915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16293880409573526128266213 3055102576795036149049915)
                      ·
                        rfl

theorem cell23_5949791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_5949791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949791 prefixEnd_5949791 := by exact prefixLift 5949791
  have htrace : WordTrace (prefixWord ++ tailWord_5949791) baseStart_5949791 baseEnd_5949791 := by
    simpa [prefixWord, tailWord_5949791, baseEnd_5949791] using wordTrace_append hprefix tailTrace_5949791
  have hstable : (prefixWord ++ tailWord_5949791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949791).length < 2 ^ (prefixWord ++ tailWord_5949791).sum := by decide
  have hdescent : baseEnd_5949791 < baseStart_5949791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949811 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3]
def baseStart_5949811 : Nat := 118140960795 + 5949811 * 2 ^ 59
def prefixEnd_5949811 : Nat := 4983230072969 + 3 ^ 40 * 5949811 * 2
def baseEnd_5949811 : Nat := 3055112846408126070799823

theorem tailTrace_5949811 : CollatzResearch.WordTrace tailWord_5949811 prefixEnd_5949811 3055112846408126070799823 := by
  unfold tailWord_5949811
  simp only [CollatzResearch.WordTrace]
  refine ⟨217007435047858368664329287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144671623365238912442886191 217007435047858368664329287)
  ·
    refine ⟨325511152571787552996493931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217007435047858368664329287 325511152571787552996493931)
    ·
      refine ⟨488266728857681329494740897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325511152571787552996493931 488266728857681329494740897)
      ·
        refine ⟨366200046643260997121055673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488266728857681329494740897 366200046643260997121055673)
        ·
          refine ⟨274650034982445747840791755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366200046643260997121055673 274650034982445747840791755)
          ·
            refine ⟨411975052473668621761187633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274650034982445747840791755 411975052473668621761187633)
            ·
              refine ⟨308981289355251466320890725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411975052473668621761187633 308981289355251466320890725)
              ·
                refine ⟨57933991754109649935167011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308981289355251466320890725 57933991754109649935167011)
                ·
                  refine ⟨86900987631164474902750517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57933991754109649935167011 86900987631164474902750517)
                  ·
                    refine ⟨8146967590421669522132861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86900987631164474902750517 8146967590421669522132861)
                    ·
                      refine ⟨3055112846408126070799823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146967590421669522132861 3055112846408126070799823)
                      ·
                        rfl

theorem cell23_5949811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_5949811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949811 prefixEnd_5949811 := by exact prefixLift 5949811
  have htrace : WordTrace (prefixWord ++ tailWord_5949811) baseStart_5949811 baseEnd_5949811 := by
    simpa [prefixWord, tailWord_5949811, baseEnd_5949811] using wordTrace_append hprefix tailTrace_5949811
  have hstable : (prefixWord ++ tailWord_5949811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949811).length < 2 ^ (prefixWord ++ tailWord_5949811).sum := by decide
  have hdescent : baseEnd_5949811 < baseStart_5949811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949828 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_5949828 : Nat := 118140960795 + 5949828 * 2 ^ 59
def prefixEnd_5949828 : Nat := 4983230072969 + 3 ^ 40 * 5949828 * 2
def baseEnd_5949828 : Nat := 3055121575579252504287245

theorem tailTrace_5949828 : CollatzResearch.WordTrace tailWord_5949828 prefixEnd_5949828 3055121575579252504287245 := by
  unfold tailWord_5949828
  simp only [CollatzResearch.WordTrace]
  refine ⟨108504027544398390283849069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144672036725864520378465425 108504027544398390283849069)
  ·
    refine ⟨40689010329149396356443401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108504027544398390283849069 40689010329149396356443401)
    ·
      refine ⟨30516757746862047267332551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40689010329149396356443401 30516757746862047267332551)
      ·
        refine ⟨45775136620293070900998827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30516757746862047267332551 45775136620293070900998827)
        ·
          refine ⟨68662704930439606351498241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45775136620293070900998827 68662704930439606351498241)
          ·
            refine ⟨51497028697829704763623681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68662704930439606351498241 51497028697829704763623681)
            ·
              refine ⟨38622771523372278572717761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51497028697829704763623681 38622771523372278572717761)
              ·
                refine ⟨28967078642529208929538321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38622771523372278572717761 28967078642529208929538321)
                ·
                  refine ⟨21725308981896906697153741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28967078642529208929538321 21725308981896906697153741)
                  ·
                    refine ⟨8146990868211340011432653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21725308981896906697153741 8146990868211340011432653)
                    ·
                      refine ⟨3055121575579252504287245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8146990868211340011432653 3055121575579252504287245)
                      ·
                        rfl

theorem cell23_5949828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_5949828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949828 prefixEnd_5949828 := by exact prefixLift 5949828
  have htrace : WordTrace (prefixWord ++ tailWord_5949828) baseStart_5949828 baseEnd_5949828 := by
    simpa [prefixWord, tailWord_5949828, baseEnd_5949828] using wordTrace_append hprefix tailTrace_5949828
  have hstable : (prefixWord ++ tailWord_5949828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949828).length < 2 ^ (prefixWord ++ tailWord_5949828).sum := by decide
  have hdescent : baseEnd_5949828 < baseStart_5949828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949835 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 5]
def baseStart_5949835 : Nat := 118140960795 + 5949835 * 2 ^ 59
def prefixEnd_5949835 : Nat := 4983230072969 + 3 ^ 40 * 5949835 * 2
def baseEnd_5949835 : Nat := 339458352215981552988857

theorem tailTrace_5949835 : CollatzResearch.WordTrace tailWord_5949835 prefixEnd_5949835 339458352215981552988857 := by
  unfold tailWord_5949835
  simp only [CollatzResearch.WordTrace]
  refine ⟨217008310399771420763202959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144672206933180947175468639 217008310399771420763202959)
  ·
    refine ⟨325512465599657131144804439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217008310399771420763202959 325512465599657131144804439)
    ·
      refine ⟨488268698399485696717206659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325512465599657131144804439 488268698399485696717206659)
      ·
        refine ⟨732403047599228545075809989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488268698399485696717206659 732403047599228545075809989)
        ·
          refine ⟨137325571424855352201714373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 732403047599228545075809989 137325571424855352201714373)
          ·
            refine ⟨25748544642160378537821445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137325571424855352201714373 25748544642160378537821445)
            ·
              refine ⟨4827852120405070975841521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25748544642160378537821445 4827852120405070975841521)
              ·
                refine ⟨3620889090303803231881141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827852120405070975841521 3620889090303803231881141)
                ·
                  refine ⟨339458352215981552988857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620889090303803231881141 339458352215981552988857)
                  ·
                    rfl

theorem cell23_5949835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 5].length) (baseStart_5949835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949835 prefixEnd_5949835 := by exact prefixLift 5949835
  have htrace : WordTrace (prefixWord ++ tailWord_5949835) baseStart_5949835 baseEnd_5949835 := by
    simpa [prefixWord, tailWord_5949835, baseEnd_5949835] using wordTrace_append hprefix tailTrace_5949835
  have hstable : (prefixWord ++ tailWord_5949835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949835).length < 2 ^ (prefixWord ++ tailWord_5949835).sum := by decide
  have hdescent : baseEnd_5949835 < baseStart_5949835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949868 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_5949868 : Nat := 118140960795 + 5949868 * 2 ^ 59
def prefixEnd_5949868 : Nat := 4983230072969 + 3 ^ 40 * 5949868 * 2
def baseEnd_5949868 : Nat := 3055142114805432347787061

theorem tailTrace_5949868 : CollatzResearch.WordTrace tailWord_5949868 prefixEnd_5949868 3055142114805432347787061 := by
  unfold tailWord_5949868
  simp only [CollatzResearch.WordTrace]
  refine ⟨108504757004325933699577129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144673009339101244932769505 108504757004325933699577129)
  ·
    refine ⟨81378567753244450274682847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108504757004325933699577129 81378567753244450274682847)
    ·
      refine ⟨122067851629866675412024271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81378567753244450274682847 122067851629866675412024271)
      ·
        refine ⟨183101777444800013118036407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122067851629866675412024271 183101777444800013118036407)
        ·
          refine ⟨274652666167200019677054611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183101777444800013118036407 274652666167200019677054611)
          ·
            refine ⟨411978999250800029515581917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274652666167200019677054611 411978999250800029515581917)
            ·
              refine ⟨154492124719050011068343219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411978999250800029515581917 154492124719050011068343219)
              ·
                refine ⟨231738187078575016602514829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154492124719050011068343219 231738187078575016602514829)
                ·
                  refine ⟨86901820154465631225943061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231738187078575016602514829 86901820154465631225943061)
                  ·
                    refine ⟨4073522819740576463716081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86901820154465631225943061 4073522819740576463716081)
                    ·
                      refine ⟨3055142114805432347787061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073522819740576463716081 3055142114805432347787061)
                      ·
                        rfl

theorem cell23_5949868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_5949868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949868 prefixEnd_5949868 := by exact prefixLift 5949868
  have htrace : WordTrace (prefixWord ++ tailWord_5949868) baseStart_5949868 baseEnd_5949868 := by
    simpa [prefixWord, tailWord_5949868, baseEnd_5949868] using wordTrace_append hprefix tailTrace_5949868
  have hstable : (prefixWord ++ tailWord_5949868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949868).length < 2 ^ (prefixWord ++ tailWord_5949868).sum := by decide
  have hdescent : baseEnd_5949868 < baseStart_5949868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949885 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_5949885 : Nat := 118140960795 + 5949885 * 2 ^ 59
def prefixEnd_5949885 : Nat := 4983230072969 + 3 ^ 40 * 5949885 * 2
def baseEnd_5949885 : Nat := 3055150843976558781274483

theorem tailTrace_5949885 : CollatzResearch.WordTrace tailWord_5949885 prefixEnd_5949885 3055150843976558781274483 := by
  unfold tailWord_5949885
  simp only [CollatzResearch.WordTrace]
  refine ⟨217010134049590279302523109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144673422699726852868348739 217010134049590279302523109)
  ·
    refine ⟨40689400134298177369223083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217010134049590279302523109 40689400134298177369223083)
    ·
      refine ⟨61034100201447266053834625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40689400134298177369223083 61034100201447266053834625)
      ·
        refine ⟨45775575151085449540375969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61034100201447266053834625 45775575151085449540375969)
        ·
          refine ⟨34331681363314087155281977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45775575151085449540375969 34331681363314087155281977)
          ·
            refine ⟨25748761022485565366461483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34331681363314087155281977 25748761022485565366461483)
            ·
              refine ⟨38623141533728348049692225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25748761022485565366461483 38623141533728348049692225)
              ·
                refine ⟨28967356150296261037269169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38623141533728348049692225 28967356150296261037269169)
                ·
                  refine ⟨21725517112722195777951877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28967356150296261037269169 21725517112722195777951877)
                  ·
                    refine ⟨4073534458635411708365977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21725517112722195777951877 4073534458635411708365977)
                    ·
                      refine ⟨3055150843976558781274483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073534458635411708365977 3055150843976558781274483)
                      ·
                        rfl

theorem cell23_5949885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_5949885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949885 prefixEnd_5949885 := by exact prefixLift 5949885
  have htrace : WordTrace (prefixWord ++ tailWord_5949885) baseStart_5949885 baseEnd_5949885 := by
    simpa [prefixWord, tailWord_5949885, baseEnd_5949885] using wordTrace_append hprefix tailTrace_5949885
  have hstable : (prefixWord ++ tailWord_5949885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949885).length < 2 ^ (prefixWord ++ tailWord_5949885).sum := by decide
  have hdescent : baseEnd_5949885 < baseStart_5949885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949888 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_5949888 : Nat := 118140960795 + 5949888 * 2 ^ 59
def prefixEnd_5949888 : Nat := 4983230072969 + 3 ^ 40 * 5949888 * 2
def baseEnd_5949888 : Nat := 3055152384418522269536969

theorem tailTrace_5949888 : CollatzResearch.WordTrace tailWord_5949888 prefixEnd_5949888 3055152384418522269536969 := by
  unfold tailWord_5949888
  simp only [CollatzResearch.WordTrace]
  refine ⟨108505121734289705407441159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144673495645719607209921545 108505121734289705407441159)
  ·
    refine ⟨162757682601434558111161739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108505121734289705407441159 162757682601434558111161739)
    ·
      refine ⟨244136523902151837166742609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162757682601434558111161739 244136523902151837166742609)
      ·
        refine ⟨183102392926613877875056957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244136523902151837166742609 183102392926613877875056957)
        ·
          refine ⟨68663397347480204203146359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183102392926613877875056957 68663397347480204203146359)
          ·
            refine ⟨102995096021220306304719539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68663397347480204203146359 102995096021220306304719539)
            ·
              refine ⟨154492644031830459457079309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102995096021220306304719539 154492644031830459457079309)
              ·
                refine ⟨57934741511936422296404741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154492644031830459457079309 57934741511936422296404741)
                ·
                  refine ⟨10862764033488079180575889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57934741511936422296404741 10862764033488079180575889)
                  ·
                    refine ⟨8147073025116059385431917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10862764033488079180575889 8147073025116059385431917)
                    ·
                      refine ⟨3055152384418522269536969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147073025116059385431917 3055152384418522269536969)
                      ·
                        rfl

theorem cell23_5949888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_5949888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949888 prefixEnd_5949888 := by exact prefixLift 5949888
  have htrace : WordTrace (prefixWord ++ tailWord_5949888) baseStart_5949888 baseEnd_5949888 := by
    simpa [prefixWord, tailWord_5949888, baseEnd_5949888] using wordTrace_append hprefix tailTrace_5949888
  have hstable : (prefixWord ++ tailWord_5949888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949888).length < 2 ^ (prefixWord ++ tailWord_5949888).sum := by decide
  have hdescent : baseEnd_5949888 < baseStart_5949888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949895 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 3, 4]
def baseStart_5949895 : Nat := 118140960795 + 5949895 * 2 ^ 59
def prefixEnd_5949895 : Nat := 4983230072969 + 3 ^ 40 * 5949895 * 2
def baseEnd_5949895 : Nat := 1018385326261034580716479

theorem tailTrace_5949895 : CollatzResearch.WordTrace tailWord_5949895 prefixEnd_5949895 1018385326261034580716479 := by
  unfold tailWord_5949895
  simp only [CollatzResearch.WordTrace]
  refine ⟨217010498779554051010387139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144673665853036034006924759 217010498779554051010387139)
  ·
    refine ⟨325515748169331076515580709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217010498779554051010387139 325515748169331076515580709)
    ·
      refine ⟨61034202781749576846671383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325515748169331076515580709 61034202781749576846671383)
      ·
        refine ⟨91551304172624365270007075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61034202781749576846671383 91551304172624365270007075)
        ·
          refine ⟨137326956258936547905010613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91551304172624365270007075 137326956258936547905010613)
          ·
            refine ⟨12874402149275301366094745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137326956258936547905010613 12874402149275301366094745)
            ·
              refine ⟨9655801611956476024571059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12874402149275301366094745 9655801611956476024571059)
              ·
                refine ⟨14483702417934714036856589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9655801611956476024571059 14483702417934714036856589)
                ·
                  refine ⟨5431388406725517763821221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14483702417934714036856589 5431388406725517763821221)
                  ·
                    refine ⟨1018385326261034580716479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431388406725517763821221 1018385326261034580716479)
                    ·
                      rfl

theorem cell23_5949895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_5949895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949895 prefixEnd_5949895 := by exact prefixLift 5949895
  have htrace : WordTrace (prefixWord ++ tailWord_5949895) baseStart_5949895 baseEnd_5949895 := by
    simpa [prefixWord, tailWord_5949895, baseEnd_5949895] using wordTrace_append hprefix tailTrace_5949895
  have hstable : (prefixWord ++ tailWord_5949895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949895).length < 2 ^ (prefixWord ++ tailWord_5949895).sum := by decide
  have hdescent : baseEnd_5949895 < baseStart_5949895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949945 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 4, 3, 2]
def baseStart_5949945 : Nat := 118140960795 + 5949945 * 2 ^ 59
def prefixEnd_5949945 : Nat := 4983230072969 + 3 ^ 40 * 5949945 * 2
def baseEnd_5949945 : Nat := 3055181652815828546524207

theorem tailTrace_5949945 : CollatzResearch.WordTrace tailWord_5949945 prefixEnd_5949945 3055181652815828546524207 := by
  unfold tailWord_5949945
  simp only [CollatzResearch.WordTrace]
  refine ⟨217012322429372909549707289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144674881619581939699804859 217012322429372909549707289)
  ·
    refine ⟨162759241822029682162280467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217012322429372909549707289 162759241822029682162280467)
    ·
      refine ⟨244138862733044523243420701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162759241822029682162280467 244138862733044523243420701)
      ·
        refine ⟨91552073524891696216282763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244138862733044523243420701 91552073524891696216282763)
        ·
          refine ⟨137328110287337544324424145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91552073524891696216282763 137328110287337544324424145)
          ·
            refine ⟨102996082715503158243318109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137328110287337544324424145 102996082715503158243318109)
            ·
              refine ⟨38623531018313684341244291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102996082715503158243318109 38623531018313684341244291)
              ·
                refine ⟨57935296527470526511866437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38623531018313684341244291 57935296527470526511866437)
                ·
                  refine ⟨10862868098900723720974957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57935296527470526511866437 10862868098900723720974957)
                  ·
                    refine ⟨4073575537087771395365609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10862868098900723720974957 4073575537087771395365609)
                    ·
                      refine ⟨3055181652815828546524207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073575537087771395365609 3055181652815828546524207)
                      ·
                        rfl

theorem cell23_5949945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_5949945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949945 prefixEnd_5949945 := by exact prefixLift 5949945
  have htrace : WordTrace (prefixWord ++ tailWord_5949945) baseStart_5949945 baseEnd_5949945 := by
    simpa [prefixWord, tailWord_5949945, baseEnd_5949945] using wordTrace_append hprefix tailTrace_5949945
  have hstable : (prefixWord ++ tailWord_5949945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949945).length < 2 ^ (prefixWord ++ tailWord_5949945).sum := by decide
  have hdescent : baseEnd_5949945 < baseStart_5949945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949959 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 6]
def baseStart_5949959 : Nat := 118140960795 + 5949959 * 2 ^ 59
def prefixEnd_5949959 : Nat := 4983230072969 + 3 ^ 40 * 5949959 * 2
def baseEnd_5949959 : Nat := 339465426838332387972127

theorem tailTrace_5949959 : CollatzResearch.WordTrace tailWord_5949959 prefixEnd_5949959 339465426838332387972127 := by
  unfold tailWord_5949959
  simp only [CollatzResearch.WordTrace]
  refine ⟨217012833051322189940716931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144675222034214793293811287 217012833051322189940716931)
  ·
    refine ⟨325519249576983284911075397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217012833051322189940716931 325519249576983284911075397)
    ·
      refine ⟨61034859295684365920826637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325519249576983284911075397 61034859295684365920826637)
      ·
        refine ⟨22888072235881637220309989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61034859295684365920826637 22888072235881637220309989)
        ·
          refine ⟨4291513544227806978808123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22888072235881637220309989 4291513544227806978808123)
          ·
            refine ⟨6437270316341710468212185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291513544227806978808123 6437270316341710468212185)
            ·
              refine ⟨4827952737256282851159139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437270316341710468212185 4827952737256282851159139)
              ·
                refine ⟨7241929105884424276738709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827952737256282851159139 7241929105884424276738709)
                ·
                  refine ⟨339465426838332387972127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7241929105884424276738709 339465426838332387972127)
                  ·
                    rfl

theorem cell23_5949959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 6].length) (baseStart_5949959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949959 prefixEnd_5949959 := by exact prefixLift 5949959
  have htrace : WordTrace (prefixWord ++ tailWord_5949959) baseStart_5949959 baseEnd_5949959 := by
    simpa [prefixWord, tailWord_5949959, baseEnd_5949959] using wordTrace_append hprefix tailTrace_5949959
  have hstable : (prefixWord ++ tailWord_5949959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949959).length < 2 ^ (prefixWord ++ tailWord_5949959).sum := by decide
  have hdescent : baseEnd_5949959 < baseStart_5949959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949972 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5949972 : Nat := 118140960795 + 5949972 * 2 ^ 59
def prefixEnd_5949972 : Nat := 4983230072969 + 3 ^ 40 * 5949972 * 2
def baseEnd_5949972 : Nat := 1018398505597833313628861

theorem tailTrace_5949972 : CollatzResearch.WordTrace tailWord_5949972 prefixEnd_5949972 1018398505597833313628861 := by
  unfold tailWord_5949972
  simp only [CollatzResearch.WordTrace]
  refine ⟨108506653600137546580470085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144675538133516728773960113 108506653600137546580470085)
  ·
    refine ⟨20344997550025789983838141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108506653600137546580470085 20344997550025789983838141)
    ·
      refine ⟨7629374081259671243939303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20344997550025789983838141 7629374081259671243939303)
      ·
        refine ⟨11444061121889506865908955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7629374081259671243939303 11444061121889506865908955)
        ·
          refine ⟨17166091682834260298863433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11444061121889506865908955 17166091682834260298863433)
          ·
            refine ⟨12874568762125695224147575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17166091682834260298863433 12874568762125695224147575)
            ·
              refine ⟨19311853143188542836221363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12874568762125695224147575 19311853143188542836221363)
              ·
                refine ⟨28967779714782814254332045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19311853143188542836221363 28967779714782814254332045)
                ·
                  refine ⟨10862917393043555345374517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28967779714782814254332045 10862917393043555345374517)
                  ·
                    refine ⟨1018398505597833313628861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10862917393043555345374517 1018398505597833313628861)
                    ·
                      rfl

theorem cell23_5949972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5949972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949972 prefixEnd_5949972 := by exact prefixLift 5949972
  have htrace : WordTrace (prefixWord ++ tailWord_5949972) baseStart_5949972 baseEnd_5949972 := by
    simpa [prefixWord, tailWord_5949972, baseEnd_5949972] using wordTrace_append hprefix tailTrace_5949972
  have hstable : (prefixWord ++ tailWord_5949972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949972).length < 2 ^ (prefixWord ++ tailWord_5949972).sum := by decide
  have hdescent : baseEnd_5949972 < baseStart_5949972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949978 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_5949978 : Nat := 118140960795 + 5949978 * 2 ^ 59
def prefixEnd_5949978 : Nat := 4983230072969 + 3 ^ 40 * 5949978 * 2
def baseEnd_5949978 : Nat := 3055198597677426917411555

theorem tailTrace_5949978 : CollatzResearch.WordTrace tailWord_5949978 prefixEnd_5949978 3055198597677426917411555 := by
  unfold tailWord_5949978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54253381509563339046414647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144675684025502237457105725 54253381509563339046414647)
  ·
    refine ⟨81380072264345008569621971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54253381509563339046414647 81380072264345008569621971)
    ·
      refine ⟨122070108396517512854432957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81380072264345008569621971 122070108396517512854432957)
      ·
        refine ⟨45776290648694067320412359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122070108396517512854432957 45776290648694067320412359)
        ·
          refine ⟨68664435973041100980618539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45776290648694067320412359 68664435973041100980618539)
          ·
            refine ⟨102996653959561651470927809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68664435973041100980618539 102996653959561651470927809)
            ·
              refine ⟨77247490469671238603195857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102996653959561651470927809 77247490469671238603195857)
              ·
                refine ⟨57935617852253428952396893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77247490469671238603195857 57935617852253428952396893)
                ·
                  refine ⟨21725856694595035857148835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57935617852253428952396893 21725856694595035857148835)
                  ·
                    refine ⟨32588785041892553785723253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21725856694595035857148835 32588785041892553785723253)
                    ·
                      refine ⟨3055198597677426917411555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32588785041892553785723253 3055198597677426917411555)
                      ·
                        rfl

theorem cell23_5949978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_5949978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949978 prefixEnd_5949978 := by exact prefixLift 5949978
  have htrace : WordTrace (prefixWord ++ tailWord_5949978) baseStart_5949978 baseEnd_5949978 := by
    simpa [prefixWord, tailWord_5949978, baseEnd_5949978] using wordTrace_append hprefix tailTrace_5949978
  have hstable : (prefixWord ++ tailWord_5949978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949978).length < 2 ^ (prefixWord ++ tailWord_5949978).sum := by decide
  have hdescent : baseEnd_5949978 < baseStart_5949978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949995 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 3]
def baseStart_5949995 : Nat := 118140960795 + 5949995 * 2 ^ 59
def prefixEnd_5949995 : Nat := 4983230072969 + 3 ^ 40 * 5949995 * 2
def baseEnd_5949995 : Nat := 3055207326848553350898977

theorem tailTrace_5949995 : CollatzResearch.WordTrace tailWord_5949995 prefixEnd_5949995 3055207326848553350898977 := by
  unfold tailWord_5949995
  simp only [CollatzResearch.WordTrace]
  refine ⟨217014146079191768089027439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144676097386127845392684959 217014146079191768089027439)
  ·
    refine ⟨325521219118787652133541159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217014146079191768089027439 325521219118787652133541159)
    ·
      refine ⟨488281828678181478200311739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325521219118787652133541159 488281828678181478200311739)
      ·
        refine ⟨732422743017272217300467609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488281828678181478200311739 732422743017272217300467609)
        ·
          refine ⟨549317057262954162975350707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732422743017272217300467609 549317057262954162975350707)
          ·
            refine ⟨823975585894431244463026061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549317057262954162975350707 823975585894431244463026061)
            ·
              refine ⟨308990844710411716673634773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 823975585894431244463026061 308990844710411716673634773)
              ·
                refine ⟨7241972922900274609538315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 308990844710411716673634773 7241972922900274609538315)
                ·
                  refine ⟨10862959384350411914307473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241972922900274609538315 10862959384350411914307473)
                  ·
                    refine ⟨8147219538262808935730605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10862959384350411914307473 8147219538262808935730605)
                    ·
                      refine ⟨3055207326848553350898977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147219538262808935730605 3055207326848553350898977)
                      ·
                        rfl

theorem cell23_5949995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 3].length) (baseStart_5949995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949995 prefixEnd_5949995 := by exact prefixLift 5949995
  have htrace : WordTrace (prefixWord ++ tailWord_5949995) baseStart_5949995 baseEnd_5949995 := by
    simpa [prefixWord, tailWord_5949995, baseEnd_5949995] using wordTrace_append hprefix tailTrace_5949995
  have hstable : (prefixWord ++ tailWord_5949995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949995).length < 2 ^ (prefixWord ++ tailWord_5949995).sum := by decide
  have hdescent : baseEnd_5949995 < baseStart_5949995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949997 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5949997 : Nat := 118140960795 + 5949997 * 2 ^ 59
def prefixEnd_5949997 : Nat := 4983230072969 + 3 ^ 40 * 5949997 * 2
def baseEnd_5949997 : Nat := 1018402784603287447691323

theorem tailTrace_5949997 : CollatzResearch.WordTrace tailWord_5949997 prefixEnd_5949997 1018402784603287447691323 := by
  unfold tailWord_5949997
  simp only [CollatzResearch.WordTrace]
  refine ⟨217014219025184522430600245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144676146016789681620400163 217014219025184522430600245)
  ·
    refine ⟨20345083033611048977868773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217014219025184522430600245 20345083033611048977868773)
    ·
      refine ⟨3814703068802071683350395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20345083033611048977868773 3814703068802071683350395)
      ·
        refine ⟨5722054603203107525025593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814703068802071683350395 5722054603203107525025593)
        ·
          refine ⟨4291540952402330643769195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5722054603203107525025593 4291540952402330643769195)
          ·
            refine ⟨6437311428603495965653793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291540952402330643769195 6437311428603495965653793)
            ·
              refine ⟨4827983571452621974240345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437311428603495965653793 4827983571452621974240345)
              ·
                refine ⟨3620987678589466480680259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827983571452621974240345 3620987678589466480680259)
                ·
                  refine ⟨5431481517884199721020389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620987678589466480680259 5431481517884199721020389)
                  ·
                    refine ⟨1018402784603287447691323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431481517884199721020389 1018402784603287447691323)
                    ·
                      rfl

theorem cell23_5949997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5949997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949997 prefixEnd_5949997 := by exact prefixLift 5949997
  have htrace : WordTrace (prefixWord ++ tailWord_5949997) baseStart_5949997 baseEnd_5949997 := by
    simpa [prefixWord, tailWord_5949997, baseEnd_5949997] using wordTrace_append hprefix tailTrace_5949997
  have hstable : (prefixWord ++ tailWord_5949997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949997).length < 2 ^ (prefixWord ++ tailWord_5949997).sum := by decide
  have hdescent : baseEnd_5949997 < baseStart_5949997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5949998 : List Nat := [4, 1, 3, 1, 14]
def baseStart_5949998 : Nat := 118140960795 + 5949998 * 2 ^ 59
def prefixEnd_5949998 : Nat := 4983230072969 + 3 ^ 40 * 5949998 * 2
def baseEnd_5949998 : Nat := 4190958665693438736847

theorem tailTrace_5949998 : CollatzResearch.WordTrace tailWord_5949998 prefixEnd_5949998 4190958665693438736847 := by
  unfold tailWord_5949998
  simp only [CollatzResearch.WordTrace]
  refine ⟨27126781937272612450173331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144676170332120599734257765 27126781937272612450173331)
  ·
    refine ⟨40690172905908918675259997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27126781937272612450173331 40690172905908918675259997)
    ·
      refine ⟨15258814839715844503222499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40690172905908918675259997 15258814839715844503222499)
      ·
        refine ⟨22888222259573766754833749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258814839715844503222499 22888222259573766754833749)
        ·
          refine ⟨4190958665693438736847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 22888222259573766754833749 4190958665693438736847)
          ·
            rfl

theorem cell23_5949998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 14].length) (baseStart_5949998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5949998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5949998 prefixEnd_5949998 := by exact prefixLift 5949998
  have htrace : WordTrace (prefixWord ++ tailWord_5949998) baseStart_5949998 baseEnd_5949998 := by
    simpa [prefixWord, tailWord_5949998, baseEnd_5949998] using wordTrace_append hprefix tailTrace_5949998
  have hstable : (prefixWord ++ tailWord_5949998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5949998).length < 2 ^ (prefixWord ++ tailWord_5949998).sum := by decide
  have hdescent : baseEnd_5949998 < baseStart_5949998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5949998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950025 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 3]
def baseStart_5950025 : Nat := 118140960795 + 5950025 * 2 ^ 59
def prefixEnd_5950025 : Nat := 4983230072969 + 3 ^ 40 * 5950025 * 2
def baseEnd_5950025 : Nat := 3055222731268188233523839

theorem tailTrace_5950025 : CollatzResearch.WordTrace tailWord_5950025 prefixEnd_5950025 3055222731268188233523839 := by
  unfold tailWord_5950025
  simp only [CollatzResearch.WordTrace]
  refine ⟨217015240269083083212619529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144676826846055388808413019 217015240269083083212619529)
  ·
    refine ⟨162761430201812312409464647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217015240269083083212619529 162761430201812312409464647)
    ·
      refine ⟨244142145302718468614196971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162761430201812312409464647 244142145302718468614196971)
      ·
        refine ⟨366213217954077702921295457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244142145302718468614196971 366213217954077702921295457)
        ·
          refine ⟨274659913465558277190971593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366213217954077702921295457 274659913465558277190971593)
          ·
            refine ⟨205994935099168707893228695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274659913465558277190971593 205994935099168707893228695)
            ·
              refine ⟨308992402648753061839843043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205994935099168707893228695 308992402648753061839843043)
              ·
                refine ⟨463488603973129592759764565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308992402648753061839843043 463488603973129592759764565)
                ·
                  refine ⟨5431507077810112415153491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 463488603973129592759764565 5431507077810112415153491)
                  ·
                    refine ⟨8147260616715168622730237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5431507077810112415153491 8147260616715168622730237)
                    ·
                      refine ⟨3055222731268188233523839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147260616715168622730237 3055222731268188233523839)
                      ·
                        rfl

theorem cell23_5950025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_5950025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950025 prefixEnd_5950025 := by exact prefixLift 5950025
  have htrace : WordTrace (prefixWord ++ tailWord_5950025) baseStart_5950025 baseEnd_5950025 := by
    simpa [prefixWord, tailWord_5950025, baseEnd_5950025] using wordTrace_append hprefix tailTrace_5950025
  have hstable : (prefixWord ++ tailWord_5950025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950025).length < 2 ^ (prefixWord ++ tailWord_5950025).sum := by decide
  have hdescent : baseEnd_5950025 < baseStart_5950025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950028 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_5950028 : Nat := 118140960795 + 5950028 * 2 ^ 59
def prefixEnd_5950028 : Nat := 4983230072969 + 3 ^ 40 * 5950028 * 2
def baseEnd_5950028 : Nat := 1018408090570050573928775

theorem tailTrace_5950028 : CollatzResearch.WordTrace tailWord_5950028 prefixEnd_5950028 1018408090570050573928775 := by
  unfold tailWord_5950028
  simp only [CollatzResearch.WordTrace]
  refine ⟨108507674844036107362489369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144676899792048143149985825 108507674844036107362489369)
  ·
    refine ⟨81380756133027080521867027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108507674844036107362489369 81380756133027080521867027)
    ·
      refine ⟨122071134199540620782800541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81380756133027080521867027 122071134199540620782800541)
      ·
        refine ⟨45776675324827732793550203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122071134199540620782800541 45776675324827732793550203)
        ·
          refine ⟨68665012987241599190325305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45776675324827732793550203 68665012987241599190325305)
          ·
            refine ⟨51498759740431199392743979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68665012987241599190325305 51498759740431199392743979)
            ·
              refine ⟨77248139610646799089115969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51498759740431199392743979 77248139610646799089115969)
              ·
                refine ⟨57936104707985099316836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77248139610646799089115969 57936104707985099316836977)
                ·
                  refine ⟨43452078530988824487627733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57936104707985099316836977 43452078530988824487627733)
                  ·
                    refine ⟨1018408090570050573928775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43452078530988824487627733 1018408090570050573928775)
                    ·
                      rfl

theorem cell23_5950028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_5950028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950028 prefixEnd_5950028 := by exact prefixLift 5950028
  have htrace : WordTrace (prefixWord ++ tailWord_5950028) baseStart_5950028 baseEnd_5950028 := by
    simpa [prefixWord, tailWord_5950028, baseEnd_5950028] using wordTrace_append hprefix tailTrace_5950028
  have hstable : (prefixWord ++ tailWord_5950028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950028).length < 2 ^ (prefixWord ++ tailWord_5950028).sum := by decide
  have hdescent : baseEnd_5950028 < baseStart_5950028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950065 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_5950065 : Nat := 118140960795 + 5950065 * 2 ^ 59
def prefixEnd_5950065 : Nat := 4983230072969 + 3 ^ 40 * 5950065 * 2
def baseEnd_5950065 : Nat := 3055243270494368077023655

theorem tailTrace_5950065 : CollatzResearch.WordTrace tailWord_5950065 prefixEnd_5950065 3055243270494368077023655 := by
  unfold tailWord_5950065
  simp only [CollatzResearch.WordTrace]
  refine ⟨217016699188938170044075649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144677799459292113362717099 217016699188938170044075649)
  ·
    refine ⟨162762524391703627533056737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217016699188938170044075649 162762524391703627533056737)
    ·
      refine ⟨122071893293777720649792553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162762524391703627533056737 122071893293777720649792553)
      ·
        refine ⟨91553919970333290487344415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122071893293777720649792553 91553919970333290487344415)
        ·
          refine ⟨137330879955499935731016623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91553919970333290487344415 137330879955499935731016623)
          ·
            refine ⟨205996319933249903596524935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137330879955499935731016623 205996319933249903596524935)
            ·
              refine ⟨308994479899874855394787403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205996319933249903596524935 308994479899874855394787403)
              ·
                refine ⟨463491719849812283092181105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308994479899874855394787403 463491719849812283092181105)
                ·
                  refine ⟨347618789887359212319135829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463491719849812283092181105 347618789887359212319135829)
                  ·
                    refine ⟨4073657693992490769364873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 347618789887359212319135829 4073657693992490769364873)
                    ·
                      refine ⟨3055243270494368077023655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073657693992490769364873 3055243270494368077023655)
                      ·
                        rfl

theorem cell23_5950065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_5950065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950065 prefixEnd_5950065 := by exact prefixLift 5950065
  have htrace : WordTrace (prefixWord ++ tailWord_5950065) baseStart_5950065 baseEnd_5950065 := by
    simpa [prefixWord, tailWord_5950065, baseEnd_5950065] using wordTrace_append hprefix tailTrace_5950065
  have hstable : (prefixWord ++ tailWord_5950065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950065).length < 2 ^ (prefixWord ++ tailWord_5950065).sum := by decide
  have hdescent : baseEnd_5950065 < baseStart_5950065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950115 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3]
def baseStart_5950115 : Nat := 118140960795 + 5950115 * 2 ^ 59
def prefixEnd_5950115 : Nat := 4983230072969 + 3 ^ 40 * 5950115 * 2
def baseEnd_5950115 : Nat := 3055268944527092881398425

theorem tailTrace_5950115 : CollatzResearch.WordTrace tailWord_5950115 prefixEnd_5950115 3055268944527092881398425 := by
  unfold tailWord_5950115
  simp only [CollatzResearch.WordTrace]
  refine ⟨217018522838757028583395799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144679015225838019055597199 217018522838757028583395799)
  ·
    refine ⟨325527784258135542875093699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217018522838757028583395799 325527784258135542875093699)
    ·
      refine ⟨488291676387203314312640549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325527784258135542875093699 488291676387203314312640549)
      ·
        refine ⟨91554689322600621433620103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 488291676387203314312640549 91554689322600621433620103)
        ·
          refine ⟨137332033983900932150430155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91554689322600621433620103 137332033983900932150430155)
          ·
            refine ⟨205998050975851398225645233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137332033983900932150430155 205998050975851398225645233)
            ·
              refine ⟨154498538231888548669233925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205998050975851398225645233 154498538231888548669233925)
              ·
                refine ⟨28968475918479102875481361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154498538231888548669233925 28968475918479102875481361)
                ·
                  refine ⟨21726356938859327156611021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28968475918479102875481361 21726356938859327156611021)
                  ·
                    refine ⟨8147383852072247683729133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21726356938859327156611021 8147383852072247683729133)
                    ·
                      refine ⟨3055268944527092881398425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147383852072247683729133 3055268944527092881398425)
                      ·
                        rfl

theorem cell23_5950115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_5950115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950115 prefixEnd_5950115 := by exact prefixLift 5950115
  have htrace : WordTrace (prefixWord ++ tailWord_5950115) baseStart_5950115 baseEnd_5950115 := by
    simpa [prefixWord, tailWord_5950115, baseEnd_5950115] using wordTrace_append hprefix tailTrace_5950115
  have hstable : (prefixWord ++ tailWord_5950115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950115).length < 2 ^ (prefixWord ++ tailWord_5950115).sum := by decide
  have hdescent : baseEnd_5950115 < baseStart_5950115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950133 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5950133 : Nat := 118140960795 + 5950133 * 2 ^ 59
def prefixEnd_5950133 : Nat := 4983230072969 + 3 ^ 40 * 5950133 * 2
def baseEnd_5950133 : Nat := 3055278187178873810973343

theorem tailTrace_5950133 : CollatzResearch.WordTrace tailWord_5950133 prefixEnd_5950133 3055278187178873810973343 := by
  unfold tailWord_5950133
  simp only [CollatzResearch.WordTrace]
  refine ⟨217019179352691817657551053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144679452901794545105034035 217019179352691817657551053)
  ·
    refine ⟨81382192257259431621581645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217019179352691817657551053 81382192257259431621581645)
    ·
      refine ⟨30518322096472286858093117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81382192257259431621581645 30518322096472286858093117)
      ·
        refine ⟨11444370786177107571784919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30518322096472286858093117 11444370786177107571784919)
        ·
          refine ⟨17166556179265661357677379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11444370786177107571784919 17166556179265661357677379)
          ·
            refine ⟨25749834268898492036516069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17166556179265661357677379 25749834268898492036516069)
            ·
              refine ⟨4828093925418467256846763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25749834268898492036516069 4828093925418467256846763)
              ·
                refine ⟨7242140888127700885270145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828093925418467256846763 7242140888127700885270145)
                ·
                  refine ⟨5431605666095775663952609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7242140888127700885270145 5431605666095775663952609)
                  ·
                    refine ⟨4073704249571831747964457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5431605666095775663952609 4073704249571831747964457)
                    ·
                      refine ⟨3055278187178873810973343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073704249571831747964457 3055278187178873810973343)
                      ·
                        rfl

theorem cell23_5950133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5950133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950133 prefixEnd_5950133 := by exact prefixLift 5950133
  have htrace : WordTrace (prefixWord ++ tailWord_5950133) baseStart_5950133 baseEnd_5950133 := by
    simpa [prefixWord, tailWord_5950133, baseEnd_5950133] using wordTrace_append hprefix tailTrace_5950133
  have hstable : (prefixWord ++ tailWord_5950133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950133).length < 2 ^ (prefixWord ++ tailWord_5950133).sum := by decide
  have hdescent : baseEnd_5950133 < baseStart_5950133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950152 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_5950152 : Nat := 118140960795 + 5950152 * 2 ^ 59
def prefixEnd_5950152 : Nat := 4983230072969 + 3 ^ 40 * 5950152 * 2
def baseEnd_5950152 : Nat := 1018429314437103078878585

theorem tailTrace_5950152 : CollatzResearch.WordTrace tailWord_5950152 prefixEnd_5950152 1018429314437103078878585 := by
  unfold tailWord_5950152
  simp only [CollatzResearch.WordTrace]
  refine ⟨108509936169811491951246355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144679914893081989268328473 108509936169811491951246355)
  ·
    refine ⟨162764904254717237926869533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108509936169811491951246355 162764904254717237926869533)
    ·
      refine ⟨61036839095518964222576075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162764904254717237926869533 61036839095518964222576075)
      ·
        refine ⟨91555258643278446333864113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61036839095518964222576075 91555258643278446333864113)
        ·
          refine ⟨68666443982458834750398085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91555258643278446333864113 68666443982458834750398085)
          ·
            refine ⟨12874958246711031515699641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68666443982458834750398085 12874958246711031515699641)
            ·
              refine ⟨9656218685033273636774731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12874958246711031515699641 9656218685033273636774731)
              ·
                refine ⟨14484328027549910455162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656218685033273636774731 14484328027549910455162097)
                ·
                  refine ⟨10863246020662432841371573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14484328027549910455162097 10863246020662432841371573)
                  ·
                    refine ⟨1018429314437103078878585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10863246020662432841371573 1018429314437103078878585)
                    ·
                      rfl

theorem cell23_5950152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_5950152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950152 prefixEnd_5950152 := by exact prefixLift 5950152
  have htrace : WordTrace (prefixWord ++ tailWord_5950152) baseStart_5950152 baseEnd_5950152 := by
    simpa [prefixWord, tailWord_5950152, baseEnd_5950152] using wordTrace_append hprefix tailTrace_5950152
  have hstable : (prefixWord ++ tailWord_5950152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950152).length < 2 ^ (prefixWord ++ tailWord_5950152).sum := by decide
  have hdescent : baseEnd_5950152 < baseStart_5950152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950189 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_5950189 : Nat := 118140960795 + 5950189 * 2 ^ 59
def prefixEnd_5950189 : Nat := 4983230072969 + 3 ^ 40 * 5950189 * 2
def baseEnd_5950189 : Nat := 3055306942095525591873085

theorem tailTrace_5950189 : CollatzResearch.WordTrace tailWord_5950189 prefixEnd_5950189 3055306942095525591873085 := by
  unfold tailWord_5950189
  simp only [CollatzResearch.WordTrace]
  refine ⟨217021221840488939221589621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144680814560325959481059747 217021221840488939221589621)
  ·
    refine ⟨20345739547545838052024027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217021221840488939221589621 20345739547545838052024027)
    ·
      refine ⟨30518609321318757078036041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20345739547545838052024027 30518609321318757078036041)
      ·
        refine ⟨22888956990989067808527031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30518609321318757078036041 22888956990989067808527031)
        ·
          refine ⟨34333435486483601712790547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22888956990989067808527031 34333435486483601712790547)
          ·
            refine ⟨51500153229725402569185821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34333435486483601712790547 51500153229725402569185821)
            ·
              refine ⟨19312557461147025963444683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51500153229725402569185821 19312557461147025963444683)
              ·
                refine ⟨28968836191720538945167025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19312557461147025963444683 28968836191720538945167025)
                ·
                  refine ⟨21726627143790404208875269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28968836191720538945167025 21726627143790404208875269)
                  ·
                    refine ⟨4073742589460700789164113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21726627143790404208875269 4073742589460700789164113)
                    ·
                      refine ⟨3055306942095525591873085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073742589460700789164113 3055306942095525591873085)
                      ·
                        rfl

theorem cell23_5950189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_5950189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950189 prefixEnd_5950189 := by exact prefixLift 5950189
  have htrace : WordTrace (prefixWord ++ tailWord_5950189) baseStart_5950189 baseEnd_5950189 := by
    simpa [prefixWord, tailWord_5950189, baseEnd_5950189] using wordTrace_append hprefix tailTrace_5950189
  have hstable : (prefixWord ++ tailWord_5950189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950189).length < 2 ^ (prefixWord ++ tailWord_5950189).sum := by decide
  have hdescent : baseEnd_5950189 < baseStart_5950189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950206 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5950206 : Nat := 118140960795 + 5950206 * 2 ^ 59
def prefixEnd_5950206 : Nat := 4983230072969 + 3 ^ 40 * 5950206 * 2
def baseEnd_5950206 : Nat := 3055315671266652025360507

theorem tailTrace_5950206 : CollatzResearch.WordTrace tailWord_5950206 prefixEnd_5950206 3055315671266652025360507 := by
  unfold tailWord_5950206
  simp only [CollatzResearch.WordTrace]
  refine ⟨27127730235178418890619809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144681227920951567416638981 27127730235178418890619809)
  ·
    refine ⟨20345797676383814167964857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27127730235178418890619809 20345797676383814167964857)
    ·
      refine ⟨15259348257287860625973643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20345797676383814167964857 15259348257287860625973643)
      ·
        refine ⟨22889022385931790938960465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15259348257287860625973643 22889022385931790938960465)
        ·
          refine ⟨17166766789448843204220349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22889022385931790938960465 17166766789448843204220349)
          ·
            refine ⟨6437537546043316201582631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17166766789448843204220349 6437537546043316201582631)
            ·
              refine ⟨9656306319064974302373947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437537546043316201582631 9656306319064974302373947)
              ·
                refine ⟨14484459478597461453560921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656306319064974302373947 14484459478597461453560921)
                ·
                  refine ⟨10863344608948096090170691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14484459478597461453560921 10863344608948096090170691)
                  ·
                    refine ⟨16295016913422144135256037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10863344608948096090170691 16295016913422144135256037)
                    ·
                      refine ⟨3055315671266652025360507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16295016913422144135256037 3055315671266652025360507)
                      ·
                        rfl

theorem cell23_5950206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5950206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950206 prefixEnd_5950206 := by exact prefixLift 5950206
  have htrace : WordTrace (prefixWord ++ tailWord_5950206) baseStart_5950206 baseEnd_5950206 := by
    simpa [prefixWord, tailWord_5950206, baseEnd_5950206] using wordTrace_append hprefix tailTrace_5950206
  have hstable : (prefixWord ++ tailWord_5950206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950206).length < 2 ^ (prefixWord ++ tailWord_5950206).sum := by decide
  have hdescent : baseEnd_5950206 < baseStart_5950206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950216 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 1, 4]
def baseStart_5950216 : Nat := 118140960795 + 5950216 * 2 ^ 59
def prefixEnd_5950216 : Nat := 4983230072969 + 3 ^ 40 * 5950216 * 2
def baseEnd_5950216 : Nat := 1018440268691065662078487

theorem tailTrace_5950216 : CollatzResearch.WordTrace tailWord_5950216 prefixEnd_5950216 1018440268691065662078487 := by
  unfold tailWord_5950216
  simp only [CollatzResearch.WordTrace]
  refine ⟨108511103305695561416411251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144681471074260748555215001 108511103305695561416411251)
  ·
    refine ⟨162766654958543342124616877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108511103305695561416411251 162766654958543342124616877)
    ·
      refine ⟨61037495609453753296731329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162766654958543342124616877 61037495609453753296731329)
      ·
        refine ⟨45778121707090314972548497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61037495609453753296731329 45778121707090314972548497)
        ·
          refine ⟨34333591280317736229411373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45778121707090314972548497 34333591280317736229411373)
          ·
            refine ⟨12875096730119151086029265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34333591280317736229411373 12875096730119151086029265)
            ·
              refine ⟨9656322547589363314521949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12875096730119151086029265 9656322547589363314521949)
              ·
                refine ⟨3621120955346011242945731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9656322547589363314521949 3621120955346011242945731)
                ·
                  refine ⟨5431681433019016864418597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621120955346011242945731 5431681433019016864418597)
                  ·
                    refine ⟨1018440268691065662078487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431681433019016864418597 1018440268691065662078487)
                    ·
                      rfl

theorem cell23_5950216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_5950216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950216 prefixEnd_5950216 := by exact prefixLift 5950216
  have htrace : WordTrace (prefixWord ++ tailWord_5950216) baseStart_5950216 baseEnd_5950216 := by
    simpa [prefixWord, tailWord_5950216, baseEnd_5950216] using wordTrace_append hprefix tailTrace_5950216
  have hstable : (prefixWord ++ tailWord_5950216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950216).length < 2 ^ (prefixWord ++ tailWord_5950216).sum := by decide
  have hdescent : baseEnd_5950216 < baseStart_5950216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950239 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 3]
def baseStart_5950239 : Nat := 118140960795 + 5950239 * 2 ^ 59
def prefixEnd_5950239 : Nat := 4983230072969 + 3 ^ 40 * 5950239 * 2
def baseEnd_5950239 : Nat := 3055332616128250396247855

theorem tailTrace_5950239 : CollatzResearch.WordTrace tailWord_5950239 prefixEnd_5950239 3055332616128250396247855 := by
  unfold tailWord_5950239
  simp only [CollatzResearch.WordTrace]
  refine ⟨217023045490307797760909771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144682030326871865173939847 217023045490307797760909771)
  ·
    refine ⟨325534568235461696641364657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217023045490307797760909771 325534568235461696641364657)
    ·
      refine ⟨244150926176596272481023493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325534568235461696641364657 244150926176596272481023493)
      ·
        refine ⟨45778298658111801090191905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244150926176596272481023493 45778298658111801090191905)
        ·
          refine ⟨34333723993583850817643929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45778298658111801090191905 34333723993583850817643929)
          ·
            refine ⟨25750292995187888113232947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34333723993583850817643929 25750292995187888113232947)
            ·
              refine ⟨38625439492781832169849421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25750292995187888113232947 38625439492781832169849421)
              ·
                refine ⟨14484539809793187063693533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38625439492781832169849421 14484539809793187063693533)
                ·
                  refine ⟨5431702428672445148885075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14484539809793187063693533 5431702428672445148885075)
                  ·
                    refine ⟨8147553643008667723327613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5431702428672445148885075 8147553643008667723327613)
                    ·
                      refine ⟨3055332616128250396247855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147553643008667723327613 3055332616128250396247855)
                      ·
                        rfl

theorem cell23_5950239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_5950239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950239 prefixEnd_5950239 := by exact prefixLift 5950239
  have htrace : WordTrace (prefixWord ++ tailWord_5950239) baseStart_5950239 baseEnd_5950239 := by
    simpa [prefixWord, tailWord_5950239, baseEnd_5950239] using wordTrace_append hprefix tailTrace_5950239
  have hstable : (prefixWord ++ tailWord_5950239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950239).length < 2 ^ (prefixWord ++ tailWord_5950239).sum := by decide
  have hdescent : baseEnd_5950239 < baseStart_5950239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950259 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 1, 5]
def baseStart_5950259 : Nat := 118140960795 + 5950259 * 2 ^ 59
def prefixEnd_5950259 : Nat := 4983230072969 + 3 ^ 40 * 5950259 * 2
def baseEnd_5950259 : Nat := 1018447628580446772665921

theorem tailTrace_5950259 : CollatzResearch.WordTrace tailWord_5950259 prefixEnd_5950259 1018447628580446772665921 := by
  unfold tailWord_5950259
  simp only [CollatzResearch.WordTrace]
  refine ⟨217023774950235341176637831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144682516633490227451091887 217023774950235341176637831)
  ·
    refine ⟨325535662425353011764956747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217023774950235341176637831 325535662425353011764956747)
    ·
      refine ⟨488303493638029517647435121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325535662425353011764956747 488303493638029517647435121)
      ·
        refine ⟨366227620228522138235576341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488303493638029517647435121 366227620228522138235576341)
        ·
          refine ⟨17166919698211975229792641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 366227620228522138235576341 17166919698211975229792641)
          ·
            refine ⟨12875189773658981422344481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17166919698211975229792641 12875189773658981422344481)
            ·
              refine ⟨9656392330244236066758361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12875189773658981422344481 9656392330244236066758361)
              ·
                refine ⟨7242294247683177050068771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9656392330244236066758361 7242294247683177050068771)
                ·
                  refine ⟨10863441371524765575103157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7242294247683177050068771 10863441371524765575103157)
                  ·
                    refine ⟨1018447628580446772665921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10863441371524765575103157 1018447628580446772665921)
                    ·
                      rfl

theorem cell23_5950259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 5].length) (baseStart_5950259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950259 prefixEnd_5950259 := by exact prefixLift 5950259
  have htrace : WordTrace (prefixWord ++ tailWord_5950259) baseStart_5950259 baseEnd_5950259 := by
    simpa [prefixWord, tailWord_5950259, baseEnd_5950259] using wordTrace_append hprefix tailTrace_5950259
  have hstable : (prefixWord ++ tailWord_5950259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950259).length < 2 ^ (prefixWord ++ tailWord_5950259).sum := by decide
  have hdescent : baseEnd_5950259 < baseStart_5950259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950326 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5950326 : Nat := 118140960795 + 5950326 * 2 ^ 59
def prefixEnd_5950326 : Nat := 4983230072969 + 3 ^ 40 * 5950326 * 2
def baseEnd_5950326 : Nat := 3055377288945191555859955

theorem tailTrace_5950326 : CollatzResearch.WordTrace tailWord_5950326 prefixEnd_5950326 3055377288945191555859955 := by
  unfold tailWord_5950326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13564138665062038226207927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144684145760661741079551221 13564138665062038226207927)
  ·
    refine ⟨20346207997593057339311891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13564138665062038226207927 20346207997593057339311891)
    ·
      refine ⟨30519311996389586008967837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20346207997593057339311891 30519311996389586008967837)
      ·
        refine ⟨11444741998646094753362939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30519311996389586008967837 11444741998646094753362939)
        ·
          refine ⟨17167112997969142130044409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11444741998646094753362939 17167112997969142130044409)
          ·
            refine ⟨12875334748476856597533307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17167112997969142130044409 12875334748476856597533307)
            ·
              refine ⟨19313002122715284896299961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12875334748476856597533307 19313002122715284896299961)
              ·
                refine ⟨14484751592036463672224971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19313002122715284896299961 14484751592036463672224971)
                ·
                  refine ⟨21727127388054695508337457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14484751592036463672224971 21727127388054695508337457)
                  ·
                    refine ⟨16295345541041021631253093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21727127388054695508337457 16295345541041021631253093)
                    ·
                      refine ⟨3055377288945191555859955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16295345541041021631253093 3055377288945191555859955)
                      ·
                        rfl

theorem cell23_5950326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5950326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950326 prefixEnd_5950326 := by exact prefixLift 5950326
  have htrace : WordTrace (prefixWord ++ tailWord_5950326) baseStart_5950326 baseEnd_5950326 := by
    simpa [prefixWord, tailWord_5950326, baseEnd_5950326] using wordTrace_append hprefix tailTrace_5950326
  have hstable : (prefixWord ++ tailWord_5950326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950326).length < 2 ^ (prefixWord ++ tailWord_5950326).sum := by decide
  have hdescent : baseEnd_5950326 < baseStart_5950326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950329 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_5950329 : Nat := 118140960795 + 5950329 * 2 ^ 59
def prefixEnd_5950329 : Nat := 4983230072969 + 3 ^ 40 * 5950329 * 2
def baseEnd_5950329 : Nat := 3055378829387155044122441

theorem tailTrace_5950329 : CollatzResearch.WordTrace tailWord_5950329 prefixEnd_5950329 3055378829387155044122441 := by
  unfold tailWord_5950329
  simp only [CollatzResearch.WordTrace]
  refine ⟨217026328059981743131686041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144684218706654495421124027 217026328059981743131686041)
  ·
    refine ⟨162769746044986307348764531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217026328059981743131686041 162769746044986307348764531)
    ·
      refine ⟨244154619067479461023146797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162769746044986307348764531 244154619067479461023146797)
      ·
        refine ⟨91557982150304797883680049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244154619067479461023146797 91557982150304797883680049)
        ·
          refine ⟨68668486612728598412760037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91557982150304797883680049 68668486612728598412760037)
          ·
            refine ⟨12875341239886612202392507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68668486612728598412760037 12875341239886612202392507)
            ·
              refine ⟨19313011859829918303588761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12875341239886612202392507 19313011859829918303588761)
              ·
                refine ⟨14484758894872438727691571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19313011859829918303588761 14484758894872438727691571)
                ·
                  refine ⟨21727138342308658091537357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14484758894872438727691571 21727138342308658091537357)
                  ·
                    refine ⟨8147676878365746784326509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21727138342308658091537357 8147676878365746784326509)
                    ·
                      refine ⟨3055378829387155044122441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147676878365746784326509 3055378829387155044122441)
                      ·
                        rfl

theorem cell23_5950329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_5950329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950329 prefixEnd_5950329 := by exact prefixLift 5950329
  have htrace : WordTrace (prefixWord ++ tailWord_5950329) baseStart_5950329 baseEnd_5950329 := by
    simpa [prefixWord, tailWord_5950329, baseEnd_5950329] using wordTrace_append hprefix tailTrace_5950329
  have hstable : (prefixWord ++ tailWord_5950329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950329).length < 2 ^ (prefixWord ++ tailWord_5950329).sum := by decide
  have hdescent : baseEnd_5950329 < baseStart_5950329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950356 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5950356 : Nat := 118140960795 + 5950356 * 2 ^ 59
def prefixEnd_5950356 : Nat := 4983230072969 + 3 ^ 40 * 5950356 * 2
def baseEnd_5950356 : Nat := 3055392693364826438484817

theorem tailTrace_5950356 : CollatzResearch.WordTrace tailWord_5950356 prefixEnd_5950356 3055392693364826438484817 := by
  unfold tailWord_5950356
  simp only [CollatzResearch.WordTrace]
  refine ⟨108513656415441963371459461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144684875220589284495279281 108513656415441963371459461)
  ·
    refine ⟨20346310577895368132148649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108513656415441963371459461 20346310577895368132148649)
    ·
      refine ⟨15259732933421526099111487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20346310577895368132148649 15259732933421526099111487)
      ·
        refine ⟨22889599400132289148667231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15259732933421526099111487 22889599400132289148667231)
        ·
          refine ⟨34334399100198433723000847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22889599400132289148667231 34334399100198433723000847)
          ·
            refine ⟨51501598650297650584501271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34334399100198433723000847 51501598650297650584501271)
            ·
              refine ⟨77252397975446475876751907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51501598650297650584501271 77252397975446475876751907)
              ·
                refine ⟨115878596963169713815127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77252397975446475876751907 115878596963169713815127861)
                ·
                  refine ⟨10863618465297160670168237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115878596963169713815127861 10863618465297160670168237)
                  ·
                    refine ⟨4073856924486435251313089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10863618465297160670168237 4073856924486435251313089)
                    ·
                      refine ⟨3055392693364826438484817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073856924486435251313089 3055392693364826438484817)
                      ·
                        rfl

theorem cell23_5950356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5950356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950356 prefixEnd_5950356 := by exact prefixLift 5950356
  have htrace : WordTrace (prefixWord ++ tailWord_5950356) baseStart_5950356 baseEnd_5950356 := by
    simpa [prefixWord, tailWord_5950356, baseEnd_5950356] using wordTrace_append hprefix tailTrace_5950356
  have hstable : (prefixWord ++ tailWord_5950356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950356).length < 2 ^ (prefixWord ++ tailWord_5950356).sum := by decide
  have hdescent : baseEnd_5950356 < baseStart_5950356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950432 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_5950432 : Nat := 118140960795 + 5950432 * 2 ^ 59
def prefixEnd_5950432 : Nat := 4983230072969 + 3 ^ 40 * 5950432 * 2
def baseEnd_5950432 : Nat := 3055431717894568141134467

theorem tailTrace_5950432 : CollatzResearch.WordTrace tailWord_5950432 prefixEnd_5950432 3055431717894568141134467 := by
  unfold tailWord_5950432
  simp only [CollatzResearch.WordTrace]
  refine ⟨108515042389304295861342775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144686723185739061148457033 108515042389304295861342775)
  ·
    refine ⟨162772563583956443792014163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108515042389304295861342775 162772563583956443792014163)
    ·
      refine ⟨244158845375934665688021245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162772563583956443792014163 244158845375934665688021245)
      ·
        refine ⟨91559567015975499633007967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244158845375934665688021245 91559567015975499633007967)
        ·
          refine ⟨137339350523963249449511951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91559567015975499633007967 137339350523963249449511951)
          ·
            refine ⟨206009025785944874174267927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137339350523963249449511951 206009025785944874174267927)
            ·
              refine ⟨309013538678917311261401891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206009025785944874174267927 309013538678917311261401891)
              ·
                refine ⟨463520308018375966892102837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309013538678917311261401891 463520308018375966892102837)
                ·
                  refine ⟨43455028876722746896134641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 463520308018375966892102837 43455028876722746896134641)
                  ·
                    refine ⟨32591271657542060172100981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43455028876722746896134641 32591271657542060172100981)
                    ·
                      refine ⟨3055431717894568141134467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32591271657542060172100981 3055431717894568141134467)
                      ·
                        rfl

theorem cell23_5950432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_5950432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950432 prefixEnd_5950432 := by exact prefixLift 5950432
  have htrace : WordTrace (prefixWord ++ tailWord_5950432) baseStart_5950432 baseEnd_5950432 := by
    simpa [prefixWord, tailWord_5950432, baseEnd_5950432] using wordTrace_append hprefix tailTrace_5950432
  have hstable : (prefixWord ++ tailWord_5950432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950432).length < 2 ^ (prefixWord ++ tailWord_5950432).sum := by decide
  have hdescent : baseEnd_5950432 < baseStart_5950432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950439 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5950439 : Nat := 118140960795 + 5950439 * 2 ^ 59
def prefixEnd_5950439 : Nat := 4983230072969 + 3 ^ 40 * 5950439 * 2
def baseEnd_5950439 : Nat := 1018478437419716537915645

theorem tailTrace_5950439 : CollatzResearch.WordTrace tailWord_5950439 prefixEnd_5950439 1018478437419716537915645 := by
  unfold tailWord_5950439
  simp only [CollatzResearch.WordTrace]
  refine ⟨217030340089583231918190371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144686893393055487945460247 217030340089583231918190371)
  ·
    refine ⟨325545510134374847877285557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217030340089583231918190371 325545510134374847877285557)
    ·
      refine ⟨30519891575097641988495521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325545510134374847877285557 30519891575097641988495521)
      ·
        refine ⟨22889918681323231491371641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30519891575097641988495521 22889918681323231491371641)
        ·
          refine ⟨17167439010992423618528731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22889918681323231491371641 17167439010992423618528731)
          ·
            refine ⟨25751158516488635427793097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17167439010992423618528731 25751158516488635427793097)
            ·
              refine ⟨19313368887366476570844823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25751158516488635427793097 19313368887366476570844823)
              ·
                refine ⟨28970053331049714856267235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19313368887366476570844823 28970053331049714856267235)
                ·
                  refine ⟨43455079996574572284400853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28970053331049714856267235 43455079996574572284400853)
                  ·
                    refine ⟨1018478437419716537915645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43455079996574572284400853 1018478437419716537915645)
                    ·
                      rfl

theorem cell23_5950439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5950439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950439 prefixEnd_5950439 := by exact prefixLift 5950439
  have htrace : WordTrace (prefixWord ++ tailWord_5950439) baseStart_5950439 baseEnd_5950439 := by
    simpa [prefixWord, tailWord_5950439, baseEnd_5950439] using wordTrace_append hprefix tailTrace_5950439
  have hstable : (prefixWord ++ tailWord_5950439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950439).length < 2 ^ (prefixWord ++ tailWord_5950439).sum := by decide
  have hdescent : baseEnd_5950439 < baseStart_5950439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950493 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_5950493 : Nat := 118140960795 + 5950493 * 2 ^ 59
def prefixEnd_5950493 : Nat := 4983230072969 + 3 ^ 40 * 5950493 * 2
def baseEnd_5950493 : Nat := 3055463040214492402471687

theorem tailTrace_5950493 : CollatzResearch.WordTrace tailWord_5950493 prefixEnd_5950493 3055463040214492402471687 := by
  unfold tailWord_5950493
  simp only [CollatzResearch.WordTrace]
  refine ⟨217032309631387599140656133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144688206420925066093770755 217032309631387599140656133)
  ·
    refine ⟨40693558055885174838873025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217032309631387599140656133 40693558055885174838873025)
    ·
      refine ⟨30520168541913881129154769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40693558055885174838873025 30520168541913881129154769)
      ·
        refine ⟨22890126406435410846866077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30520168541913881129154769 22890126406435410846866077)
        ·
          refine ⟨8583797402413279067574779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22890126406435410846866077 8583797402413279067574779)
          ·
            refine ⟨12875696103619918601362169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8583797402413279067574779 12875696103619918601362169)
            ·
              refine ⟨9656772077714938951021627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12875696103619918601362169 9656772077714938951021627)
              ·
                refine ⟨14485158116572408426532441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656772077714938951021627 14485158116572408426532441)
                ·
                  refine ⟨10863868587429306319899331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14485158116572408426532441 10863868587429306319899331)
                  ·
                    refine ⟨16295802881143959479848997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10863868587429306319899331 16295802881143959479848997)
                    ·
                      refine ⟨3055463040214492402471687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16295802881143959479848997 3055463040214492402471687)
                      ·
                        rfl

theorem cell23_5950493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_5950493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950493 prefixEnd_5950493 := by exact prefixLift 5950493
  have htrace : WordTrace (prefixWord ++ tailWord_5950493) baseStart_5950493 baseEnd_5950493 := by
    simpa [prefixWord, tailWord_5950493, baseEnd_5950493] using wordTrace_append hprefix tailTrace_5950493
  have hstable : (prefixWord ++ tailWord_5950493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950493).length < 2 ^ (prefixWord ++ tailWord_5950493).sum := by decide
  have hdescent : baseEnd_5950493 < baseStart_5950493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950520 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 1, 4]
def baseStart_5950520 : Nat := 118140960795 + 5950520 * 2 ^ 59
def prefixEnd_5950520 : Nat := 4983230072969 + 3 ^ 40 * 5950520 * 2
def baseEnd_5950520 : Nat := 1018492301397387932278021

theorem tailTrace_5950520 : CollatzResearch.WordTrace tailWord_5950520 prefixEnd_5950520 1018492301397387932278021 := by
  unfold tailWord_5950520
  simp only [CollatzResearch.WordTrace]
  refine ⟨108516647201144891375944507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144688862934859855167926009 108516647201144891375944507)
  ·
    refine ⟨162774970801717337063916761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108516647201144891375944507 162774970801717337063916761)
    ·
      refine ⟨122081228101288002797937571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162774970801717337063916761 122081228101288002797937571)
      ·
        refine ⟨183121842151932004196906357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122081228101288002797937571 183121842151932004196906357)
        ·
          refine ⟨17167672701743625393459971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183121842151932004196906357 17167672701743625393459971)
          ·
            refine ⟨25751509052615438090189957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17167672701743625393459971 25751509052615438090189957)
            ·
              refine ⟨4828407947365394641910617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25751509052615438090189957 4828407947365394641910617)
              ·
                refine ⟨3621305960524045981432963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828407947365394641910617 3621305960524045981432963)
                ·
                  refine ⟨5431958940786068972149445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621305960524045981432963 5431958940786068972149445)
                  ·
                    refine ⟨1018492301397387932278021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431958940786068972149445 1018492301397387932278021)
                    ·
                      rfl

theorem cell23_5950520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_5950520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950520 prefixEnd_5950520 := by exact prefixLift 5950520
  have htrace : WordTrace (prefixWord ++ tailWord_5950520) baseStart_5950520 baseEnd_5950520 := by
    simpa [prefixWord, tailWord_5950520, baseEnd_5950520] using wordTrace_append hprefix tailTrace_5950520
  have hstable : (prefixWord ++ tailWord_5950520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950520).length < 2 ^ (prefixWord ++ tailWord_5950520).sum := by decide
  have hdescent : baseEnd_5950520 < baseStart_5950520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950536 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_5950536 : Nat := 118140960795 + 5950536 * 2 ^ 59
def prefixEnd_5950536 : Nat := 4983230072969 + 3 ^ 40 * 5950536 * 2
def baseEnd_5950536 : Nat := 3055485119882635734233989

theorem tailTrace_5950536 : CollatzResearch.WordTrace tailWord_5950536 prefixEnd_5950536 3055485119882635734233989 := by
  unfold tailWord_5950536
  simp only [CollatzResearch.WordTrace]
  refine ⟨108516938985115908742235731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144689251980154544989647641 108516938985115908742235731)
  ·
    refine ⟨162775408477673863113353597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108516938985115908742235731 162775408477673863113353597)
    ·
      refine ⟨61040778179127698667507599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162775408477673863113353597 61040778179127698667507599)
      ·
        refine ⟨91561167268691548001261399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61040778179127698667507599 91561167268691548001261399)
        ·
          refine ⟨137341750903037322001892099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91561167268691548001261399 137341750903037322001892099)
          ·
            refine ⟨206012626354555983002838149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137341750903037322001892099 206012626354555983002838149)
            ·
              refine ⟨38627367441479246813032153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206012626354555983002838149 38627367441479246813032153)
              ·
                refine ⟨28970525581109435109774115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38627367441479246813032153 28970525581109435109774115)
                ·
                  refine ⟨43455788371664152664661173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28970525581109435109774115 43455788371664152664661173)
                  ·
                    refine ⟨4073980159843514312311985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43455788371664152664661173 4073980159843514312311985)
                    ·
                      refine ⟨3055485119882635734233989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4073980159843514312311985 3055485119882635734233989)
                      ·
                        rfl

theorem cell23_5950536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_5950536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950536 prefixEnd_5950536 := by exact prefixLift 5950536
  have htrace : WordTrace (prefixWord ++ tailWord_5950536) baseStart_5950536 baseEnd_5950536 := by
    simpa [prefixWord, tailWord_5950536, baseEnd_5950536] using wordTrace_append hprefix tailTrace_5950536
  have hstable : (prefixWord ++ tailWord_5950536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950536).length < 2 ^ (prefixWord ++ tailWord_5950536).sum := by decide
  have hdescent : baseEnd_5950536 < baseStart_5950536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950546 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_5950546 : Nat := 118140960795 + 5950546 * 2 ^ 59
def prefixEnd_5950546 : Nat := 4983230072969 + 3 ^ 40 * 5950546 * 2
def baseEnd_5950546 : Nat := 1018496751563060231702981

theorem tailTrace_5950546 : CollatzResearch.WordTrace tailWord_5950546 prefixEnd_5950546 1018496751563060231702981 := by
  unfold tailWord_5950546
  simp only [CollatzResearch.WordTrace]
  refine ⟨54258560675048897298083873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144689495133463726128223661 54258560675048897298083873)
  ·
    refine ⟨40693920506286672973562905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54258560675048897298083873 40693920506286672973562905)
    ·
      refine ⟨30520440379715004730172179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40693920506286672973562905 30520440379715004730172179)
      ·
        refine ⟨45780660569572507095258269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30520440379715004730172179 45780660569572507095258269)
        ·
          refine ⟨17167747713589690160721851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45780660569572507095258269 17167747713589690160721851)
          ·
            refine ⟨25751621570384535241082777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17167747713589690160721851 25751621570384535241082777)
            ·
              refine ⟨19313716177788401430812083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25751621570384535241082777 19313716177788401430812083)
              ·
                refine ⟨28970574266682602146218125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19313716177788401430812083 28970574266682602146218125)
                ·
                  refine ⟨10863965350005975804831797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28970574266682602146218125 10863965350005975804831797)
                  ·
                    refine ⟨1018496751563060231702981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10863965350005975804831797 1018496751563060231702981)
                    ·
                      rfl

theorem cell23_5950546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_5950546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950546 prefixEnd_5950546 := by exact prefixLift 5950546
  have htrace : WordTrace (prefixWord ++ tailWord_5950546) baseStart_5950546 baseEnd_5950546 := by
    simpa [prefixWord, tailWord_5950546, baseEnd_5950546] using wordTrace_append hprefix tailTrace_5950546
  have hstable : (prefixWord ++ tailWord_5950546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950546).length < 2 ^ (prefixWord ++ tailWord_5950546).sum := by decide
  have hdescent : baseEnd_5950546 < baseStart_5950546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950559 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 1, 6]
def baseStart_5950559 : Nat := 118140960795 + 5950559 * 2 ^ 59
def prefixEnd_5950559 : Nat := 4983230072969 + 3 ^ 40 * 5950559 * 2
def baseEnd_5950559 : Nat := 1018498976645896381415461

theorem tailTrace_5950559 : CollatzResearch.WordTrace tailWord_5950559 prefixEnd_5950559 1018498976645896381415461 := by
  unfold tailWord_5950559
  simp only [CollatzResearch.WordTrace]
  refine ⟨217034716849148492412558731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144689811232765661608372487 217034716849148492412558731)
  ·
    refine ⟨325552075273722738618838097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217034716849148492412558731 325552075273722738618838097)
    ·
      refine ⟨244164056455292053964128573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325552075273722738618838097 244164056455292053964128573)
      ·
        refine ⟨91561521170734520236548215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244164056455292053964128573 91561521170734520236548215)
        ·
          refine ⟨137342281756101780354822323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91561521170734520236548215 137342281756101780354822323)
          ·
            refine ⟨206013422634152670532233485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137342281756101780354822323 206013422634152670532233485)
            ·
              refine ⟨77255033487807251449587557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206013422634152670532233485 77255033487807251449587557)
              ·
                refine ⟨14485318778963859646797667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77255033487807251449587557 14485318778963859646797667)
                ·
                  refine ⟨21727978168445789470196501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14485318778963859646797667 21727978168445789470196501)
                  ·
                    refine ⟨1018498976645896381415461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21727978168445789470196501 1018498976645896381415461)
                    ·
                      rfl

theorem cell23_5950559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_5950559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950559 prefixEnd_5950559 := by exact prefixLift 5950559
  have htrace : WordTrace (prefixWord ++ tailWord_5950559) baseStart_5950559 baseEnd_5950559 := by
    simpa [prefixWord, tailWord_5950559, baseEnd_5950559] using wordTrace_append hprefix tailTrace_5950559
  have hstable : (prefixWord ++ tailWord_5950559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950559).length < 2 ^ (prefixWord ++ tailWord_5950559).sum := by decide
  have hdescent : baseEnd_5950559 < baseStart_5950559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950560 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 1, 1, 3]
def baseStart_5950560 : Nat := 118140960795 + 5950560 * 2 ^ 59
def prefixEnd_5950560 : Nat := 4983230072969 + 3 ^ 40 * 5950560 * 2
def baseEnd_5950560 : Nat := 3055497443418343640333879

theorem tailTrace_5950560 : CollatzResearch.WordTrace tailWord_5950560 prefixEnd_5950560 3055497443418343640333879 := by
  unfold tailWord_5950560
  simp only [CollatzResearch.WordTrace]
  refine ⟨108517376661072434791672567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144689835548096579722230089 108517376661072434791672567)
  ·
    refine ⟨162776064991608652187508851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108517376661072434791672567 162776064991608652187508851)
    ·
      refine ⟨244164097487412978281263277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162776064991608652187508851 244164097487412978281263277)
      ·
        refine ⟨91561536557779866855473729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244164097487412978281263277 91561536557779866855473729)
        ·
          refine ⟨68671152418334900141605297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91561536557779866855473729 68671152418334900141605297)
          ·
            refine ⟨51503364313751175106203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68671152418334900141605297 51503364313751175106203973)
            ·
              refine ⟨9656880808828345332413245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51503364313751175106203973 9656880808828345332413245)
              ·
                refine ⟨3621330303310629499654967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9656880808828345332413245 3621330303310629499654967)
                ·
                  refine ⟨5431995454965944249482451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621330303310629499654967 5431995454965944249482451)
                  ·
                    refine ⟨8147993182448916374223677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5431995454965944249482451 8147993182448916374223677)
                    ·
                      refine ⟨3055497443418343640333879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8147993182448916374223677 3055497443418343640333879)
                      ·
                        rfl

theorem cell23_5950560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_5950560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950560 prefixEnd_5950560 := by exact prefixLift 5950560
  have htrace : WordTrace (prefixWord ++ tailWord_5950560) baseStart_5950560 baseEnd_5950560 := by
    simpa [prefixWord, tailWord_5950560, baseEnd_5950560] using wordTrace_append hprefix tailTrace_5950560
  have hstable : (prefixWord ++ tailWord_5950560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950560).length < 2 ^ (prefixWord ++ tailWord_5950560).sum := by decide
  have hdescent : baseEnd_5950560 < baseStart_5950560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950576 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_5950576 : Nat := 118140960795 + 5950576 * 2 ^ 59
def prefixEnd_5950576 : Nat := 4983230072969 + 3 ^ 40 * 5950576 * 2
def baseEnd_5950576 : Nat := 1018501886369605192577935

theorem tailTrace_5950576 : CollatzResearch.WordTrace tailWord_5950576 prefixEnd_5950576 1018501886369605192577935 := by
  unfold tailWord_5950576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108517668445043452157963791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144690224593391269543951721 108517668445043452157963791)
  ·
    refine ⟨162776502667565178236945687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108517668445043452157963791 162776502667565178236945687)
    ·
      refine ⟨244164754001347767355418531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162776502667565178236945687 244164754001347767355418531)
      ·
        refine ⟨366247131002021651033127797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244164754001347767355418531 366247131002021651033127797)
        ·
          refine ⟨34335668531439529784355731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366247131002021651033127797 34335668531439529784355731)
          ·
            refine ⟨51503502797159294676533597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34335668531439529784355731 51503502797159294676533597)
            ·
              refine ⟨19313813548934735503700099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51503502797159294676533597 19313813548934735503700099)
              ·
                refine ⟨28970720323402103255550149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19313813548934735503700099 28970720323402103255550149)
                ·
                  refine ⟨5432010060637894360415653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28970720323402103255550149 5432010060637894360415653)
                  ·
                    refine ⟨1018501886369605192577935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432010060637894360415653 1018501886369605192577935)
                    ·
                      rfl

theorem cell23_5950576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_5950576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950576 prefixEnd_5950576 := by exact prefixLift 5950576
  have htrace : WordTrace (prefixWord ++ tailWord_5950576) baseStart_5950576 baseEnd_5950576 := by
    simpa [prefixWord, tailWord_5950576, baseEnd_5950576] using wordTrace_append hprefix tailTrace_5950576
  have hstable : (prefixWord ++ tailWord_5950576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950576).length < 2 ^ (prefixWord ++ tailWord_5950576).sum := by decide
  have hdescent : baseEnd_5950576 < baseStart_5950576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950589 : List Nat := [1, 4, 1, 1, 3, 1, 2, 10]
def baseStart_5950589 : Nat := 118140960795 + 5950589 * 2 ^ 59
def prefixEnd_5950589 : Nat := 4983230072969 + 3 ^ 40 * 5950589 * 2
def baseEnd_5950589 : Nat := 113167123494715704698935

theorem tailTrace_5950589 : CollatzResearch.WordTrace tailWord_5950589 prefixEnd_5950589 113167123494715704698935 := by
  unfold tailWord_5950589
  simp only [CollatzResearch.WordTrace]
  refine ⟨217035811039039807536150821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144690540692693205024100547 217035811039039807536150821)
  ·
    refine ⟨40694214569819963913028279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217035811039039807536150821 40694214569819963913028279)
    ·
      refine ⟨61041321854729945869542419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40694214569819963913028279 61041321854729945869542419)
      ·
        refine ⟨91561982782094918804313629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61041321854729945869542419 91561982782094918804313629)
        ·
          refine ⟨34335743543285594551617611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91561982782094918804313629 34335743543285594551617611)
          ·
            refine ⟨51503615314928391827426417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34335743543285594551617611 51503615314928391827426417)
            ·
              refine ⟨38627711486196293870569813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51503615314928391827426417 38627711486196293870569813)
              ·
                refine ⟨113167123494715704698935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38627711486196293870569813 113167123494715704698935)
                ·
                  rfl

theorem cell23_5950589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 10].length) (baseStart_5950589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950589 prefixEnd_5950589 := by exact prefixLift 5950589
  have htrace : WordTrace (prefixWord ++ tailWord_5950589) baseStart_5950589 baseEnd_5950589 := by
    simpa [prefixWord, tailWord_5950589, baseEnd_5950589] using wordTrace_append hprefix tailTrace_5950589
  have hstable : (prefixWord ++ tailWord_5950589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950589).length < 2 ^ (prefixWord ++ tailWord_5950589).sum := by decide
  have hdescent : baseEnd_5950589 < baseStart_5950589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950593 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_5950593 : Nat := 118140960795 + 5950593 * 2 ^ 59
def prefixEnd_5950593 : Nat := 4983230072969 + 3 ^ 40 * 5950593 * 2
def baseEnd_5950593 : Nat := 1018504796093314003740409

theorem tailTrace_5950593 : CollatzResearch.WordTrace tailWord_5950593 prefixEnd_5950593 1018504796093314003740409 := by
  unfold tailWord_5950593
  simp only [CollatzResearch.WordTrace]
  refine ⟨217035956931025316219296433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144690637954016877479530955 217035956931025316219296433)
  ·
    refine ⟨162776967698268987164472325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217035956931025316219296433 162776967698268987164472325)
    ·
      refine ⟨30520681443425435093338561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162776967698268987164472325 30520681443425435093338561)
      ·
        refine ⟨22890511082569076320003921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30520681443425435093338561 22890511082569076320003921)
        ·
          refine ⟨17167883311926807240002941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22890511082569076320003921 17167883311926807240002941)
          ·
            refine ⟨6437956241972552715001103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17167883311926807240002941 6437956241972552715001103)
            ·
              refine ⟨9656934362958829072501655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437956241972552715001103 9656934362958829072501655)
              ·
                refine ⟨14485401544438243608752483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656934362958829072501655 14485401544438243608752483)
                ·
                  refine ⟨21728102316657365413128725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14485401544438243608752483 21728102316657365413128725)
                  ·
                    refine ⟨1018504796093314003740409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21728102316657365413128725 1018504796093314003740409)
                    ·
                      rfl

theorem cell23_5950593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_5950593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950593 prefixEnd_5950593 := by exact prefixLift 5950593
  have htrace : WordTrace (prefixWord ++ tailWord_5950593) baseStart_5950593 baseEnd_5950593 := by
    simpa [prefixWord, tailWord_5950593, baseEnd_5950593] using wordTrace_append hprefix tailTrace_5950593
  have hstable : (prefixWord ++ tailWord_5950593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950593).length < 2 ^ (prefixWord ++ tailWord_5950593).sum := by decide
  have hdescent : baseEnd_5950593 < baseStart_5950593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950596 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5950596 : Nat := 118140960795 + 5950596 * 2 ^ 59
def prefixEnd_5950596 : Nat := 4983230072969 + 3 ^ 40 * 5950596 * 2
def baseEnd_5950596 : Nat := 3055515928721905499483713

theorem tailTrace_5950596 : CollatzResearch.WordTrace tailWord_5950596 prefixEnd_5950596 3055515928721905499483713 := by
  unfold tailWord_5950596
  simp only [CollatzResearch.WordTrace]
  refine ⟨108518033175007223865827821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144690710900009631821103761 108518033175007223865827821)
  ·
    refine ⟨40694262440627708949685433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108518033175007223865827821 40694262440627708949685433)
    ·
      refine ⟨30520696830470781712264075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40694262440627708949685433 30520696830470781712264075)
      ·
        refine ⟨45781045245706172568396113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30520696830470781712264075 45781045245706172568396113)
        ·
          refine ⟨34335783934279629426297085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45781045245706172568396113 34335783934279629426297085)
          ·
            refine ⟨12875918975354861034861407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34335783934279629426297085 12875918975354861034861407)
            ·
              refine ⟨19313878463032291552292111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12875918975354861034861407 19313878463032291552292111)
              ·
                refine ⟨28970817694548437328438167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19313878463032291552292111 28970817694548437328438167)
                ·
                  refine ⟨43456226541822655992657251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28970817694548437328438167 43456226541822655992657251)
                  ·
                    refine ⟨65184339812733983988985877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43456226541822655992657251 65184339812733983988985877)
                    ·
                      refine ⟨3055515928721905499483713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65184339812733983988985877 3055515928721905499483713)
                      ·
                        rfl

theorem cell23_5950596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5950596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950596 prefixEnd_5950596 := by exact prefixLift 5950596
  have htrace : WordTrace (prefixWord ++ tailWord_5950596) baseStart_5950596 baseEnd_5950596 := by
    simpa [prefixWord, tailWord_5950596, baseEnd_5950596] using wordTrace_append hprefix tailTrace_5950596
  have hstable : (prefixWord ++ tailWord_5950596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950596).length < 2 ^ (prefixWord ++ tailWord_5950596).sum := by decide
  have hdescent : baseEnd_5950596 < baseStart_5950596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950600 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5950600 : Nat := 118140960795 + 5950600 * 2 ^ 59
def prefixEnd_5950600 : Nat := 4983230072969 + 3 ^ 40 * 5950600 * 2
def baseEnd_5950600 : Nat := 3055517982644523483833695

theorem tailTrace_5950600 : CollatzResearch.WordTrace tailWord_5950600 prefixEnd_5950600 3055517982644523483833695 := by
  unfold tailWord_5950600
  simp only [CollatzResearch.WordTrace]
  refine ⟨108518106120999978207400627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144690808161333304276534169 108518106120999978207400627)
  ·
    refine ⟨162777159181499967311100941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108518106120999978207400627 162777159181499967311100941)
    ·
      refine ⟨61041434693062487741662853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162777159181499967311100941 61041434693062487741662853)
      ·
        refine ⟨11445269004949216451561785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61041434693062487741662853 11445269004949216451561785)
        ·
          refine ⟨8583951753711912338671339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11445269004949216451561785 8583951753711912338671339)
          ·
            refine ⟨12875927630567868508007009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8583951753711912338671339 12875927630567868508007009)
            ·
              refine ⟨9656945722925901381005257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12875927630567868508007009 9656945722925901381005257)
              ·
                refine ⟨7242709292194426035753943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9656945722925901381005257 7242709292194426035753943)
                ·
                  refine ⟨10864063938291639053630915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7242709292194426035753943 10864063938291639053630915)
                  ·
                    refine ⟨16296095907437458580446373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10864063938291639053630915 16296095907437458580446373)
                    ·
                      refine ⟨3055517982644523483833695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16296095907437458580446373 3055517982644523483833695)
                      ·
                        rfl

theorem cell23_5950600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5950600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950600 prefixEnd_5950600 := by exact prefixLift 5950600
  have htrace : WordTrace (prefixWord ++ tailWord_5950600) baseStart_5950600 baseEnd_5950600 := by
    simpa [prefixWord, tailWord_5950600, baseEnd_5950600] using wordTrace_append hprefix tailTrace_5950600
  have hstable : (prefixWord ++ tailWord_5950600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950600).length < 2 ^ (prefixWord ++ tailWord_5950600).sum := by decide
  have hdescent : baseEnd_5950600 < baseStart_5950600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950606 : List Nat := [4, 1, 1, 3, 2, 2, 1, 9]
def baseStart_5950606 : Nat := 118140960795 + 5950606 * 2 ^ 59
def prefixEnd_5950606 : Nat := 4983230072969 + 3 ^ 40 * 5950606 * 2
def baseEnd_5950606 : Nat := 113167446797350017050321

theorem tailTrace_5950606 : CollatzResearch.WordTrace tailWord_5950606 prefixEnd_5950606 113167446797350017050321 := by
  unfold tailWord_5950606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27129553884997277429939959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144690954053318812959679781 27129553884997277429939959)
  ·
    refine ⟨40694330827495916144909939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27129553884997277429939959 40694330827495916144909939)
    ·
      refine ⟨61041496241243874217364909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40694330827495916144909939 61041496241243874217364909)
      ·
        refine ⟨22890561090466452831511841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61041496241243874217364909 22890561090466452831511841)
        ·
          refine ⟨17167920817849839623633881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22890561090466452831511841 17167920817849839623633881)
          ·
            refine ⟨12875940613387379717725411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17167920817849839623633881 12875940613387379717725411)
            ·
              refine ⟨19313910920081069576588117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12875940613387379717725411 19313910920081069576588117)
              ·
                refine ⟨113167446797350017050321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19313910920081069576588117 113167446797350017050321)
                ·
                  rfl

theorem cell23_5950606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_5950606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950606 prefixEnd_5950606 := by exact prefixLift 5950606
  have htrace : WordTrace (prefixWord ++ tailWord_5950606) baseStart_5950606 baseEnd_5950606 := by
    simpa [prefixWord, tailWord_5950606, baseEnd_5950606] using wordTrace_append hprefix tailTrace_5950606
  have hstable : (prefixWord ++ tailWord_5950606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950606).length < 2 ^ (prefixWord ++ tailWord_5950606).sum := by decide
  have hdescent : baseEnd_5950606 < baseStart_5950606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950623 : List Nat := [1, 1, 2, 6, 3, 1, 9]
def baseStart_5950623 : Nat := 118140960795 + 5950623 * 2 ^ 59
def prefixEnd_5950623 : Nat := 4983230072969 + 3 ^ 40 * 5950623 * 2
def baseEnd_5950623 : Nat := 37722590033328109800569

theorem tailTrace_5950623 : CollatzResearch.WordTrace tailWord_5950623 prefixEnd_5950623 37722590033328109800569 := by
  unfold tailWord_5950623
  simp only [CollatzResearch.WordTrace]
  refine ⟨217037051120916631342888523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144691367413944420895259015 217037051120916631342888523)
  ·
    refine ⟨325555576681374947014332785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217037051120916631342888523 325555576681374947014332785)
    ·
      refine ⟨244166682511031210260749589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325555576681374947014332785 244166682511031210260749589)
      ·
        refine ⟨11445313242704587980972637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244166682511031210260749589 11445313242704587980972637)
        ·
          refine ⟨4291992466014220492864739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11445313242704587980972637 4291992466014220492864739)
          ·
            refine ⟨6437988699021330739297109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291992466014220492864739 6437988699021330739297109)
            ·
              refine ⟨37722590033328109800569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6437988699021330739297109 37722590033328109800569)
              ·
                rfl

theorem cell23_5950623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 9].length) (baseStart_5950623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950623 prefixEnd_5950623 := by exact prefixLift 5950623
  have htrace : WordTrace (prefixWord ++ tailWord_5950623) baseStart_5950623 baseEnd_5950623 := by
    simpa [prefixWord, tailWord_5950623, baseEnd_5950623] using wordTrace_append hprefix tailTrace_5950623
  have hstable : (prefixWord ++ tailWord_5950623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950623).length < 2 ^ (prefixWord ++ tailWord_5950623).sum := by decide
  have hdescent : baseEnd_5950623 < baseStart_5950623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950634 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5950634 : Nat := 118140960795 + 5950634 * 2 ^ 59
def prefixEnd_5950634 : Nat := 4983230072969 + 3 ^ 40 * 5950634 * 2
def baseEnd_5950634 : Nat := 3055535440986776350808539

theorem tailTrace_5950634 : CollatzResearch.WordTrace tailWord_5950634 prefixEnd_5950634 3055535440986776350808539 := by
  unfold tailWord_5950634
  simp only [CollatzResearch.WordTrace]
  refine ⟨54259363080969195055384739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144691634882584520147692637 54259363080969195055384739)
  ·
    refine ⟨81389044621453792583077109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54259363080969195055384739 81389044621453792583077109)
    ·
      refine ⟨7630222933261293054663479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81389044621453792583077109 7630222933261293054663479)
      ·
        refine ⟨11445334399891939581995219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630222933261293054663479 11445334399891939581995219)
        ·
          refine ⟨17168001599837909372992829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11445334399891939581995219 17168001599837909372992829)
          ·
            refine ⟨6438000599939216014872311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17168001599837909372992829 6438000599939216014872311)
            ·
              refine ⟨9657000899908824022308467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438000599939216014872311 9657000899908824022308467)
              ·
                refine ⟨14485501349863236033462701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9657000899908824022308467 14485501349863236033462701)
                ·
                  refine ⟨5432063006198713512548513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14485501349863236033462701 5432063006198713512548513)
                  ·
                    refine ⟨4074047254649035134411385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432063006198713512548513 4074047254649035134411385)
                    ·
                      refine ⟨3055535440986776350808539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074047254649035134411385 3055535440986776350808539)
                      ·
                        rfl

theorem cell23_5950634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5950634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950634 prefixEnd_5950634 := by exact prefixLift 5950634
  have htrace : WordTrace (prefixWord ++ tailWord_5950634) baseStart_5950634 baseEnd_5950634 := by
    simpa [prefixWord, tailWord_5950634, baseEnd_5950634] using wordTrace_append hprefix tailTrace_5950634
  have hstable : (prefixWord ++ tailWord_5950634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950634).length < 2 ^ (prefixWord ++ tailWord_5950634).sum := by decide
  have hdescent : baseEnd_5950634 < baseStart_5950634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950696 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 7]
def baseStart_5950696 : Nat := 118140960795 + 5950696 * 2 ^ 59
def prefixEnd_5950696 : Nat := 4983230072969 + 3 ^ 40 * 5950696 * 2
def baseEnd_5950696 : Nat := 339507475198595012025917

theorem tailTrace_5950696 : CollatzResearch.WordTrace tailWord_5950696 prefixEnd_5950696 339507475198595012025917 := by
  unfold tailWord_5950696
  simp only [CollatzResearch.WordTrace]
  refine ⟨108519856824826082405147971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144693142433101443206863961 108519856824826082405147971)
  ·
    refine ⟨162779785237239123607721957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108519856824826082405147971 162779785237239123607721957)
    ·
      refine ⟨30521209731982335676447867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162779785237239123607721957 30521209731982335676447867)
      ·
        refine ⟨45781814597973503514671801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30521209731982335676447867 45781814597973503514671801)
        ·
          refine ⟨34336360948480127636003851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45781814597973503514671801 34336360948480127636003851)
          ·
            refine ⟨51504541422720191454005777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34336360948480127636003851 51504541422720191454005777)
            ·
              refine ⟨38628406067040143590504333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51504541422720191454005777 38628406067040143590504333)
              ·
                refine ⟨14485652275140053846439125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38628406067040143590504333 14485652275140053846439125)
                ·
                  refine ⟨339507475198595012025917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14485652275140053846439125 339507475198595012025917)
                  ·
                    rfl

theorem cell23_5950696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_5950696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950696 prefixEnd_5950696 := by exact prefixLift 5950696
  have htrace : WordTrace (prefixWord ++ tailWord_5950696) baseStart_5950696 baseEnd_5950696 := by
    simpa [prefixWord, tailWord_5950696, baseEnd_5950696] using wordTrace_append hprefix tailTrace_5950696
  have hstable : (prefixWord ++ tailWord_5950696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950696).length < 2 ^ (prefixWord ++ tailWord_5950696).sum := by decide
  have hdescent : baseEnd_5950696 < baseStart_5950696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950703 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_5950703 : Nat := 118140960795 + 5950703 * 2 ^ 59
def prefixEnd_5950703 : Nat := 4983230072969 + 3 ^ 40 * 5950703 * 2
def baseEnd_5950703 : Nat := 3055570871151936580845721

theorem tailTrace_5950703 : CollatzResearch.WordTrace tailWord_5950703 prefixEnd_5950703 3055570871151936580845721 := by
  unfold tailWord_5950703
  simp only [CollatzResearch.WordTrace]
  refine ⟨217039968960626805005800763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144693312640417870003867175 217039968960626805005800763)
  ·
    refine ⟨325559953440940207508701145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217039968960626805005800763 325559953440940207508701145)
    ·
      refine ⟨244169965080705155631525859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325559953440940207508701145 244169965080705155631525859)
      ·
        refine ⟨366254947621057733447288789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244169965080705155631525859 366254947621057733447288789)
        ·
          refine ⟨8584100334868540627670831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 366254947621057733447288789 8584100334868540627670831)
          ·
            refine ⟨12876150502302810941506247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584100334868540627670831 12876150502302810941506247)
            ·
              refine ⟨19314225753454216412259371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12876150502302810941506247 19314225753454216412259371)
              ·
                refine ⟨28971338630181324618389057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19314225753454216412259371 28971338630181324618389057)
                ·
                  refine ⟨21728503972635993463791793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28971338630181324618389057 21728503972635993463791793)
                  ·
                    refine ⟨16296377979476995097843845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21728503972635993463791793 16296377979476995097843845)
                    ·
                      refine ⟨3055570871151936580845721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16296377979476995097843845 3055570871151936580845721)
                      ·
                        rfl

theorem cell23_5950703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_5950703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950703 prefixEnd_5950703 := by exact prefixLift 5950703
  have htrace : WordTrace (prefixWord ++ tailWord_5950703) baseStart_5950703 baseEnd_5950703 := by
    simpa [prefixWord, tailWord_5950703, baseEnd_5950703] using wordTrace_append hprefix tailTrace_5950703
  have hstable : (prefixWord ++ tailWord_5950703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950703).length < 2 ^ (prefixWord ++ tailWord_5950703).sum := by decide
  have hdescent : baseEnd_5950703 < baseStart_5950703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950776 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_5950776 : Nat := 118140960795 + 5950776 * 2 ^ 59
def prefixEnd_5950776 : Nat := 4983230072969 + 3 ^ 40 * 5950776 * 2
def baseEnd_5950776 : Nat := 3055608355239714795232885

theorem tailTrace_5950776 : CollatzResearch.WordTrace tailWord_5950776 prefixEnd_5950776 3055608355239714795232885 := by
  unfold tailWord_5950776
  simp only [CollatzResearch.WordTrace]
  refine ⟨108521315744681169236604091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144695087659574892315472121 108521315744681169236604091)
  ·
    refine ⟨162781973617021753854906137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108521315744681169236604091 162781973617021753854906137)
    ·
      refine ⟨122086480212766315391179603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162781973617021753854906137 122086480212766315391179603)
      ·
        refine ⟨183129720319149473086769405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122086480212766315391179603 183129720319149473086769405)
        ·
          refine ⟨68673645119681052407538527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183129720319149473086769405 68673645119681052407538527)
          ·
            refine ⟨103010467679521578611307791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68673645119681052407538527 103010467679521578611307791)
            ·
              refine ⟨154515701519282367916961687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103010467679521578611307791 154515701519282367916961687)
              ·
                refine ⟨231773552278923551875442531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154515701519282367916961687 231773552278923551875442531)
                ·
                  refine ⟨347660328418385327813163797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231773552278923551875442531 347660328418385327813163797)
                  ·
                    refine ⟨16296577894611812241242053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 347660328418385327813163797 16296577894611812241242053)
                    ·
                      refine ⟨3055608355239714795232885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16296577894611812241242053 3055608355239714795232885)
                      ·
                        rfl

theorem cell23_5950776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_5950776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950776 prefixEnd_5950776 := by exact prefixLift 5950776
  have htrace : WordTrace (prefixWord ++ tailWord_5950776) baseStart_5950776 baseEnd_5950776 := by
    simpa [prefixWord, tailWord_5950776, baseEnd_5950776] using wordTrace_append hprefix tailTrace_5950776
  have hstable : (prefixWord ++ tailWord_5950776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950776).length < 2 ^ (prefixWord ++ tailWord_5950776).sum := by decide
  have hdescent : baseEnd_5950776 < baseStart_5950776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950783 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_5950783 : Nat := 118140960795 + 5950783 * 2 ^ 59
def prefixEnd_5950783 : Nat := 4983230072969 + 3 ^ 40 * 5950783 * 2
def baseEnd_5950783 : Nat := 3055611949604296267845353

theorem tailTrace_5950783 : CollatzResearch.WordTrace tailWord_5950783 prefixEnd_5950783 3055611949604296267845353 := by
  unfold tailWord_5950783
  simp only [CollatzResearch.WordTrace]
  refine ⟨217042886800336978668713003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144695257866891319112475335 217042886800336978668713003)
  ·
    refine ⟨325564330200505468003069505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217042886800336978668713003 325564330200505468003069505)
    ·
      refine ⟨244173247650379101002302129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325564330200505468003069505 244173247650379101002302129)
      ·
        refine ⟨183129935737784325751726597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244173247650379101002302129 183129935737784325751726597)
        ·
          refine ⟨34336862950834561078448737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183129935737784325751726597 34336862950834561078448737)
          ·
            refine ⟨25752647213125920808836553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34336862950834561078448737 25752647213125920808836553)
            ·
              refine ⟨19314485409844440606627415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25752647213125920808836553 19314485409844440606627415)
              ·
                refine ⟨28971728114766660909941123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19314485409844440606627415 28971728114766660909941123)
                ·
                  refine ⟨43457592172149991364911685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28971728114766660909941123 43457592172149991364911685)
                  ·
                    refine ⟨8148298532278123380920941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43457592172149991364911685 8148298532278123380920941)
                    ·
                      refine ⟨3055611949604296267845353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8148298532278123380920941 3055611949604296267845353)
                      ·
                        rfl

theorem cell23_5950783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_5950783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950783 prefixEnd_5950783 := by exact prefixLift 5950783
  have htrace : WordTrace (prefixWord ++ tailWord_5950783) baseStart_5950783 baseEnd_5950783 := by
    simpa [prefixWord, tailWord_5950783, baseEnd_5950783] using wordTrace_append hprefix tailTrace_5950783
  have hstable : (prefixWord ++ tailWord_5950783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950783).length < 2 ^ (prefixWord ++ tailWord_5950783).sum := by decide
  have hdescent : baseEnd_5950783 < baseStart_5950783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950820 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 6]
def baseStart_5950820 : Nat := 118140960795 + 5950820 * 2 ^ 59
def prefixEnd_5950820 : Nat := 4983230072969 + 3 ^ 40 * 5950820 * 2
def baseEnd_5950820 : Nat := 339514549820945847009187

theorem tailTrace_5950820 : CollatzResearch.WordTrace tailWord_5950820 prefixEnd_5950820 339514549820945847009187 := by
  unfold tailWord_5950820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108522118150601466993904957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144696157534135289325206609 108522118150601466993904957)
  ·
    refine ⟨40695794306475550122714359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108522118150601466993904957 40695794306475550122714359)
    ·
      refine ⟨61043691459713325184071539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40695794306475550122714359 61043691459713325184071539)
      ·
        refine ⟨91565537189569987776107309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61043691459713325184071539 91565537189569987776107309)
        ·
          refine ⟨34337076446088745416040241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91565537189569987776107309 34337076446088745416040241)
          ·
            refine ⟨25752807334566559062030181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34337076446088745416040241 25752807334566559062030181)
            ·
              refine ⟨4828651375231229824130659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25752807334566559062030181 4828651375231229824130659)
              ·
                refine ⟨7242977062846844736195989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828651375231229824130659 7242977062846844736195989)
                ·
                  refine ⟨339514549820945847009187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7242977062846844736195989 339514549820945847009187)
                  ·
                    rfl

theorem cell23_5950820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_5950820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950820 prefixEnd_5950820 := by exact prefixLift 5950820
  have htrace : WordTrace (prefixWord ++ tailWord_5950820) baseStart_5950820 baseEnd_5950820 := by
    simpa [prefixWord, tailWord_5950820, baseEnd_5950820] using wordTrace_append hprefix tailTrace_5950820
  have hstable : (prefixWord ++ tailWord_5950820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950820).length < 2 ^ (prefixWord ++ tailWord_5950820).sum := by decide
  have hdescent : baseEnd_5950820 < baseStart_5950820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950880 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_5950880 : Nat := 118140960795 + 5950880 * 2 ^ 59
def prefixEnd_5950880 : Nat := 4983230072969 + 3 ^ 40 * 5950880 * 2
def baseEnd_5950880 : Nat := 1018553919075927462777469

theorem tailTrace_5950880 : CollatzResearch.WordTrace tailWord_5950880 prefixEnd_5950880 1018553919075927462777469 := by
  unfold tailWord_5950880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108523212340492782117497047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144697616453990376156662729 108523212340492782117497047)
  ·
    refine ⟨162784818510739173176245571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108523212340492782117497047 162784818510739173176245571)
    ·
      refine ⟨244177227766108759764368357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162784818510739173176245571 244177227766108759764368357)
      ·
        refine ⟨45783230206145392455819067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244177227766108759764368357 45783230206145392455819067)
        ·
          refine ⟨68674845309218088683728601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45783230206145392455819067 68674845309218088683728601)
          ·
            refine ⟨51506133981913566512796451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68674845309218088683728601 51506133981913566512796451)
            ·
              refine ⟨77259200972870349769194677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51506133981913566512796451 77259200972870349769194677)
              ·
                refine ⟨7243050091206595290862001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77259200972870349769194677 7243050091206595290862001)
                ·
                  refine ⟨5432287568404946468146501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243050091206595290862001 5432287568404946468146501)
                  ·
                    refine ⟨1018553919075927462777469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432287568404946468146501 1018553919075927462777469)
                    ·
                      rfl

theorem cell23_5950880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_5950880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950880 prefixEnd_5950880 := by exact prefixLift 5950880
  have htrace : WordTrace (prefixWord ++ tailWord_5950880) baseStart_5950880 baseEnd_5950880 := by
    simpa [prefixWord, tailWord_5950880, baseEnd_5950880] using wordTrace_append hprefix tailTrace_5950880
  have hstable : (prefixWord ++ tailWord_5950880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950880).length < 2 ^ (prefixWord ++ tailWord_5950880).sum := by decide
  have hdescent : baseEnd_5950880 < baseStart_5950880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950904 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 1, 2, 2]
def baseStart_5950904 : Nat := 118140960795 + 5950904 * 2 ^ 59
def prefixEnd_5950904 : Nat := 4983230072969 + 3 ^ 40 * 5950904 * 2
def baseEnd_5950904 : Nat := 3055674080763490294432297

theorem tailTrace_5950904 : CollatzResearch.WordTrace tailWord_5950904 prefixEnd_5950904 3055674080763490294432297 := by
  unfold tailWord_5950904
  simp only [CollatzResearch.WordTrace]
  refine ⟨108523650016449308166933883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144698200021932410889245177 108523650016449308166933883)
  ·
    refine ⟨162785475024673962250400825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108523650016449308166933883 162785475024673962250400825)
    ·
      refine ⟨122089106268505471687800619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162785475024673962250400825 122089106268505471687800619)
      ·
        refine ⟨183133659402758207531700929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122089106268505471687800619 183133659402758207531700929)
        ·
          refine ⟨137350244552068655648775697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183133659402758207531700929 137350244552068655648775697)
          ·
            refine ⟨103012683414051491736581773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137350244552068655648775697 103012683414051491736581773)
            ·
              refine ⟨38629756280269309401218165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103012683414051491736581773 38629756280269309401218165)
              ·
                refine ⟨3621539651275247756364203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38629756280269309401218165 3621539651275247756364203)
                ·
                  refine ⟨5432309476912871634546305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621539651275247756364203 5432309476912871634546305)
                  ·
                    refine ⟨4074232107684653725909729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432309476912871634546305 4074232107684653725909729)
                    ·
                      refine ⟨3055674080763490294432297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074232107684653725909729 3055674080763490294432297)
                      ·
                        rfl

theorem cell23_5950904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_5950904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950904 prefixEnd_5950904 := by exact prefixLift 5950904
  have htrace : WordTrace (prefixWord ++ tailWord_5950904) baseStart_5950904 baseEnd_5950904 := by
    simpa [prefixWord, tailWord_5950904, baseEnd_5950904] using wordTrace_append hprefix tailTrace_5950904
  have hstable : (prefixWord ++ tailWord_5950904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950904).length < 2 ^ (prefixWord ++ tailWord_5950904).sum := by decide
  have hdescent : baseEnd_5950904 < baseStart_5950904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950934 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_5950934 : Nat := 118140960795 + 5950934 * 2 ^ 59
def prefixEnd_5950934 : Nat := 4983230072969 + 3 ^ 40 * 5950934 * 2
def baseEnd_5950934 : Nat := 3055689485183125177057159

theorem tailTrace_5950934 : CollatzResearch.WordTrace tailWord_5950934 prefixEnd_5950934 3055689485183125177057159 := by
  unfold tailWord_5950934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565524638924370716091241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144698929481859954304973237 13565524638924370716091241)
  ·
    refine ⟨10174143479193278037068431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13565524638924370716091241 10174143479193278037068431)
    ·
      refine ⟨15261215218789917055602647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10174143479193278037068431 15261215218789917055602647)
      ·
        refine ⟨22891822828184875583403971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15261215218789917055602647 22891822828184875583403971)
        ·
          refine ⟨34337734242277313375105957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22891822828184875583403971 34337734242277313375105957)
          ·
            refine ⟨6438325170426996257832367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34337734242277313375105957 6438325170426996257832367)
            ·
              refine ⟨9657487755640494386748551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438325170426996257832367 9657487755640494386748551)
              ·
                refine ⟨14486231633460741580122827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9657487755640494386748551 14486231633460741580122827)
                ·
                  refine ⟨21729347450191112370184241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14486231633460741580122827 21729347450191112370184241)
                  ·
                    refine ⟨16297010587643334277638181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21729347450191112370184241 16297010587643334277638181)
                    ·
                      refine ⟨3055689485183125177057159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16297010587643334277638181 3055689485183125177057159)
                      ·
                        rfl

theorem cell23_5950934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_5950934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950934 prefixEnd_5950934 := by exact prefixLift 5950934
  have htrace : WordTrace (prefixWord ++ tailWord_5950934) baseStart_5950934 baseEnd_5950934 := by
    simpa [prefixWord, tailWord_5950934, baseEnd_5950934] using wordTrace_append hprefix tailTrace_5950934
  have hstable : (prefixWord ++ tailWord_5950934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950934).length < 2 ^ (prefixWord ++ tailWord_5950934).sum := by decide
  have hdescent : baseEnd_5950934 < baseStart_5950934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950937 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_5950937 : Nat := 118140960795 + 5950937 * 2 ^ 59
def prefixEnd_5950937 : Nat := 4983230072969 + 3 ^ 40 * 5950937 * 2
def baseEnd_5950937 : Nat := 3055691025625088665319645

theorem tailTrace_5950937 : CollatzResearch.WordTrace tailWord_5950937 prefixEnd_5950937 3055691025625088665319645 := by
  unfold tailWord_5950937
  simp only [CollatzResearch.WordTrace]
  refine ⟨217048503641779062969819065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144699002427852708646546043 217048503641779062969819065)
  ·
    refine ⟨162786377731334297227364299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217048503641779062969819065 162786377731334297227364299)
    ·
      refine ⟨244179566597001445841046449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162786377731334297227364299 244179566597001445841046449)
      ·
        refine ⟨183134674947751084380784837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244179566597001445841046449 183134674947751084380784837)
        ·
          refine ⟨34337751552703328321397157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183134674947751084380784837 34337751552703328321397157)
          ·
            refine ⟨6438328416131874060261967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34337751552703328321397157 6438328416131874060261967)
            ·
              refine ⟨9657492624197811090392951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438328416131874060261967 9657492624197811090392951)
              ·
                refine ⟨14486238936296716635589427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9657492624197811090392951 14486238936296716635589427)
                ·
                  refine ⟨21729358404445074953384141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14486238936296716635589427 21729358404445074953384141)
                  ·
                    refine ⟨8148509401666903107519053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21729358404445074953384141 8148509401666903107519053)
                    ·
                      refine ⟨3055691025625088665319645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8148509401666903107519053 3055691025625088665319645)
                      ·
                        rfl

theorem cell23_5950937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_5950937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950937 prefixEnd_5950937 := by exact prefixLift 5950937
  have htrace : WordTrace (prefixWord ++ tailWord_5950937) baseStart_5950937 baseEnd_5950937 := by
    simpa [prefixWord, tailWord_5950937, baseEnd_5950937] using wordTrace_append hprefix tailTrace_5950937
  have hstable : (prefixWord ++ tailWord_5950937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950937).length < 2 ^ (prefixWord ++ tailWord_5950937).sum := by decide
  have hdescent : baseEnd_5950937 < baseStart_5950937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950982 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5950982 : Nat := 118140960795 + 5950982 * 2 ^ 59
def prefixEnd_5950982 : Nat := 4983230072969 + 3 ^ 40 * 5950982 * 2
def baseEnd_5950982 : Nat := 1018571377418180329752313

theorem tailTrace_5950982 : CollatzResearch.WordTrace tailWord_5950982 prefixEnd_5950982 1018571377418180329752313 := by
  unfold tailWord_5950982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782817028956751114225225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144700096617744023770138133 6782817028956751114225225)
  ·
    refine ⟨5087112771717563335668919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6782817028956751114225225 5087112771717563335668919)
    ·
      refine ⟨7630669157576345003503379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087112771717563335668919 7630669157576345003503379)
      ·
        refine ⟨11446003736364517505255069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630669157576345003503379 11446003736364517505255069)
        ·
          refine ⟨4292251401136694064470651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11446003736364517505255069 4292251401136694064470651)
          ·
            refine ⟨6438377101705041096705977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292251401136694064470651 6438377101705041096705977)
            ·
              refine ⟨4828782826278780822529483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438377101705041096705977 4828782826278780822529483)
              ·
                refine ⟨7243174239418171233794225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828782826278780822529483 7243174239418171233794225)
                ·
                  refine ⟨5432380679563628425345669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243174239418171233794225 5432380679563628425345669)
                  ·
                    refine ⟨1018571377418180329752313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432380679563628425345669 1018571377418180329752313)
                    ·
                      rfl

theorem cell23_5950982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5950982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950982 prefixEnd_5950982 := by exact prefixLift 5950982
  have htrace : WordTrace (prefixWord ++ tailWord_5950982) baseStart_5950982 baseEnd_5950982 := by
    simpa [prefixWord, tailWord_5950982, baseEnd_5950982] using wordTrace_append hprefix tailTrace_5950982
  have hstable : (prefixWord ++ tailWord_5950982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950982).length < 2 ^ (prefixWord ++ tailWord_5950982).sum := by decide
  have hdescent : baseEnd_5950982 < baseStart_5950982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5950988 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_5950988 : Nat := 118140960795 + 5950988 * 2 ^ 59
def prefixEnd_5950988 : Nat := 4983230072969 + 3 ^ 40 * 5950988 * 2
def baseEnd_5950988 : Nat := 3055717213138467965781911

theorem tailTrace_5950988 : CollatzResearch.WordTrace tailWord_5950988 prefixEnd_5950988 3055717213138467965781911 := by
  unfold tailWord_5950988
  simp only [CollatzResearch.WordTrace]
  refine ⟨108525181882297149339962809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144700242509729532453283745 108525181882297149339962809)
  ·
    refine ⟨81393886411722862004972107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108525181882297149339962809 81393886411722862004972107)
    ·
      refine ⟨122090829617584293007458161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81393886411722862004972107 122090829617584293007458161)
      ·
        refine ⟨91568122213188219755593621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122090829617584293007458161 91568122213188219755593621)
        ·
          refine ⟨4292255728743197801043451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91568122213188219755593621 4292255728743197801043451)
          ·
            refine ⟨6438383593114796701565177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292255728743197801043451 6438383593114796701565177)
            ·
              refine ⟨4828787694836097526173883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438383593114796701565177 4828787694836097526173883)
              ·
                refine ⟨7243181542254146289260825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828787694836097526173883 7243181542254146289260825)
                ·
                  refine ⟨5432386156690609716945619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243181542254146289260825 5432386156690609716945619)
                  ·
                    refine ⟨8148579235035914575418429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5432386156690609716945619 8148579235035914575418429)
                    ·
                      refine ⟨3055717213138467965781911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8148579235035914575418429 3055717213138467965781911)
                      ·
                        rfl

theorem cell23_5950988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_5950988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5950988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5950988 prefixEnd_5950988 := by exact prefixLift 5950988
  have htrace : WordTrace (prefixWord ++ tailWord_5950988) baseStart_5950988 baseEnd_5950988 := by
    simpa [prefixWord, tailWord_5950988, baseEnd_5950988] using wordTrace_append hprefix tailTrace_5950988
  have hstable : (prefixWord ++ tailWord_5950988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5950988).length < 2 ^ (prefixWord ++ tailWord_5950988).sum := by decide
  have hdescent : baseEnd_5950988 < baseStart_5950988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5950988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951043 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 8]
def baseStart_5951043 : Nat := 118140960795 + 5951043 * 2 ^ 59
def prefixEnd_5951043 : Nat := 4983230072969 + 3 ^ 40 * 5951043 * 2
def baseEnd_5951043 : Nat := 1018581818191488416864719

theorem tailTrace_5951043 : CollatzResearch.WordTrace tailWord_5951043 prefixEnd_5951043 1018581818191488416864719 := by
  unfold tailWord_5951043
  simp only [CollatzResearch.WordTrace]
  refine ⟨217052369779395043073177783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144701579852930028715451855 217052369779395043073177783)
  ·
    refine ⟨325578554669092564609766675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217052369779395043073177783 325578554669092564609766675)
    ·
      refine ⟨488367832003638846914650013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325578554669092564609766675 488367832003638846914650013)
      ·
        refine ⟨183137937001364567592993755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488367832003638846914650013 183137937001364567592993755)
        ·
          refine ⟨274706905502046851389490633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183137937001364567592993755 274706905502046851389490633)
          ·
            refine ⟨206030179126535138542117975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274706905502046851389490633 206030179126535138542117975)
            ·
              refine ⟨309045268689802707813176963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206030179126535138542117975 309045268689802707813176963)
              ·
                refine ⟨463567903034704061719765445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309045268689802707813176963 463567903034704061719765445)
                ·
                  refine ⟨86918981819007011572456021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463567903034704061719765445 86918981819007011572456021)
                  ·
                    refine ⟨1018581818191488416864719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86918981819007011572456021 1018581818191488416864719)
                    ·
                      rfl

theorem cell23_5951043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_5951043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951043 prefixEnd_5951043 := by exact prefixLift 5951043
  have htrace : WordTrace (prefixWord ++ tailWord_5951043) baseStart_5951043 baseEnd_5951043 := by
    simpa [prefixWord, tailWord_5951043, baseEnd_5951043] using wordTrace_append hprefix tailTrace_5951043
  have hstable : (prefixWord ++ tailWord_5951043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951043).length < 2 ^ (prefixWord ++ tailWord_5951043).sum := by decide
  have hdescent : baseEnd_5951043 < baseStart_5951043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
