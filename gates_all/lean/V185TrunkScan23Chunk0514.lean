import V185TrunkScan23Chunk0513

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3039196 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3039196 : Nat := 118140960795 + 3039196 * 2 ^ 59
def prefixEnd_3039196 : Nat := 4983230072969 + 3 ^ 40 * 3039196 * 2
def baseEnd_3039196 : Nat := 1560568351221996365372999

theorem tailTrace_3039196 : CollatzResearch.WordTrace tailWord_3039196 prefixEnd_3039196 1560568351221996365372999 := by
  unfold tailWord_3039196
  simp only [CollatzResearch.WordTrace]
  refine ⟨55424292348759710098980721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73899056465012946798640961 55424292348759710098980721)
  ·
    refine ⟨41568219261569782574235541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55424292348759710098980721 41568219261569782574235541)
    ·
      refine ⟨1948510277886083558167291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41568219261569782574235541 1948510277886083558167291)
      ·
        refine ⟨2922765416829125337250937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948510277886083558167291 2922765416829125337250937)
        ·
          refine ⟨2192074062621844002938203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922765416829125337250937 2192074062621844002938203)
          ·
            refine ⟨3288111093932766004407305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192074062621844002938203 3288111093932766004407305)
            ·
              refine ⟨2466083320449574503305479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3288111093932766004407305 2466083320449574503305479)
              ·
                refine ⟨3699124980674361754958219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466083320449574503305479 3699124980674361754958219)
                ·
                  refine ⟨5548687471011542632437329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699124980674361754958219 5548687471011542632437329)
                  ·
                    refine ⟨4161515603258656974327997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548687471011542632437329 4161515603258656974327997)
                    ·
                      refine ⟨1560568351221996365372999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4161515603258656974327997 1560568351221996365372999)
                      ·
                        rfl

theorem cell23_3039196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3039196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039196 prefixEnd_3039196 := by exact prefixLift 3039196
  have htrace : WordTrace (prefixWord ++ tailWord_3039196) baseStart_3039196 baseEnd_3039196 := by
    simpa [prefixWord, tailWord_3039196, baseEnd_3039196] using wordTrace_append hprefix tailTrace_3039196
  have hstable : (prefixWord ++ tailWord_3039196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039196).length < 2 ^ (prefixWord ++ tailWord_3039196).sum := by decide
  have hdescent : baseEnd_3039196 < baseStart_3039196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039202 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3039202 : Nat := 118140960795 + 3039202 * 2 ^ 59
def prefixEnd_3039202 : Nat := 4983230072969 + 3 ^ 40 * 3039202 * 2
def baseEnd_3039202 : Nat := 1560571432105923341897971

theorem tailTrace_3039202 : CollatzResearch.WordTrace tailWord_3039202 prefixEnd_3039202 1560571432105923341897971 := by
  unfold tailWord_3039202
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712200883874420805669965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73899202356998455481786573 27712200883874420805669965)
  ·
    refine ⟨10392075331452907802126237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27712200883874420805669965 10392075331452907802126237)
    ·
      refine ⟨3897028249294840425797339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10392075331452907802126237 3897028249294840425797339)
      ·
        refine ⟨5845542373942260638696009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897028249294840425797339 5845542373942260638696009)
        ·
          refine ⟨4384156780456695479022007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5845542373942260638696009 4384156780456695479022007)
          ·
            refine ⟨6576235170685043218533011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384156780456695479022007 6576235170685043218533011)
            ·
              refine ⟨9864352756027564827799517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576235170685043218533011 9864352756027564827799517)
              ·
                refine ⟨3699132283510336810424819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9864352756027564827799517 3699132283510336810424819)
                ·
                  refine ⟨5548698425265505215637229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699132283510336810424819 5548698425265505215637229)
                  ·
                    refine ⟨2080761909474564455863961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5548698425265505215637229 2080761909474564455863961)
                    ·
                      refine ⟨1560571432105923341897971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080761909474564455863961 1560571432105923341897971)
                      ·
                        rfl

theorem cell23_3039202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3039202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039202 prefixEnd_3039202 := by exact prefixLift 3039202
  have htrace : WordTrace (prefixWord ++ tailWord_3039202) baseStart_3039202 baseEnd_3039202 := by
    simpa [prefixWord, tailWord_3039202, baseEnd_3039202] using wordTrace_append hprefix tailTrace_3039202
  have hstable : (prefixWord ++ tailWord_3039202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039202).length < 2 ^ (prefixWord ++ tailWord_3039202).sum := by decide
  have hdescent : baseEnd_3039202 < baseStart_3039202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039255 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 5]
def baseStart_3039255 : Nat := 118140960795 + 3039255 * 2 ^ 59
def prefixEnd_3039255 : Nat := 4983230072969 + 3 ^ 40 * 3039255 * 2
def baseEnd_3039255 : Nat := 173399849620067959392803

theorem tailTrace_3039255 : CollatzResearch.WordTrace tailWord_3039255 prefixEnd_3039255 173399849620067959392803 := by
  unfold tailWord_3039255
  simp only [CollatzResearch.WordTrace]
  refine ⟨110850736604305673274359219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73900491069537115516239479 110850736604305673274359219)
  ·
    refine ⟨166276104906458509911538829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110850736604305673274359219 166276104906458509911538829)
    ·
      refine ⟨62353539339921941216827061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166276104906458509911538829 62353539339921941216827061)
      ·
        refine ⟨5845644313117681989077537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62353539339921941216827061 5845644313117681989077537)
        ·
          refine ⟨4384233234838261491808153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5845644313117681989077537 4384233234838261491808153)
          ·
            refine ⟨3288174926128696118856115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4384233234838261491808153 3288174926128696118856115)
            ·
              refine ⟨4932262389193044178284173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288174926128696118856115 4932262389193044178284173)
              ·
                refine ⟨1849598395947391566856565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4932262389193044178284173 1849598395947391566856565)
                ·
                  refine ⟨173399849620067959392803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1849598395947391566856565 173399849620067959392803)
                  ·
                    rfl

theorem cell23_3039255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 5].length) (baseStart_3039255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039255 prefixEnd_3039255 := by exact prefixLift 3039255
  have htrace : WordTrace (prefixWord ++ tailWord_3039255) baseStart_3039255 baseEnd_3039255 := by
    simpa [prefixWord, tailWord_3039255, baseEnd_3039255] using wordTrace_append hprefix tailTrace_3039255
  have hstable : (prefixWord ++ tailWord_3039255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039255).length < 2 ^ (prefixWord ++ tailWord_3039255).sum := by decide
  have hdescent : baseEnd_3039255 < baseStart_3039255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039268 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_3039268 : Nat := 118140960795 + 3039268 * 2 ^ 59
def prefixEnd_3039268 : Nat := 4983230072969 + 3 ^ 40 * 3039268 * 2
def baseEnd_3039268 : Nat := 520201773943040027890889

theorem tailTrace_3039268 : CollatzResearch.WordTrace tailWord_3039268 prefixEnd_3039268 520201773943040027890889 := by
  unfold tailWord_3039268
  simp only [CollatzResearch.WordTrace]
  refine ⟨55425605376629288247291229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73900807168839050996388305 55425605376629288247291229)
  ·
    refine ⟨20784602016235983092734211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55425605376629288247291229 20784602016235983092734211)
    ·
      refine ⟨31176903024353974639101317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20784602016235983092734211 31176903024353974639101317)
      ·
        refine ⟨5845669317066370244831497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31176903024353974639101317 5845669317066370244831497)
        ·
          refine ⟨4384251987799777683623623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5845669317066370244831497 4384251987799777683623623)
          ·
            refine ⟨6576377981699666525435435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384251987799777683623623 6576377981699666525435435)
            ·
              refine ⟨9864566972549499788153153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576377981699666525435435 9864566972549499788153153)
              ·
                refine ⟨7398425229412124841114865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9864566972549499788153153 7398425229412124841114865)
                ·
                  refine ⟨5548818922059093630836149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398425229412124841114865 5548818922059093630836149)
                  ·
                    refine ⟨520201773943040027890889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5548818922059093630836149 520201773943040027890889)
                    ·
                      rfl

theorem cell23_3039268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_3039268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039268 prefixEnd_3039268 := by exact prefixLift 3039268
  have htrace : WordTrace (prefixWord ++ tailWord_3039268) baseStart_3039268 baseEnd_3039268 := by
    simpa [prefixWord, tailWord_3039268, baseEnd_3039268] using wordTrace_append hprefix tailTrace_3039268
  have hstable : (prefixWord ++ tailWord_3039268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039268).length < 2 ^ (prefixWord ++ tailWord_3039268).sum := by decide
  have hdescent : baseEnd_3039268 < baseStart_3039268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039272 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 5]
def baseStart_3039272 : Nat := 118140960795 + 3039272 * 2 ^ 59
def prefixEnd_3039272 : Nat := 4983230072969 + 3 ^ 40 * 3039272 * 2
def baseEnd_3039272 : Nat := 173400819527970896446961

theorem tailTrace_3039272 : CollatzResearch.WordTrace tailWord_3039272 prefixEnd_3039272 173400819527970896446961 := by
  unfold tailWord_3039272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55425678322622042588864035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73900904430162723451818713 55425678322622042588864035)
  ·
    refine ⟨83138517483933063883296053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55425678322622042588864035 83138517483933063883296053)
    ·
      refine ⟨7794236014118724739059005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83138517483933063883296053 7794236014118724739059005)
      ·
        refine ⟨2922838505294521777147127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7794236014118724739059005 2922838505294521777147127)
        ·
          refine ⟨4384257757941782665720691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922838505294521777147127 4384257757941782665720691)
          ·
            refine ⟨6576386636912673998581037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384257757941782665720691 6576386636912673998581037)
            ·
              refine ⟨2466144988842252749467889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6576386636912673998581037 2466144988842252749467889)
              ·
                refine ⟨1849608741631689562100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2466144988842252749467889 1849608741631689562100917)
                ·
                  refine ⟨173400819527970896446961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1849608741631689562100917 173400819527970896446961)
                  ·
                    rfl

theorem cell23_3039272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 5].length) (baseStart_3039272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039272 prefixEnd_3039272 := by exact prefixLift 3039272
  have htrace : WordTrace (prefixWord ++ tailWord_3039272) baseStart_3039272 baseEnd_3039272 := by
    simpa [prefixWord, tailWord_3039272, baseEnd_3039272] using wordTrace_append hprefix tailTrace_3039272
  have hstable : (prefixWord ++ tailWord_3039272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039272).length < 2 ^ (prefixWord ++ tailWord_3039272).sum := by decide
  have hdescent : baseEnd_3039272 < baseStart_3039272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039325 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3039325 : Nat := 118140960795 + 3039325 * 2 ^ 59
def prefixEnd_3039325 : Nat := 4983230072969 + 3 ^ 40 * 3039325 * 2
def baseEnd_3039325 : Nat := 1560634590226426360659905

theorem tailTrace_3039325 : CollatzResearch.WordTrace tailWord_3039325 prefixEnd_3039325 1560634590226426360659905 := by
  unfold tailWord_3039325
  simp only [CollatzResearch.WordTrace]
  refine ⟨110853289714052075229407429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73902193142701383486271619 110853289714052075229407429)
  ·
    refine ⟨20784991821384764105513893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110853289714052075229407429 20784991821384764105513893)
    ·
      refine ⟨3897185966509643269783855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20784991821384764105513893 3897185966509643269783855)
      ·
        refine ⟨5845778949764464904675783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897185966509643269783855 5845778949764464904675783)
        ·
          refine ⟨8768668424646697357013675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845778949764464904675783 8768668424646697357013675)
          ·
            refine ⟨13153002636970046035520513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768668424646697357013675 13153002636970046035520513)
            ·
              refine ⟨9864751977727534526640385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13153002636970046035520513 9864751977727534526640385)
              ·
                refine ⟨7398563983295650894980289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9864751977727534526640385 7398563983295650894980289)
                ·
                  refine ⟨5548922987471738171235217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398563983295650894980289 5548922987471738171235217)
                  ·
                    refine ⟨4161692240603803628426413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548922987471738171235217 4161692240603803628426413)
                    ·
                      refine ⟨1560634590226426360659905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4161692240603803628426413 1560634590226426360659905)
                      ·
                        rfl

theorem cell23_3039325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3039325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039325 prefixEnd_3039325 := by exact prefixLift 3039325
  have htrace : WordTrace (prefixWord ++ tailWord_3039325) baseStart_3039325 baseEnd_3039325 := by
    simpa [prefixWord, tailWord_3039325, baseEnd_3039325] using wordTrace_append hprefix tailTrace_3039325
  have hstable : (prefixWord ++ tailWord_3039325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039325).length < 2 ^ (prefixWord ++ tailWord_3039325).sum := by decide
  have hdescent : baseEnd_3039325 < baseStart_3039325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039341 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3039341 : Nat := 118140960795 + 3039341 * 2 ^ 59
def prefixEnd_3039341 : Nat := 4983230072969 + 3 ^ 40 * 3039341 * 2
def baseEnd_3039341 : Nat := 520214268638966099353277

theorem tailTrace_3039341 : CollatzResearch.WordTrace tailWord_3039341 prefixEnd_3039341 520214268638966099353277 := by
  unfold tailWord_3039341
  simp only [CollatzResearch.WordTrace]
  refine ⟨110853873281994109961989877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73902582187996073307993251 110853873281994109961989877)
  ·
    refine ⟨10392550620186947808936551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110853873281994109961989877 10392550620186947808936551)
    ·
      refine ⟨15588825930280421713404827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392550620186947808936551 15588825930280421713404827)
      ·
        refine ⟨23383238895420632570107241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15588825930280421713404827 23383238895420632570107241)
        ·
          refine ⟨17537429171565474427580431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23383238895420632570107241 17537429171565474427580431)
          ·
            refine ⟨26306143757348211641370647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17537429171565474427580431 26306143757348211641370647)
            ·
              refine ⟨39459215636022317462055971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26306143757348211641370647 39459215636022317462055971)
              ·
                refine ⟨59188823454033476193083957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39459215636022317462055971 59188823454033476193083957)
                ·
                  refine ⟨5548952198815638393101621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59188823454033476193083957 5548952198815638393101621)
                  ·
                    refine ⟨520214268638966099353277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5548952198815638393101621 520214268638966099353277)
                    ·
                      rfl

theorem cell23_3039341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3039341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039341 prefixEnd_3039341 := by exact prefixLift 3039341
  have htrace : WordTrace (prefixWord ++ tailWord_3039341) baseStart_3039341 baseEnd_3039341 := by
    simpa [prefixWord, tailWord_3039341, baseEnd_3039341] using wordTrace_append hprefix tailTrace_3039341
  have hstable : (prefixWord ++ tailWord_3039341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039341).length < 2 ^ (prefixWord ++ tailWord_3039341).sum := by decide
  have hdescent : baseEnd_3039341 < baseStart_3039341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039365 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_3039365 : Nat := 118140960795 + 3039365 * 2 ^ 59
def prefixEnd_3039365 : Nat := 4983230072969 + 3 ^ 40 * 3039365 * 2
def baseEnd_3039365 : Nat := 1560655129452606204159721

theorem tailTrace_3039365 : CollatzResearch.WordTrace tailWord_3039365 prefixEnd_3039365 1560655129452606204159721 := by
  unfold tailWord_3039365
  simp only [CollatzResearch.WordTrace]
  refine ⟨110854748633907162060863549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73903165755938108040575699 110854748633907162060863549)
  ·
    refine ⟨41570530737715185772823831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110854748633907162060863549 41570530737715185772823831)
    ·
      refine ⟨62355796106572778659235747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41570530737715185772823831 62355796106572778659235747)
      ·
        refine ⟨93533694159859167988853621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62355796106572778659235747 93533694159859167988853621)
        ·
          refine ⟨8768783827486796998955027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93533694159859167988853621 8768783827486796998955027)
          ·
            refine ⟨13153175741230195498432541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768783827486796998955027 13153175741230195498432541)
            ·
              refine ⟨4932440902961323311912203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13153175741230195498432541 4932440902961323311912203)
              ·
                refine ⟨7398661354441984967868305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932440902961323311912203 7398661354441984967868305)
                ·
                  refine ⟨5548996015831488725901229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398661354441984967868305 5548996015831488725901229)
                  ·
                    refine ⟨2080873505936808272212961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5548996015831488725901229 2080873505936808272212961)
                    ·
                      refine ⟨1560655129452606204159721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080873505936808272212961 1560655129452606204159721)
                      ·
                        rfl

theorem cell23_3039365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_3039365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039365 prefixEnd_3039365 := by exact prefixLift 3039365
  have htrace : WordTrace (prefixWord ++ tailWord_3039365) baseStart_3039365 baseEnd_3039365 := by
    simpa [prefixWord, tailWord_3039365, baseEnd_3039365] using wordTrace_append hprefix tailTrace_3039365
  have hstable : (prefixWord ++ tailWord_3039365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039365).length < 2 ^ (prefixWord ++ tailWord_3039365).sum := by decide
  have hdescent : baseEnd_3039365 < baseStart_3039365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039381 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3039381 : Nat := 118140960795 + 3039381 * 2 ^ 59
def prefixEnd_3039381 : Nat := 4983230072969 + 3 ^ 40 * 3039381 * 2
def baseEnd_3039381 : Nat := 1560663345143078141559647

theorem tailTrace_3039381 : CollatzResearch.WordTrace tailWord_3039381 prefixEnd_3039381 1560663345143078141559647 := by
  unfold tailWord_3039381
  simp only [CollatzResearch.WordTrace]
  refine ⟨110855332201849196793445997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73903554801232797862297331 110855332201849196793445997)
  ·
    refine ⟨41570749575693448797542249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110855332201849196793445997 41570749575693448797542249)
    ·
      refine ⟨31178062181770086598156687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41570749575693448797542249 31178062181770086598156687)
      ·
        refine ⟨46767093272655129897235031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31178062181770086598156687 46767093272655129897235031)
        ·
          refine ⟨70150639908982694845852547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46767093272655129897235031 70150639908982694845852547)
          ·
            refine ⟨105225959863474042268778821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70150639908982694845852547 105225959863474042268778821)
            ·
              refine ⟨19729867474401382925396029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105225959863474042268778821 19729867474401382925396029)
              ·
                refine ⟨7398700302900518597023511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19729867474401382925396029 7398700302900518597023511)
                ·
                  refine ⟨11098050454350777895535267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398700302900518597023511 11098050454350777895535267)
                  ·
                    refine ⟨16647075681526166843302901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11098050454350777895535267 16647075681526166843302901)
                    ·
                      refine ⟨1560663345143078141559647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16647075681526166843302901 1560663345143078141559647)
                      ·
                        rfl

theorem cell23_3039381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3039381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039381 prefixEnd_3039381 := by exact prefixLift 3039381
  have htrace : WordTrace (prefixWord ++ tailWord_3039381) baseStart_3039381 baseEnd_3039381 := by
    simpa [prefixWord, tailWord_3039381, baseEnd_3039381] using wordTrace_append hprefix tailTrace_3039381
  have hstable : (prefixWord ++ tailWord_3039381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039381).length < 2 ^ (prefixWord ++ tailWord_3039381).sum := by decide
  have hdescent : baseEnd_3039381 < baseStart_3039381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039388 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3039388 : Nat := 118140960795 + 3039388 * 2 ^ 59
def prefixEnd_3039388 : Nat := 4983230072969 + 3 ^ 40 * 3039388 * 2
def baseEnd_3039388 : Nat := 520222313169219871390705

theorem tailTrace_3039388 : CollatzResearch.WordTrace tailWord_3039388 prefixEnd_3039388 520222313169219871390705 := by
  unfold tailWord_3039388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55427793756411918494475409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73903725008549224659300545 55427793756411918494475409)
  ·
    refine ⟨41570845317308938870856557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55427793756411918494475409 41570845317308938870856557)
    ·
      refine ⟨15589066993990852076571209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41570845317308938870856557 15589066993990852076571209)
      ·
        refine ⟨11691800245493139057428407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15589066993990852076571209 11691800245493139057428407)
        ·
          refine ⟨17537700368239708586142611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11691800245493139057428407 17537700368239708586142611)
          ·
            refine ⟨26306550552359562879213917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17537700368239708586142611 26306550552359562879213917)
            ·
              refine ⟨9864956457134836079705219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26306550552359562879213917 9864956457134836079705219)
              ·
                refine ⟨14797434685702254119557829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864956457134836079705219 14797434685702254119557829)
                ·
                  refine ⟨2774519003569172647417093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14797434685702254119557829 2774519003569172647417093)
                  ·
                    refine ⟨520222313169219871390705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774519003569172647417093 520222313169219871390705)
                    ·
                      rfl

theorem cell23_3039388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3039388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039388 prefixEnd_3039388 := by exact prefixLift 3039388
  have htrace : WordTrace (prefixWord ++ tailWord_3039388) baseStart_3039388 baseEnd_3039388 := by
    simpa [prefixWord, tailWord_3039388, baseEnd_3039388] using wordTrace_append hprefix tailTrace_3039388
  have hstable : (prefixWord ++ tailWord_3039388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039388).length < 2 ^ (prefixWord ++ tailWord_3039388).sum := by decide
  have hdescent : baseEnd_3039388 < baseStart_3039388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039405 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3039405 : Nat := 118140960795 + 3039405 * 2 ^ 59
def prefixEnd_3039405 : Nat := 4983230072969 + 3 ^ 40 * 3039405 * 2
def baseEnd_3039405 : Nat := 520225222892928682553179

theorem tailTrace_3039405 : CollatzResearch.WordTrace tailWord_3039405 prefixEnd_3039405 520225222892928682553179 := by
  unfold tailWord_3039405
  simp only [CollatzResearch.WordTrace]
  refine ⟨110856207553762248892319669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73904138369174832594879779 110856207553762248892319669)
  ·
    refine ⟨10392769458165210833654969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110856207553762248892319669 10392769458165210833654969)
    ·
      refine ⟨7794577093623908125241227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10392769458165210833654969 7794577093623908125241227)
      ·
        refine ⟨11691865640435862187861841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7794577093623908125241227 11691865640435862187861841)
        ·
          refine ⟨8768899230326896640896381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11691865640435862187861841 8768899230326896640896381)
          ·
            refine ⟨3288337211372586240336143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8768899230326896640896381 3288337211372586240336143)
            ·
              refine ⟨4932505817058879360504215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288337211372586240336143 4932505817058879360504215)
              ·
                refine ⟨7398758725588319040756323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932505817058879360504215 7398758725588319040756323)
                ·
                  refine ⟨11098138088382478561134485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398758725588319040756323 11098138088382478561134485)
                  ·
                    refine ⟨520225222892928682553179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11098138088382478561134485 520225222892928682553179)
                    ·
                      rfl

theorem cell23_3039405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3039405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039405 prefixEnd_3039405 := by exact prefixLift 3039405
  have htrace : WordTrace (prefixWord ++ tailWord_3039405) baseStart_3039405 baseEnd_3039405 := by
    simpa [prefixWord, tailWord_3039405, baseEnd_3039405] using wordTrace_append hprefix tailTrace_3039405
  have hstable : (prefixWord ++ tailWord_3039405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039405).length < 2 ^ (prefixWord ++ tailWord_3039405).sum := by decide
  have hdescent : baseEnd_3039405 < baseStart_3039405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039415 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_3039415 : Nat := 118140960795 + 3039415 * 2 ^ 59
def prefixEnd_3039415 : Nat := 4983230072969 + 3 ^ 40 * 3039415 * 2
def baseEnd_3039415 : Nat := 1560680803485331008534491

theorem tailTrace_3039415 : CollatzResearch.WordTrace tailWord_3039415 prefixEnd_3039415 1560680803485331008534491 := by
  unfold tailWord_3039415
  simp only [CollatzResearch.WordTrace]
  refine ⟨110856572283726020600183699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73904381522484013733455799 110856572283726020600183699)
  ·
    refine ⟨166284858425589030900275549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110856572283726020600183699 166284858425589030900275549)
    ·
      refine ⟨62356821909595886587603331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166284858425589030900275549 62356821909595886587603331)
      ·
        refine ⟨93535232864393829881404997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62356821909595886587603331 93535232864393829881404997)
        ·
          refine ⟨17537856162073843102763437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93535232864393829881404997 17537856162073843102763437)
          ·
            refine ⟨6576696060777691163536289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17537856162073843102763437 6576696060777691163536289)
            ·
              refine ⟨4932522045583268372652217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6576696060777691163536289 4932522045583268372652217)
              ·
                refine ⟨3699391534187451279489163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932522045583268372652217 3699391534187451279489163)
                ·
                  refine ⟨5549087301281176919233745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699391534187451279489163 5549087301281176919233745)
                  ·
                    refine ⟨4161815475960882689425309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549087301281176919233745 4161815475960882689425309)
                    ·
                      refine ⟨1560680803485331008534491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4161815475960882689425309 1560680803485331008534491)
                      ·
                        rfl

theorem cell23_3039415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_3039415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039415 prefixEnd_3039415 := by exact prefixLift 3039415
  have htrace : WordTrace (prefixWord ++ tailWord_3039415) baseStart_3039415 baseEnd_3039415 := by
    simpa [prefixWord, tailWord_3039415, baseEnd_3039415] using wordTrace_append hprefix tailTrace_3039415
  have hstable : (prefixWord ++ tailWord_3039415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039415).length < 2 ^ (prefixWord ++ tailWord_3039415).sum := by decide
  have hdescent : baseEnd_3039415 < baseStart_3039415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039446 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3039446 : Nat := 118140960795 + 3039446 * 2 ^ 59
def prefixEnd_3039446 : Nat := 4983230072969 + 3 ^ 40 * 3039446 * 2
def baseEnd_3039446 : Nat := 1560696721385620387246849

theorem tailTrace_3039446 : CollatzResearch.WordTrace tailWord_3039446 prefixEnd_3039446 1560696721385620387246849 := by
  unfold tailWord_3039446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928606434163357055910137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73905135297742475263041461 6928606434163357055910137)
  ·
    refine ⟨5196454825622517791932603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6928606434163357055910137 5196454825622517791932603)
    ·
      refine ⟨7794682238433776687898905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196454825622517791932603 7794682238433776687898905)
      ·
        refine ⟨5846011678825332515924179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794682238433776687898905 5846011678825332515924179)
        ·
          refine ⟨8769017518237998773886269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846011678825332515924179 8769017518237998773886269)
          ·
            refine ⟨3288381569339249540207351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8769017518237998773886269 3288381569339249540207351)
            ·
              refine ⟨4932572354008874310311027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288381569339249540207351 4932572354008874310311027)
              ·
                refine ⟨7398858531013311465466541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932572354008874310311027 7398858531013311465466541)
                ·
                  refine ⟨2774571949129991799549953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7398858531013311465466541 2774571949129991799549953)
                  ·
                    refine ⟨2080928961847493849662465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774571949129991799549953 2080928961847493849662465)
                    ·
                      refine ⟨1560696721385620387246849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080928961847493849662465 1560696721385620387246849)
                      ·
                        rfl

theorem cell23_3039446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3039446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039446 prefixEnd_3039446 := by exact prefixLift 3039446
  have htrace : WordTrace (prefixWord ++ tailWord_3039446) baseStart_3039446 baseEnd_3039446 := by
    simpa [prefixWord, tailWord_3039446, baseEnd_3039446] using wordTrace_append hprefix tailTrace_3039446
  have hstable : (prefixWord ++ tailWord_3039446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039446).length < 2 ^ (prefixWord ++ tailWord_3039446).sum := by decide
  have hdescent : baseEnd_3039446 < baseStart_3039446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039481 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3039481 : Nat := 118140960795 + 3039481 * 2 ^ 59
def prefixEnd_3039481 : Nat := 4983230072969 + 3 ^ 40 * 3039481 * 2
def baseEnd_3039481 : Nat := 1560714693208527750309187

theorem tailTrace_3039481 : CollatzResearch.WordTrace tailWord_3039481 prefixEnd_3039481 1560714693208527750309187 := by
  unfold tailWord_3039481
  simp only [CollatzResearch.WordTrace]
  refine ⟨110858979501486913872086297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73905986334324609248057531 110858979501486913872086297)
  ·
    refine ⟨83144234626115185404064723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110858979501486913872086297 83144234626115185404064723)
    ·
      refine ⟨124716351939172778106097085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83144234626115185404064723 124716351939172778106097085)
      ·
        refine ⟨46768631977189791789786407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124716351939172778106097085 46768631977189791789786407)
        ·
          refine ⟨70152947965784687684679611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46768631977189791789786407 70152947965784687684679611)
          ·
            refine ⟨105229421948677031527019417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70152947965784687684679611 105229421948677031527019417)
            ·
              refine ⟨78922066461507773645264563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105229421948677031527019417 78922066461507773645264563)
              ·
                refine ⟨118383099692261660467896845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78922066461507773645264563 118383099692261660467896845)
                ·
                  refine ⟨44393662384598122675461317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118383099692261660467896845 44393662384598122675461317)
                  ·
                    refine ⟨8323811697112148001648997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44393662384598122675461317 8323811697112148001648997)
                    ·
                      refine ⟨1560714693208527750309187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8323811697112148001648997 1560714693208527750309187)
                      ·
                        rfl

theorem cell23_3039481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3039481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039481 prefixEnd_3039481 := by exact prefixLift 3039481
  have htrace : WordTrace (prefixWord ++ tailWord_3039481) baseStart_3039481 baseEnd_3039481 := by
    simpa [prefixWord, tailWord_3039481, baseEnd_3039481] using wordTrace_append hprefix tailTrace_3039481
  have hstable : (prefixWord ++ tailWord_3039481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039481).length < 2 ^ (prefixWord ++ tailWord_3039481).sum := by decide
  have hdescent : baseEnd_3039481 < baseStart_3039481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039485 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_3039485 : Nat := 118140960795 + 3039485 * 2 ^ 59
def prefixEnd_3039485 : Nat := 4983230072969 + 3 ^ 40 * 3039485 * 2
def baseEnd_3039485 : Nat := 1560716747131145734659169

theorem tailTrace_3039485 : CollatzResearch.WordTrace tailWord_3039485 prefixEnd_3039485 1560716747131145734659169 := by
  unfold tailWord_3039485
  simp only [CollatzResearch.WordTrace]
  refine ⟨110859125393472422555231909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73906083595648281703487939 110859125393472422555231909)
  ·
    refine ⟨20786086011276079229105983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110859125393472422555231909 20786086011276079229105983)
    ·
      refine ⟨31179129016914118843658975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20786086011276079229105983 31179129016914118843658975)
      ·
        refine ⟨46768693525371178265488463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31179129016914118843658975 46768693525371178265488463)
        ·
          refine ⟨70153040288056767398232695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46768693525371178265488463 70153040288056767398232695)
          ·
            refine ⟨105229560432085151097349043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70153040288056767398232695 105229560432085151097349043)
            ·
              refine ⟨157844340648127726646023565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105229560432085151097349043 157844340648127726646023565)
              ·
                refine ⟨59191627743047897492258837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157844340648127726646023565 59191627743047897492258837)
                ·
                  refine ⟨2774607550455370194949633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59191627743047897492258837 2774607550455370194949633)
                  ·
                    refine ⟨2080955662841527646212225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774607550455370194949633 2080955662841527646212225)
                    ·
                      refine ⟨1560716747131145734659169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080955662841527646212225 1560716747131145734659169)
                      ·
                        rfl

theorem cell23_3039485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_3039485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039485 prefixEnd_3039485 := by exact prefixLift 3039485
  have htrace : WordTrace (prefixWord ++ tailWord_3039485) baseStart_3039485 baseEnd_3039485 := by
    simpa [prefixWord, tailWord_3039485, baseEnd_3039485] using wordTrace_append hprefix tailTrace_3039485
  have hstable : (prefixWord ++ tailWord_3039485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039485).length < 2 ^ (prefixWord ++ tailWord_3039485).sum := by decide
  have hdescent : baseEnd_3039485 < baseStart_3039485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039553 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3039553 : Nat := 118140960795 + 3039553 * 2 ^ 59
def prefixEnd_3039553 : Nat := 4983230072969 + 3 ^ 40 * 3039553 * 2
def baseEnd_3039553 : Nat := 1560751663815651468608857

theorem tailTrace_3039553 : CollatzResearch.WordTrace tailWord_3039553 prefixEnd_3039553 1560751663815651468608857 := by
  unfold tailWord_3039553
  simp only [CollatzResearch.WordTrace]
  refine ⟨110861605557226070168707313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73907737038150713445804875 110861605557226070168707313)
  ·
    refine ⟨83146204167919552626530485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110861605557226070168707313 83146204167919552626530485)
    ·
      refine ⟨7794956640742458058737233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83146204167919552626530485 7794956640742458058737233)
      ·
        refine ⟨5846217480556843544052925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794956640742458058737233 5846217480556843544052925)
        ·
          refine ⟨2192331555208816329019847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5846217480556843544052925 2192331555208816329019847)
          ·
            refine ⟨3288497332813224493529771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192331555208816329019847 3288497332813224493529771)
            ·
              refine ⟨4932745999219836740294657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288497332813224493529771 4932745999219836740294657)
              ·
                refine ⟨3699559499414877555220993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932745999219836740294657 3699559499414877555220993)
                ·
                  refine ⟨2774669624561158166415745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3699559499414877555220993 2774669624561158166415745)
                  ·
                    refine ⟨2081002218420868624811809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774669624561158166415745 2081002218420868624811809)
                    ·
                      refine ⟨1560751663815651468608857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081002218420868624811809 1560751663815651468608857)
                      ·
                        rfl

theorem cell23_3039553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3039553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039553 prefixEnd_3039553 := by exact prefixLift 3039553
  have htrace : WordTrace (prefixWord ++ tailWord_3039553) baseStart_3039553 baseEnd_3039553 := by
    simpa [prefixWord, tailWord_3039553, baseEnd_3039553] using wordTrace_append hprefix tailTrace_3039553
  have hstable : (prefixWord ++ tailWord_3039553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039553).length < 2 ^ (prefixWord ++ tailWord_3039553).sum := by decide
  have hdescent : baseEnd_3039553 < baseStart_3039553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039575 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_3039575 : Nat := 118140960795 + 3039575 * 2 ^ 59
def prefixEnd_3039575 : Nat := 4983230072969 + 3 ^ 40 * 3039575 * 2
def baseEnd_3039575 : Nat := 1560762960390050382533755

theorem tailTrace_3039575 : CollatzResearch.WordTrace tailWord_3039575 prefixEnd_3039575 1560762960390050382533755 := by
  unfold tailWord_3039575
  simp only [CollatzResearch.WordTrace]
  refine ⟨110862407963146367926008179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73908271975430911950672119 110862407963146367926008179)
  ·
    refine ⟨166293611944719551889012269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110862407963146367926008179 166293611944719551889012269)
    ·
      refine ⟨62360104479269831958379601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166293611944719551889012269 62360104479269831958379601)
      ·
        refine ⟨46770078359452373968784701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62360104479269831958379601 46770078359452373968784701)
        ·
          refine ⟨17538779384794640238294263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46770078359452373968784701 17538779384794640238294263)
          ·
            refine ⟨26308169077191960357441395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17538779384794640238294263 26308169077191960357441395)
            ·
              refine ⟨39462253615787940536162093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26308169077191960357441395 39462253615787940536162093)
              ·
                refine ⟨14798345105920477701060785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39462253615787940536162093 14798345105920477701060785)
                ·
                  refine ⟨11098758829440358275795589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14798345105920477701060785 11098758829440358275795589)
                  ·
                    refine ⟨2081017280520067176711673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11098758829440358275795589 2081017280520067176711673)
                    ·
                      refine ⟨1560762960390050382533755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081017280520067176711673 1560762960390050382533755)
                      ·
                        rfl

theorem cell23_3039575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_3039575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039575 prefixEnd_3039575 := by exact prefixLift 3039575
  have htrace : WordTrace (prefixWord ++ tailWord_3039575) baseStart_3039575 baseEnd_3039575 := by
    simpa [prefixWord, tailWord_3039575, baseEnd_3039575] using wordTrace_append hprefix tailTrace_3039575
  have hstable : (prefixWord ++ tailWord_3039575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039575).length < 2 ^ (prefixWord ++ tailWord_3039575).sum := by decide
  have hdescent : baseEnd_3039575 < baseStart_3039575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039588 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_3039588 : Nat := 118140960795 + 3039588 * 2 ^ 59
def prefixEnd_3039588 : Nat := 4983230072969 + 3 ^ 40 * 3039588 * 2
def baseEnd_3039588 : Nat := 1560769635638558831671195

theorem tailTrace_3039588 : CollatzResearch.WordTrace tailWord_3039588 prefixEnd_3039588 1560769635638558831671195 := by
  unfold tailWord_3039588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55431441056049635573115709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73908588074732847430820945 55431441056049635573115709)
  ·
    refine ⟨20786790396018613339918391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55431441056049635573115709 20786790396018613339918391)
    ·
      refine ⟨31180185594027920009877587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20786790396018613339918391 31180185594027920009877587)
      ·
        refine ⟨46770278391041880014816381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31180185594027920009877587 46770278391041880014816381)
        ·
          refine ⟨17538854396640705005556143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46770278391041880014816381 17538854396640705005556143)
          ·
            refine ⟨26308281594961057508334215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17538854396640705005556143 26308281594961057508334215)
            ·
              refine ⟨39462422392441586262501323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26308281594961057508334215 39462422392441586262501323)
              ·
                refine ⟨59193633588662379393751985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39462422392441586262501323 59193633588662379393751985)
                ·
                  refine ⟨44395225191496784545313989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59193633588662379393751985 44395225191496784545313989)
                  ·
                    refine ⟨8324104723405647102246373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44395225191496784545313989 8324104723405647102246373)
                    ·
                      refine ⟨1560769635638558831671195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8324104723405647102246373 1560769635638558831671195)
                      ·
                        rfl

theorem cell23_3039588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_3039588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039588 prefixEnd_3039588 := by exact prefixLift 3039588
  have htrace : WordTrace (prefixWord ++ tailWord_3039588) baseStart_3039588 baseEnd_3039588 := by
    simpa [prefixWord, tailWord_3039588, baseEnd_3039588] using wordTrace_append hprefix tailTrace_3039588
  have hstable : (prefixWord ++ tailWord_3039588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039588).length < 2 ^ (prefixWord ++ tailWord_3039588).sum := by decide
  have hdescent : baseEnd_3039588 < baseStart_3039588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039619 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 3, 4]
def baseStart_3039619 : Nat := 118140960795 + 3039619 * 2 ^ 59
def prefixEnd_3039619 : Nat := 4983230072969 + 3 ^ 40 * 3039619 * 2
def baseEnd_3039619 : Nat := 520261851179616070127851

theorem tailTrace_3039619 : CollatzResearch.WordTrace tailWord_3039619 prefixEnd_3039619 520261851179616070127851 := by
  unfold tailWord_3039619
  simp only [CollatzResearch.WordTrace]
  refine ⟨110864012774986963440609911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73909341849991308960406607 110864012774986963440609911)
  ·
    refine ⟨166296019162480445160914867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110864012774986963440609911 166296019162480445160914867)
    ·
      refine ⟨249444028743720667741372301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166296019162480445160914867 249444028743720667741372301)
      ·
        refine ⟨93541510778895250403014613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249444028743720667741372301 93541510778895250403014613)
        ·
          refine ⟨2192379158880357431320655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93541510778895250403014613 2192379158880357431320655)
          ·
            refine ⟨3288568738320536146980983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192379158880357431320655 3288568738320536146980983)
            ·
              refine ⟨4932853107480804220471475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288568738320536146980983 4932853107480804220471475)
              ·
                refine ⟨7399279661221206330707213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932853107480804220471475 7399279661221206330707213)
                ·
                  refine ⟨2774729872957952374015205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7399279661221206330707213 2774729872957952374015205)
                  ·
                    refine ⟨520261851179616070127851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774729872957952374015205 520261851179616070127851)
                    ·
                      rfl

theorem cell23_3039619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 4].length) (baseStart_3039619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039619 prefixEnd_3039619 := by exact prefixLift 3039619
  have htrace : WordTrace (prefixWord ++ tailWord_3039619) baseStart_3039619 baseEnd_3039619 := by
    simpa [prefixWord, tailWord_3039619, baseEnd_3039619] using wordTrace_append hprefix tailTrace_3039619
  have hstable : (prefixWord ++ tailWord_3039619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039619).length < 2 ^ (prefixWord ++ tailWord_3039619).sum := by decide
  have hdescent : baseEnd_3039619 < baseStart_3039619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039652 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_3039652 : Nat := 118140960795 + 3039652 * 2 ^ 59
def prefixEnd_3039652 : Nat := 4983230072969 + 3 ^ 40 * 3039652 * 2
def baseEnd_3039652 : Nat := 1560802498400446581270901

theorem tailTrace_3039652 : CollatzResearch.WordTrace tailWord_3039652 prefixEnd_3039652 1560802498400446581270901 := by
  unfold tailWord_3039652
  simp only [CollatzResearch.WordTrace]
  refine ⟨55432608191933705038280605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73910144255911606717707473 55432608191933705038280605)
  ·
    refine ⟨20787228071975139389355227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55432608191933705038280605 20787228071975139389355227)
    ·
      refine ⟨31180842107962709084032841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20787228071975139389355227 31180842107962709084032841)
      ·
        refine ⟨23385631580972031813024631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31180842107962709084032841 23385631580972031813024631)
        ·
          refine ⟨35078447371458047719536947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23385631580972031813024631 35078447371458047719536947)
          ·
            refine ⟨52617671057187071579305421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35078447371458047719536947 52617671057187071579305421)
            ·
              refine ⟨19731626646445151842239533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52617671057187071579305421 19731626646445151842239533)
              ·
                refine ⟨7399359992416931940839825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19731626646445151842239533 7399359992416931940839825)
                ·
                  refine ⟨5549519994312698955629869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7399359992416931940839825 5549519994312698955629869)
                  ·
                    refine ⟨2081069997867262108361201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5549519994312698955629869 2081069997867262108361201)
                    ·
                      refine ⟨1560802498400446581270901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081069997867262108361201 1560802498400446581270901)
                      ·
                        rfl

theorem cell23_3039652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_3039652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039652 prefixEnd_3039652 := by exact prefixLift 3039652
  have htrace : WordTrace (prefixWord ++ tailWord_3039652) baseStart_3039652 baseEnd_3039652 := by
    simpa [prefixWord, tailWord_3039652, baseEnd_3039652] using wordTrace_append hprefix tailTrace_3039652
  have hstable : (prefixWord ++ tailWord_3039652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039652).length < 2 ^ (prefixWord ++ tailWord_3039652).sum := by decide
  have hdescent : baseEnd_3039652 < baseStart_3039652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039676 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3039676 : Nat := 118140960795 + 3039676 * 2 ^ 59
def prefixEnd_3039676 : Nat := 4983230072969 + 3 ^ 40 * 3039676 * 2
def baseEnd_3039676 : Nat := 1560814821936154487370791

theorem tailTrace_3039676 : CollatzResearch.WordTrace tailWord_3039676 prefixEnd_3039676 1560814821936154487370791 := by
  unfold tailWord_3039676
  simp only [CollatzResearch.WordTrace]
  refine ⟨55433045867890231087717441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73910727823853641450289921 55433045867890231087717441)
  ·
    refine ⟨41574784400917673315788081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55433045867890231087717441 41574784400917673315788081)
    ·
      refine ⟨31181088300688254986841061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41574784400917673315788081 31181088300688254986841061)
      ·
        refine ⟨5846454056379047810032699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31181088300688254986841061 5846454056379047810032699)
        ·
          refine ⟨8769681084568571715049049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846454056379047810032699 8769681084568571715049049)
          ·
            refine ⟨6577260813426428786286787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8769681084568571715049049 6577260813426428786286787)
            ·
              refine ⟨9865891220139643179430181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577260813426428786286787 9865891220139643179430181)
              ·
                refine ⟨1849854603776183096143159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9865891220139643179430181 1849854603776183096143159)
                ·
                  refine ⟨2774781905664274644214739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849854603776183096143159 2774781905664274644214739)
                  ·
                    refine ⟨4162172858496411966322109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2774781905664274644214739 4162172858496411966322109)
                    ·
                      refine ⟨1560814821936154487370791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4162172858496411966322109 1560814821936154487370791)
                      ·
                        rfl

theorem cell23_3039676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3039676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039676 prefixEnd_3039676 := by exact prefixLift 3039676
  have htrace : WordTrace (prefixWord ++ tailWord_3039676) baseStart_3039676 baseEnd_3039676 := by
    simpa [prefixWord, tailWord_3039676, baseEnd_3039676] using wordTrace_append hprefix tailTrace_3039676
  have hstable : (prefixWord ++ tailWord_3039676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039676).length < 2 ^ (prefixWord ++ tailWord_3039676).sum := by decide
  have hdescent : baseEnd_3039676 < baseStart_3039676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039692 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_3039692 : Nat := 118140960795 + 3039692 * 2 ^ 59
def prefixEnd_3039692 : Nat := 4983230072969 + 3 ^ 40 * 3039692 * 2
def baseEnd_3039692 : Nat := 520274345875542141590239

theorem tailTrace_3039692 : CollatzResearch.WordTrace tailWord_3039692 prefixEnd_3039692 520274345875542141590239 := by
  unfold tailWord_3039692
  simp only [CollatzResearch.WordTrace]
  refine ⟨55433337651861248454008665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73911116869148331272011553 55433337651861248454008665)
  ·
    refine ⟨41575003238895936340506499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55433337651861248454008665 41575003238895936340506499)
    ·
      refine ⟨62362504858343904510759749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41575003238895936340506499 62362504858343904510759749)
      ·
        refine ⟨11692969660939482095767453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62362504858343904510759749 11692969660939482095767453)
        ·
          refine ⟨4384863622852305785912795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11692969660939482095767453 4384863622852305785912795)
          ·
            refine ⟨6577295434278458678869193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384863622852305785912795 6577295434278458678869193)
            ·
              refine ⟨4932971575708844009151895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577295434278458678869193 4932971575708844009151895)
              ·
                refine ⟨7399457363563266013727843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932971575708844009151895 7399457363563266013727843)
                ·
                  refine ⟨11099186045344899020591765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399457363563266013727843 11099186045344899020591765)
                  ·
                    refine ⟨520274345875542141590239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11099186045344899020591765 520274345875542141590239)
                    ·
                      rfl

theorem cell23_3039692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_3039692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039692 prefixEnd_3039692 := by exact prefixLift 3039692
  have htrace : WordTrace (prefixWord ++ tailWord_3039692) baseStart_3039692 baseEnd_3039692 := by
    simpa [prefixWord, tailWord_3039692, baseEnd_3039692] using wordTrace_append hprefix tailTrace_3039692
  have hstable : (prefixWord ++ tailWord_3039692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039692).length < 2 ^ (prefixWord ++ tailWord_3039692).sum := by decide
  have hdescent : baseEnd_3039692 < baseStart_3039692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039705 : List Nat := [1, 2, 1, 2, 4, 1, 5, 7]
def baseStart_3039705 : Nat := 118140960795 + 3039705 * 2 ^ 59
def prefixEnd_3039705 : Nat := 4983230072969 + 3 ^ 40 * 3039705 * 2
def baseEnd_3039705 : Nat := 57808507884264254589191

theorem tailTrace_3039705 : CollatzResearch.WordTrace tailWord_3039705 prefixEnd_3039705 57808507884264254589191 := by
  unfold tailWord_3039705
  simp only [CollatzResearch.WordTrace]
  refine ⟨110867149452675400128240569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73911432968450266752160379 110867149452675400128240569)
  ·
    refine ⟨83150362089506550096180427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110867149452675400128240569 83150362089506550096180427)
    ·
      refine ⟨124725543134259825144270641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83150362089506550096180427 124725543134259825144270641)
      ·
        refine ⟨93544157350694868858202981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124725543134259825144270641 93544157350694868858202981)
        ·
          refine ⟨17539529503255287910913059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93544157350694868858202981 17539529503255287910913059)
          ·
            refine ⟨26309294254882931866369589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17539529503255287910913059 26309294254882931866369589)
            ·
              refine ⟨2466496336395274862472149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26309294254882931866369589 2466496336395274862472149)
              ·
                refine ⟨57808507884264254589191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2466496336395274862472149 57808507884264254589191)
                ·
                  rfl

theorem cell23_3039705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 7].length) (baseStart_3039705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039705 prefixEnd_3039705 := by exact prefixLift 3039705
  have htrace : WordTrace (prefixWord ++ tailWord_3039705) baseStart_3039705 baseEnd_3039705 := by
    simpa [prefixWord, tailWord_3039705, baseEnd_3039705] using wordTrace_append hprefix tailTrace_3039705
  have hstable : (prefixWord ++ tailWord_3039705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039705).length < 2 ^ (prefixWord ++ tailWord_3039705).sum := by decide
  have hdescent : baseEnd_3039705 < baseStart_3039705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039733 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3039733 : Nat := 118140960795 + 3039733 * 2 ^ 59
def prefixEnd_3039733 : Nat := 4983230072969 + 3 ^ 40 * 3039733 * 2
def baseEnd_3039733 : Nat := 1560844090333460764358029

theorem tailTrace_3039733 : CollatzResearch.WordTrace tailWord_3039733 prefixEnd_3039733 1560844090333460764358029 := by
  unfold tailWord_3039733
  simp only [CollatzResearch.WordTrace]
  refine ⟨110868170696573960910259853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73912113797715973940173235 110868170696573960910259853)
  ·
    refine ⟨41575564011215235341347445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110868170696573960910259853 41575564011215235341347445)
    ·
      refine ⟨3897709126051428313251323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41575564011215235341347445 3897709126051428313251323)
      ·
        refine ⟨5846563689077142469876985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897709126051428313251323 5846563689077142469876985)
        ·
          refine ⟨4384922766807856852407739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5846563689077142469876985 4384922766807856852407739)
          ·
            refine ⟨6577384150211785278611609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384922766807856852407739 6577384150211785278611609)
            ·
              refine ⟨4933038112658838958958707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577384150211785278611609 4933038112658838958958707)
              ·
                refine ⟨7399557168988258438438061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933038112658838958958707 7399557168988258438438061)
                ·
                  refine ⟨2774833938370596914414273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7399557168988258438438061 2774833938370596914414273)
                  ·
                    refine ⟨2081125453777947685810705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774833938370596914414273 2081125453777947685810705)
                    ·
                      refine ⟨1560844090333460764358029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081125453777947685810705 1560844090333460764358029)
                      ·
                        rfl

theorem cell23_3039733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3039733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039733 prefixEnd_3039733 := by exact prefixLift 3039733
  have htrace : WordTrace (prefixWord ++ tailWord_3039733) baseStart_3039733 baseEnd_3039733 := by
    simpa [prefixWord, tailWord_3039733, baseEnd_3039733] using wordTrace_append hprefix tailTrace_3039733
  have hstable : (prefixWord ++ tailWord_3039733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039733).length < 2 ^ (prefixWord ++ tailWord_3039733).sum := by decide
  have hdescent : baseEnd_3039733 < baseStart_3039733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039746 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3039746 : Nat := 118140960795 + 3039746 * 2 ^ 59
def prefixEnd_3039746 : Nat := 4983230072969 + 3 ^ 40 * 3039746 * 2
def baseEnd_3039746 : Nat := 1560850765581969213495469

theorem tailTrace_3039746 : CollatzResearch.WordTrace tailWord_3039746 prefixEnd_3039746 1560850765581969213495469 := by
  unfold tailWord_3039746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27717161211381716032620773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73912429897017909420322061 27717161211381716032620773)
  ·
    refine ⟨5196967727134071756116395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27717161211381716032620773 5196967727134071756116395)
    ·
      refine ⟨7795451590701107634174593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196967727134071756116395 7795451590701107634174593)
      ·
        refine ⟨5846588693025830725630945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7795451590701107634174593 5846588693025830725630945)
        ·
          refine ⟨4384941519769373044223209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5846588693025830725630945 4384941519769373044223209)
          ·
            refine ⟨3288706139827029783167407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4384941519769373044223209 3288706139827029783167407)
            ·
              refine ⟨4933059209740544674751111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288706139827029783167407 4933059209740544674751111)
              ·
                refine ⟨7399588814610817012126667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933059209740544674751111 7399588814610817012126667)
                ·
                  refine ⟨11099383221916225518190001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399588814610817012126667 11099383221916225518190001)
                  ·
                    refine ⟨8324537416437169138642501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11099383221916225518190001 8324537416437169138642501)
                    ·
                      refine ⟨1560850765581969213495469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8324537416437169138642501 1560850765581969213495469)
                      ·
                        rfl

theorem cell23_3039746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3039746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039746 prefixEnd_3039746 := by exact prefixLift 3039746
  have htrace : WordTrace (prefixWord ++ tailWord_3039746) baseStart_3039746 baseEnd_3039746 := by
    simpa [prefixWord, tailWord_3039746, baseEnd_3039746] using wordTrace_append hprefix tailTrace_3039746
  have hstable : (prefixWord ++ tailWord_3039746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039746).length < 2 ^ (prefixWord ++ tailWord_3039746).sum := by decide
  have hdescent : baseEnd_3039746 < baseStart_3039746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039750 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3039750 : Nat := 118140960795 + 3039750 * 2 ^ 59
def prefixEnd_3039750 : Nat := 4983230072969 + 3 ^ 40 * 3039750 * 2
def baseEnd_3039750 : Nat := 1560852819504587197845451

theorem tailTrace_3039750 : CollatzResearch.WordTrace tailWord_3039750 prefixEnd_3039750 1560852819504587197845451 := by
  unfold tailWord_3039750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464649710547261650425897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73912527158341581875752469 3464649710547261650425897)
  ·
    refine ⟨2598487282910446237819423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3464649710547261650425897 2598487282910446237819423)
    ·
      refine ⟨3897730924365669356729135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598487282910446237819423 3897730924365669356729135)
      ·
        refine ⟨5846596386548504035093703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897730924365669356729135 5846596386548504035093703)
        ·
          refine ⟨8769894579822756052640555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846596386548504035093703 8769894579822756052640555)
          ·
            refine ⟨13154841869734134078960833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769894579822756052640555 13154841869734134078960833)
            ·
              refine ⟨9866131402300600559220625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13154841869734134078960833 9866131402300600559220625)
              ·
                refine ⟨7399598551725450419415469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9866131402300600559220625 7399598551725450419415469)
                ·
                  refine ⟨2774849456897043907280801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7399598551725450419415469 2774849456897043907280801)
                  ·
                    refine ⟨2081137092672782930460601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774849456897043907280801 2081137092672782930460601)
                    ·
                      refine ⟨1560852819504587197845451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081137092672782930460601 1560852819504587197845451)
                      ·
                        rfl

theorem cell23_3039750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3039750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039750 prefixEnd_3039750 := by exact prefixLift 3039750
  have htrace : WordTrace (prefixWord ++ tailWord_3039750) baseStart_3039750 baseEnd_3039750 := by
    simpa [prefixWord, tailWord_3039750, baseEnd_3039750] using wordTrace_append hprefix tailTrace_3039750
  have hstable : (prefixWord ++ tailWord_3039750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039750).length < 2 ^ (prefixWord ++ tailWord_3039750).sum := by decide
  have hdescent : baseEnd_3039750 < baseStart_3039750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039767 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3039767 : Nat := 118140960795 + 3039767 * 2 ^ 59
def prefixEnd_3039767 : Nat := 4983230072969 + 3 ^ 40 * 3039767 * 2
def baseEnd_3039767 : Nat := 1560861548675713631332873

theorem tailTrace_3039767 : CollatzResearch.WordTrace tailWord_3039767 prefixEnd_3039767 1560861548675713631332873 := by
  unfold tailWord_3039767
  simp only [CollatzResearch.WordTrace]
  refine ⟨110869410778450784716997555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73912940518967189811331703 110869410778450784716997555)
  ·
    refine ⟨166304116167676177075496333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110869410778450784716997555 166304116167676177075496333)
    ·
      refine ⟨62364043562878566403311125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166304116167676177075496333 62364043562878566403311125)
      ·
        refine ⟨2923314542009932800155209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62364043562878566403311125 2923314542009932800155209)
        ·
          refine ⟨2192485906507449600116407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923314542009932800155209 2192485906507449600116407)
          ·
            refine ⟨3288728859761174400174611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192485906507449600116407 3288728859761174400174611)
            ·
              refine ⟨4933093289641761600261917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288728859761174400174611 4933093289641761600261917)
              ·
                refine ⟨1849909983615660600098219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4933093289641761600261917 1849909983615660600098219)
                ·
                  refine ⟨2774864975423490900147329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849909983615660600098219 2774864975423490900147329)
                  ·
                    refine ⟨2081148731567618175110497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774864975423490900147329 2081148731567618175110497)
                    ·
                      refine ⟨1560861548675713631332873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081148731567618175110497 1560861548675713631332873)
                      ·
                        rfl

theorem cell23_3039767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3039767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039767 prefixEnd_3039767 := by exact prefixLift 3039767
  have htrace : WordTrace (prefixWord ++ tailWord_3039767) baseStart_3039767 baseEnd_3039767 := by
    simpa [prefixWord, tailWord_3039767, baseEnd_3039767] using wordTrace_append hprefix tailTrace_3039767
  have hstable : (prefixWord ++ tailWord_3039767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039767).length < 2 ^ (prefixWord ++ tailWord_3039767).sum := by decide
  have hdescent : baseEnd_3039767 < baseStart_3039767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039775 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3039775 : Nat := 118140960795 + 3039775 * 2 ^ 59
def prefixEnd_3039775 : Nat := 4983230072969 + 3 ^ 40 * 3039775 * 2
def baseEnd_3039775 : Nat := 1560865656520949600032835

theorem tailTrace_3039775 : CollatzResearch.WordTrace tailWord_3039775 prefixEnd_3039775 1560865656520949600032835 := by
  unfold tailWord_3039775
  simp only [CollatzResearch.WordTrace]
  refine ⟨110869702562421802083288779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73913135041614534722192519 110869702562421802083288779)
  ·
    refine ⟨166304553843632703124933169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110869702562421802083288779 166304553843632703124933169)
    ·
      refine ⟨124728415382724527343699877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166304553843632703124933169 124728415382724527343699877)
      ·
        refine ⟨23386577884260848876943727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124728415382724527343699877 23386577884260848876943727)
        ·
          refine ⟨35079866826391273315415591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23386577884260848876943727 35079866826391273315415591)
          ·
            refine ⟨52619800239586909973123387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35079866826391273315415591 52619800239586909973123387)
            ·
              refine ⟨78929700359380364959685081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52619800239586909973123387 78929700359380364959685081)
              ·
                refine ⟨59197275269535273719763811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78929700359380364959685081 59197275269535273719763811)
                ·
                  refine ⟨88795912904302910579645717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59197275269535273719763811 88795912904302910579645717)
                  ·
                    refine ⟨4162308417389198933420893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88795912904302910579645717 4162308417389198933420893)
                    ·
                      refine ⟨1560865656520949600032835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4162308417389198933420893 1560865656520949600032835)
                      ·
                        rfl

theorem cell23_3039775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3039775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039775 prefixEnd_3039775 := by exact prefixLift 3039775
  have htrace : WordTrace (prefixWord ++ tailWord_3039775) baseStart_3039775 baseEnd_3039775 := by
    simpa [prefixWord, tailWord_3039775, baseEnd_3039775] using wordTrace_append hprefix tailTrace_3039775
  have hstable : (prefixWord ++ tailWord_3039775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039775).length < 2 ^ (prefixWord ++ tailWord_3039775).sum := by decide
  have hdescent : baseEnd_3039775 < baseStart_3039775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039872 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_3039872 : Nat := 118140960795 + 3039872 * 2 ^ 59
def prefixEnd_3039872 : Nat := 4983230072969 + 3 ^ 40 * 3039872 * 2
def baseEnd_3039872 : Nat := 520305154714811906839963

theorem tailTrace_3039872 : CollatzResearch.WordTrace tailWord_3039872 prefixEnd_3039872 520305154714811906839963 := by
  unfold tailWord_3039872
  simp only [CollatzResearch.WordTrace]
  refine ⟨55436620221535193824784935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73915493628713591766379913 55436620221535193824784935)
  ·
    refine ⟨83154930332302790737177403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55436620221535193824784935 83154930332302790737177403)
    ·
      refine ⟨124732395498454186105766105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83154930332302790737177403 124732395498454186105766105)
      ·
        refine ⟨93549296623840639579324579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124732395498454186105766105 93549296623840639579324579)
        ·
          refine ⟨140323944935760959368986869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93549296623840639579324579 140323944935760959368986869)
          ·
            refine ⟨13155369837727589940842519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140323944935760959368986869 13155369837727589940842519)
            ·
              refine ⟨19733054756591384911263779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13155369837727589940842519 19733054756591384911263779)
              ·
                refine ⟨29599582134887077366895669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19733054756591384911263779 29599582134887077366895669)
                ·
                  refine ⟨2774960825145663503146469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29599582134887077366895669 2774960825145663503146469)
                  ·
                    refine ⟨520305154714811906839963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774960825145663503146469 520305154714811906839963)
                    ·
                      rfl

theorem cell23_3039872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_3039872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039872 prefixEnd_3039872 := by exact prefixLift 3039872
  have htrace : WordTrace (prefixWord ++ tailWord_3039872) baseStart_3039872 baseEnd_3039872 := by
    simpa [prefixWord, tailWord_3039872, baseEnd_3039872] using wordTrace_append hprefix tailTrace_3039872
  have hstable : (prefixWord ++ tailWord_3039872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039872).length < 2 ^ (prefixWord ++ tailWord_3039872).sum := by decide
  have hdescent : baseEnd_3039872 < baseStart_3039872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039919 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 6]
def baseStart_3039919 : Nat := 118140960795 + 3039919 * 2 ^ 59
def prefixEnd_3039919 : Nat := 4983230072969 + 3 ^ 40 * 3039919 * 2
def baseEnd_3039919 : Nat := 173437733081688559625797

theorem tailTrace_3039919 : CollatzResearch.WordTrace tailWord_3039919 prefixEnd_3039919 173437733081688559625797 := by
  unfold tailWord_3039919
  simp only [CollatzResearch.WordTrace]
  refine ⟨110874954673900114676530811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73916636449266743117687207 110874954673900114676530811)
  ·
    refine ⟨166312432010850172014796217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110874954673900114676530811 166312432010850172014796217)
    ·
      refine ⟨124734324008137629011097163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166312432010850172014796217 124734324008137629011097163)
      ·
        refine ⟨187101486012206443516645745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124734324008137629011097163 187101486012206443516645745)
        ·
          refine ⟨140326114509154832637484309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187101486012206443516645745 140326114509154832637484309)
          ·
            refine ⟨6577786617616632779882077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140326114509154832637484309 6577786617616632779882077)
            ·
              refine ⟨2466669981606237292455779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6577786617616632779882077 2466669981606237292455779)
              ·
                refine ⟨3700004972409355938683669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466669981606237292455779 3700004972409355938683669)
                ·
                  refine ⟨173437733081688559625797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3700004972409355938683669 173437733081688559625797)
                  ·
                    rfl

theorem cell23_3039919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 6].length) (baseStart_3039919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039919 prefixEnd_3039919 := by exact prefixLift 3039919
  have htrace : WordTrace (prefixWord ++ tailWord_3039919) baseStart_3039919 baseEnd_3039919 := by
    simpa [prefixWord, tailWord_3039919, baseEnd_3039919] using wordTrace_append hprefix tailTrace_3039919
  have hstable : (prefixWord ++ tailWord_3039919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039919).length < 2 ^ (prefixWord ++ tailWord_3039919).sum := by decide
  have hdescent : baseEnd_3039919 < baseStart_3039919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039986 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3039986 : Nat := 118140960795 + 3039986 * 2 ^ 59
def prefixEnd_3039986 : Nat := 4983230072969 + 3 ^ 40 * 3039986 * 2
def baseEnd_3039986 : Nat := 1560974000939048274494365

theorem tailTrace_3039986 : CollatzResearch.WordTrace tailWord_3039986 prefixEnd_3039986 1560974000939048274494365 := by
  unfold tailWord_3039986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27719349591164346279804953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73918265576438256746146541 27719349591164346279804953)
  ·
    refine ⟨20789512193373259709853715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27719349591164346279804953 20789512193373259709853715)
    ·
      refine ⟨31184268290059889564780573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789512193373259709853715 31184268290059889564780573)
      ·
        refine ⟨11694100608772458586792715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31184268290059889564780573 11694100608772458586792715)
        ·
          refine ⟨17541150913158687880189073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11694100608772458586792715 17541150913158687880189073)
          ·
            refine ⟨13155863184869015910141805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17541150913158687880189073 13155863184869015910141805)
            ·
              refine ⟨4933448694325880966303177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13155863184869015910141805 4933448694325880966303177)
              ·
                refine ⟨3700086520744410724727383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4933448694325880966303177 3700086520744410724727383)
                ·
                  refine ⟨5550129781116616087091075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700086520744410724727383 5550129781116616087091075)
                  ·
                    refine ⟨8325194671674924130636613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5550129781116616087091075 8325194671674924130636613)
                    ·
                      refine ⟨1560974000939048274494365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8325194671674924130636613 1560974000939048274494365)
                      ·
                        rfl

theorem cell23_3039986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3039986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039986 prefixEnd_3039986 := by exact prefixLift 3039986
  have htrace : WordTrace (prefixWord ++ tailWord_3039986) baseStart_3039986 baseEnd_3039986 := by
    simpa [prefixWord, tailWord_3039986, baseEnd_3039986] using wordTrace_append hprefix tailTrace_3039986
  have hstable : (prefixWord ++ tailWord_3039986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039986).length < 2 ^ (prefixWord ++ tailWord_3039986).sum := by decide
  have hdescent : baseEnd_3039986 < baseStart_3039986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040003 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 1, 2, 2]
def baseStart_3040003 : Nat := 118140960795 + 3040003 * 2 ^ 59
def prefixEnd_3040003 : Nat := 4983230072969 + 3 ^ 40 * 3040003 * 2
def baseEnd_3040003 : Nat := 1560982730110174707981787

theorem tailTrace_3040003 : CollatzResearch.WordTrace tailWord_3040003 prefixEnd_3040003 1560982730110174707981787 := by
  unfold tailWord_3040003
  simp only [CollatzResearch.WordTrace]
  refine ⟨110878018405595797022588663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73918678937063864681725775 110878018405595797022588663)
  ·
    refine ⟨166317027608393695533882995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110878018405595797022588663 166317027608393695533882995)
    ·
      refine ⟨249475541412590543300824493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166317027608393695533882995 249475541412590543300824493)
      ·
        refine ⟨93553328029721453737809185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249475541412590543300824493 93553328029721453737809185)
        ·
          refine ⟨70164996022291090303356889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93553328029721453737809185 70164996022291090303356889)
          ·
            refine ⟨52623747016718317727517667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70164996022291090303356889 52623747016718317727517667)
            ·
              refine ⟨78935620525077476591276501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52623747016718317727517667 78935620525077476591276501)
              ·
                refine ⟨1850053606056503357608043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78935620525077476591276501 1850053606056503357608043)
                ·
                  refine ⟨2775080409084755036412065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850053606056503357608043 2775080409084755036412065)
                  ·
                    refine ⟨2081310306813566277309049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775080409084755036412065 2081310306813566277309049)
                    ·
                      refine ⟨1560982730110174707981787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081310306813566277309049 1560982730110174707981787)
                      ·
                        rfl

theorem cell23_3040003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_3040003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040003 prefixEnd_3040003 := by exact prefixLift 3040003
  have htrace : WordTrace (prefixWord ++ tailWord_3040003) baseStart_3040003 baseEnd_3040003 := by
    simpa [prefixWord, tailWord_3040003, baseEnd_3040003] using wordTrace_append hprefix tailTrace_3040003
  have hstable : (prefixWord ++ tailWord_3040003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040003).length < 2 ^ (prefixWord ++ tailWord_3040003).sum := by decide
  have hdescent : baseEnd_3040003 < baseStart_3040003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040054 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3040054 : Nat := 118140960795 + 3040054 * 2 ^ 59
def prefixEnd_3040054 : Nat := 4983230072969 + 3 ^ 40 * 3040054 * 2
def baseEnd_3040054 : Nat := 1561008917623554008444053

theorem tailTrace_3040054 : CollatzResearch.WordTrace tailWord_3040054 prefixEnd_3040054 1561008917623554008444053 := by
  unfold tailWord_3040054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929992408025689545793451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73919919018940688488463477 6929992408025689545793451)
  ·
    refine ⟨10394988612038534318690177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6929992408025689545793451 10394988612038534318690177)
    ·
      refine ⟨7796241459028900739017633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10394988612038534318690177 7796241459028900739017633)
      ·
        refine ⟨5847181094271675554263225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7796241459028900739017633 5847181094271675554263225)
        ·
          refine ⟨4385385820703756665697419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5847181094271675554263225 4385385820703756665697419)
          ·
            refine ⟨6578078731055634998546129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385385820703756665697419 6578078731055634998546129)
            ·
              refine ⟨4933559048291726248909597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6578078731055634998546129 4933559048291726248909597)
              ·
                refine ⟨1850084643109397343341099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4933559048291726248909597 1850084643109397343341099)
                ·
                  refine ⟨2775126964664096015011649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850084643109397343341099 2775126964664096015011649)
                  ·
                    refine ⟨2081345223498072011258737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775126964664096015011649 2081345223498072011258737)
                    ·
                      refine ⟨1561008917623554008444053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081345223498072011258737 1561008917623554008444053)
                      ·
                        rfl

theorem cell23_3040054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3040054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040054 prefixEnd_3040054 := by exact prefixLift 3040054
  have htrace : WordTrace (prefixWord ++ tailWord_3040054) baseStart_3040054 baseEnd_3040054 := by
    simpa [prefixWord, tailWord_3040054, baseEnd_3040054] using wordTrace_append hprefix tailTrace_3040054
  have hstable : (prefixWord ++ tailWord_3040054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040054).length < 2 ^ (prefixWord ++ tailWord_3040054).sum := by decide
  have hdescent : baseEnd_3040054 < baseStart_3040054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040063 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 1, 3, 2]
def baseStart_3040063 : Nat := 118140960795 + 3040063 * 2 ^ 59
def prefixEnd_3040063 : Nat := 4983230072969 + 3 ^ 40 * 3040063 * 2
def baseEnd_3040063 : Nat := 1561013538949444473231511

theorem tailTrace_3040063 : CollatzResearch.WordTrace tailWord_3040063 prefixEnd_3040063 1561013538949444473231511 := by
  unfold tailWord_3040063
  simp only [CollatzResearch.WordTrace]
  refine ⟨110880206785378427269772843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73920137856918951513181895 110880206785378427269772843)
  ·
    refine ⟨166320310178067640904659265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110880206785378427269772843 166320310178067640904659265)
    ·
      refine ⟨124740232633550730678494449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166320310178067640904659265 124740232633550730678494449)
      ·
        refine ⟨93555174475163048008870837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124740232633550730678494449 93555174475163048008870837)
        ·
          refine ⟨8770797607046535750831641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93555174475163048008870837 8770797607046535750831641)
          ·
            refine ⟨6578098205284901813123731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8770797607046535750831641 6578098205284901813123731)
            ·
              refine ⟨9867147307927352719685597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578098205284901813123731 9867147307927352719685597)
              ·
                refine ⟨3700180240472757269882099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9867147307927352719685597 3700180240472757269882099)
                ·
                  refine ⟨5550270360709135904823149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700180240472757269882099 5550270360709135904823149)
                  ·
                    refine ⟨2081351385265925964308681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5550270360709135904823149 2081351385265925964308681)
                    ·
                      refine ⟨1561013538949444473231511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081351385265925964308681 1561013538949444473231511)
                      ·
                        rfl

theorem cell23_3040063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_3040063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040063 prefixEnd_3040063 := by exact prefixLift 3040063
  have htrace : WordTrace (prefixWord ++ tailWord_3040063) baseStart_3040063 baseEnd_3040063 := by
    simpa [prefixWord, tailWord_3040063, baseEnd_3040063] using wordTrace_append hprefix tailTrace_3040063
  have hstable : (prefixWord ++ tailWord_3040063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040063).length < 2 ^ (prefixWord ++ tailWord_3040063).sum := by decide
  have hdescent : baseEnd_3040063 < baseStart_3040063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040089 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_3040089 : Nat := 118140960795 + 3040089 * 2 ^ 59
def prefixEnd_3040089 : Nat := 4983230072969 + 3 ^ 40 * 3040089 * 2
def baseEnd_3040089 : Nat := 1561026889446461371506391

theorem tailTrace_3040089 : CollatzResearch.WordTrace tailWord_3040089 prefixEnd_3040089 1561026889446461371506391 := by
  unfold tailWord_3040089
  simp only [CollatzResearch.WordTrace]
  refine ⟨110881155083284233710219321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73920770055522822473479547 110881155083284233710219321)
  ·
    refine ⟨83160866312463175282664491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110881155083284233710219321 83160866312463175282664491)
    ·
      refine ⟨124741299468694762923996737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83160866312463175282664491 124741299468694762923996737)
      ·
        refine ⟨93555974601521072192997553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124741299468694762923996737 93555974601521072192997553)
        ·
          refine ⟨70166980951140804144748165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93555974601521072192997553 70166980951140804144748165)
          ·
            refine ⟨13156308928338900777140281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70166980951140804144748165 13156308928338900777140281)
            ·
              refine ⟨9867231696254175582855211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13156308928338900777140281 9867231696254175582855211)
              ·
                refine ⟨14800847544381263374282817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9867231696254175582855211 14800847544381263374282817)
                ·
                  refine ⟨11100635658285947530712113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14800847544381263374282817 11100635658285947530712113)
                  ·
                    refine ⟨8325476743714460648034085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11100635658285947530712113 8325476743714460648034085)
                    ·
                      refine ⟨1561026889446461371506391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8325476743714460648034085 1561026889446461371506391)
                      ·
                        rfl

theorem cell23_3040089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_3040089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040089 prefixEnd_3040089 := by exact prefixLift 3040089
  have htrace : WordTrace (prefixWord ++ tailWord_3040089) baseStart_3040089 baseEnd_3040089 := by
    simpa [prefixWord, tailWord_3040089, baseEnd_3040089] using wordTrace_append hprefix tailTrace_3040089
  have hstable : (prefixWord ++ tailWord_3040089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040089).length < 2 ^ (prefixWord ++ tailWord_3040089).sum := by decide
  have hdescent : baseEnd_3040089 < baseStart_3040089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040099 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 7]
def baseStart_3040099 : Nat := 118140960795 + 3040099 * 2 ^ 59
def prefixEnd_3040099 : Nat := 4983230072969 + 3 ^ 40 * 3040099 * 2
def baseEnd_3040099 : Nat := 173448002694778481375705

theorem tailTrace_3040099 : CollatzResearch.WordTrace tailWord_3040099 prefixEnd_3040099 173448002694778481375705 := by
  unfold tailWord_3040099
  simp only [CollatzResearch.WordTrace]
  refine ⟨110881519813248005418083351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73921013208832003612055567 110881519813248005418083351)
  ·
    refine ⟨166322279719872008127125027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110881519813248005418083351 166322279719872008127125027)
    ·
      refine ⟨249483419579808012190687541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166322279719872008127125027 249483419579808012190687541)
      ·
        refine ⟨23389070585607001142876957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249483419579808012190687541 23389070585607001142876957)
        ·
          refine ⟨8770901469602625428578859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23389070585607001142876957 8770901469602625428578859)
          ·
            refine ⟨13156352204403938142868289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8770901469602625428578859 13156352204403938142868289)
            ·
              refine ⟨9867264153302953607151217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13156352204403938142868289 9867264153302953607151217)
              ·
                refine ⟨7400448114977215205363413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9867264153302953607151217 7400448114977215205363413)
                ·
                  refine ⟨173448002694778481375705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7400448114977215205363413 173448002694778481375705)
                  ·
                    rfl

theorem cell23_3040099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 7].length) (baseStart_3040099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040099 prefixEnd_3040099 := by exact prefixLift 3040099
  have htrace : WordTrace (prefixWord ++ tailWord_3040099) baseStart_3040099 baseEnd_3040099 := by
    simpa [prefixWord, tailWord_3040099, baseEnd_3040099] using wordTrace_append hprefix tailTrace_3040099
  have hstable : (prefixWord ++ tailWord_3040099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040099).length < 2 ^ (prefixWord ++ tailWord_3040099).sum := by decide
  have hdescent : baseEnd_3040099 < baseStart_3040099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040133 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 5]
def baseStart_3040133 : Nat := 118140960795 + 3040133 * 2 ^ 59
def prefixEnd_3040133 : Nat := 4983230072969 + 3 ^ 40 * 3040133 * 2
def baseEnd_3040133 : Nat := 173449942510584355484021

theorem tailTrace_3040133 : CollatzResearch.WordTrace tailWord_3040133 prefixEnd_3040133 173449942510584355484021 := by
  unfold tailWord_3040133
  simp only [CollatzResearch.WordTrace]
  refine ⟨110882759895124829224821053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73921839930083219483214035 110882759895124829224821053)
  ·
    refine ⟨41581034960671810959307895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110882759895124829224821053 41581034960671810959307895)
    ·
      refine ⟨62371552441007716438961843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41581034960671810959307895 62371552441007716438961843)
      ·
        refine ⟨93557328661511574658442765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62371552441007716438961843 93557328661511574658442765)
        ·
          refine ⟨35083998248066840496916037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93557328661511574658442765 35083998248066840496916037)
          ·
            refine ⟨6578249671512532593171757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35083998248066840496916037 6578249671512532593171757)
            ·
              refine ⟨2466843626817199722439409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6578249671512532593171757 2466843626817199722439409)
              ·
                refine ⟨1850132720112899791829557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2466843626817199722439409 1850132720112899791829557)
                ·
                  refine ⟨173449942510584355484021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850132720112899791829557 173449942510584355484021)
                  ·
                    rfl

theorem cell23_3040133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_3040133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040133 prefixEnd_3040133 := by exact prefixLift 3040133
  have htrace : WordTrace (prefixWord ++ tailWord_3040133) baseStart_3040133 baseEnd_3040133 := by
    simpa [prefixWord, tailWord_3040133, baseEnd_3040133] using wordTrace_append hprefix tailTrace_3040133
  have hstable : (prefixWord ++ tailWord_3040133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040133).length < 2 ^ (prefixWord ++ tailWord_3040133).sum := by decide
  have hdescent : baseEnd_3040133 < baseStart_3040133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040186 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_3040186 : Nat := 118140960795 + 3040186 * 2 ^ 59
def prefixEnd_3040186 : Nat := 4983230072969 + 3 ^ 40 * 3040186 * 2
def baseEnd_3040186 : Nat := 1561076697069947491993445

theorem tailTrace_3040186 : CollatzResearch.WordTrace tailWord_3040186 prefixEnd_3040186 1561076697069947491993445 := by
  unfold tailWord_3040186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27721173240983204819125103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73923128642621879517666941 27721173240983204819125103)
  ·
    refine ⟨41581759861474807228687655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27721173240983204819125103 41581759861474807228687655)
    ·
      refine ⟨62372639792212210843031483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41581759861474807228687655 62372639792212210843031483)
      ·
        refine ⟨93558959688318316264547225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62372639792212210843031483 93558959688318316264547225)
        ·
          refine ⟨70169219766238737198410419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93558959688318316264547225 70169219766238737198410419)
          ·
            refine ⟨105253829649358105797615629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70169219766238737198410419 105253829649358105797615629)
            ·
              refine ⟨39470186118509289674105861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105253829649358105797615629 39470186118509289674105861)
              ·
                refine ⟨7400659897220491813894849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39470186118509289674105861 7400659897220491813894849)
                ·
                  refine ⟨5550494922915368860421137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7400659897220491813894849 5550494922915368860421137)
                  ·
                    refine ⟨4162871192186526645315853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5550494922915368860421137 4162871192186526645315853)
                    ·
                      refine ⟨1561076697069947491993445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4162871192186526645315853 1561076697069947491993445)
                      ·
                        rfl

theorem cell23_3040186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_3040186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040186 prefixEnd_3040186 := by exact prefixLift 3040186
  have htrace : WordTrace (prefixWord ++ tailWord_3040186) baseStart_3040186 baseEnd_3040186 := by
    simpa [prefixWord, tailWord_3040186, baseEnd_3040186] using wordTrace_append hprefix tailTrace_3040186
  have hstable : (prefixWord ++ tailWord_3040186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040186).length < 2 ^ (prefixWord ++ tailWord_3040186).sum := by decide
  have hdescent : baseEnd_3040186 < baseStart_3040186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040206 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_3040206 : Nat := 118140960795 + 3040206 * 2 ^ 59
def prefixEnd_3040206 : Nat := 4983230072969 + 3 ^ 40 * 3040206 * 2
def baseEnd_3040206 : Nat := 173454107409226379304817

theorem tailTrace_3040206 : CollatzResearch.WordTrace tailWord_3040206 prefixEnd_3040206 173454107409226379304817 := by
  unfold tailWord_3040206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860677802982545336528559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73923614949240241794818981 13860677802982545336528559)
  ·
    refine ⟨20791016704473818004792839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13860677802982545336528559 20791016704473818004792839)
    ·
      refine ⟨31186525056710727007189259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20791016704473818004792839 31186525056710727007189259)
      ·
        refine ⟨46779787585066090510783889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31186525056710727007189259 46779787585066090510783889)
        ·
          refine ⟨35084840688799567883087917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46779787585066090510783889 35084840688799567883087917)
          ·
            refine ⟨13156815258299837956157969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35084840688799567883087917 13156815258299837956157969)
            ·
              refine ⟨9867611443724878467118477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13156815258299837956157969 9867611443724878467118477)
              ·
                refine ⟨3700354291396829425169429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9867611443724878467118477 3700354291396829425169429)
                ·
                  refine ⟨173454107409226379304817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3700354291396829425169429 173454107409226379304817)
                  ·
                    rfl

theorem cell23_3040206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_3040206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040206 prefixEnd_3040206 := by exact prefixLift 3040206
  have htrace : WordTrace (prefixWord ++ tailWord_3040206) baseStart_3040206 baseEnd_3040206 := by
    simpa [prefixWord, tailWord_3040206, baseEnd_3040206] using wordTrace_append hprefix tailTrace_3040206
  have hstable : (prefixWord ++ tailWord_3040206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040206).length < 2 ^ (prefixWord ++ tailWord_3040206).sum := by decide
  have hdescent : baseEnd_3040206 < baseStart_3040206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040284 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_3040284 : Nat := 118140960795 + 3040284 * 2 ^ 59
def prefixEnd_3040284 : Nat := 4983230072969 + 3 ^ 40 * 3040284 * 2
def baseEnd_3040284 : Nat := 1561127018174088108567995

theorem tailTrace_3040284 : CollatzResearch.WordTrace tailWord_3040284 prefixEnd_3040284 1561127018174088108567995 := by
  unfold tailWord_3040284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55444133658788891006783953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73925511545051854675711937 55444133658788891006783953)
  ·
    refine ⟨41583100244091668255087965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55444133658788891006783953 41583100244091668255087965)
    ·
      refine ⟨15593662591534375595657987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41583100244091668255087965 15593662591534375595657987)
      ·
        refine ⟨23390493887301563393486981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15593662591534375595657987 23390493887301563393486981)
        ·
          refine ⟨4385717603869043136278809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23390493887301563393486981 4385717603869043136278809)
          ·
            refine ⟨3289288202901782352209107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4385717603869043136278809 3289288202901782352209107)
            ·
              refine ⟨4933932304352673528313661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289288202901782352209107 4933932304352673528313661)
              ·
                refine ⟨1850224614132252573117623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4933932304352673528313661 1850224614132252573117623)
                ·
                  refine ⟨2775336921198378859676435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850224614132252573117623 2775336921198378859676435)
                  ·
                    refine ⟨4163005381797568289514653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2775336921198378859676435 4163005381797568289514653)
                    ·
                      refine ⟨1561127018174088108567995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4163005381797568289514653 1561127018174088108567995)
                      ·
                        rfl

theorem cell23_3040284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_3040284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040284 prefixEnd_3040284 := by exact prefixLift 3040284
  have htrace : WordTrace (prefixWord ++ tailWord_3040284) baseStart_3040284 baseEnd_3040284 := by
    simpa [prefixWord, tailWord_3040284, baseEnd_3040284] using wordTrace_append hprefix tailTrace_3040284
  have hstable : (prefixWord ++ tailWord_3040284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040284).length < 2 ^ (prefixWord ++ tailWord_3040284).sum := by decide
  have hdescent : baseEnd_3040284 < baseStart_3040284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040293 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_3040293 : Nat := 118140960795 + 3040293 * 2 ^ 59
def prefixEnd_3040293 : Nat := 4983230072969 + 3 ^ 40 * 3040293 * 2
def baseEnd_3040293 : Nat := 1561131639499978573355453

theorem tailTrace_3040293 : CollatzResearch.WordTrace tailWord_3040293 prefixEnd_3040293 1561131639499978573355453 := by
  unfold tailWord_3040293
  simp only [CollatzResearch.WordTrace]
  refine ⟨110888595574545176550645533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73925730383030117700430355 110888595574545176550645533)
  ·
    refine ⟨41583223340454441206492075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110888595574545176550645533 41583223340454441206492075)
    ·
      refine ⟨62374835010681661809738113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41583223340454441206492075 62374835010681661809738113)
      ·
        refine ⟨46781126258011246357303585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62374835010681661809738113 46781126258011246357303585)
        ·
          refine ⟨35085844693508434767977689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46781126258011246357303585 35085844693508434767977689)
          ·
            refine ⟨26314383520131326075983267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35085844693508434767977689 26314383520131326075983267)
            ·
              refine ⟨39471575280196989113974901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26314383520131326075983267 39471575280196989113974901)
              ·
                refine ⟨3700460182518467729435147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39471575280196989113974901 3700460182518467729435147)
                ·
                  refine ⟨5550690273777701594152721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700460182518467729435147 5550690273777701594152721)
                  ·
                    refine ⟨4163017705333276195614541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5550690273777701594152721 4163017705333276195614541)
                    ·
                      refine ⟨1561131639499978573355453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4163017705333276195614541 1561131639499978573355453)
                      ·
                        rfl

theorem cell23_3040293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_3040293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040293 prefixEnd_3040293 := by exact prefixLift 3040293
  have htrace : WordTrace (prefixWord ++ tailWord_3040293) baseStart_3040293 baseEnd_3040293 := by
    simpa [prefixWord, tailWord_3040293, baseEnd_3040293] using wordTrace_append hprefix tailTrace_3040293
  have hstable : (prefixWord ++ tailWord_3040293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040293).length < 2 ^ (prefixWord ++ tailWord_3040293).sum := by decide
  have hdescent : baseEnd_3040293 < baseStart_3040293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040317 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_3040317 : Nat := 118140960795 + 3040317 * 2 ^ 59
def prefixEnd_3040317 : Nat := 4983230072969 + 3 ^ 40 * 3040317 * 2
def baseEnd_3040317 : Nat := 520381321011895493151781

theorem tailTrace_3040317 : CollatzResearch.WordTrace tailWord_3040317 prefixEnd_3040317 520381321011895493151781 := by
  unfold tailWord_3040317
  simp only [CollatzResearch.WordTrace]
  refine ⟨110889470926458228649519205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73926313950972152433012803 110889470926458228649519205)
  ·
    refine ⟨20791775798710917871784851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110889470926458228649519205 20791775798710917871784851)
    ·
      refine ⟨31187663698066376807677277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20791775798710917871784851 31187663698066376807677277)
      ·
        refine ⟨11695373886774891302878979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31187663698066376807677277 11695373886774891302878979)
        ·
          refine ⟨17543060830162336954318469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11695373886774891302878979 17543060830162336954318469)
          ·
            refine ⟨3289323905655438178934713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17543060830162336954318469 3289323905655438178934713)
            ·
              refine ⟨2466992929241578634201035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3289323905655438178934713 2466992929241578634201035)
              ·
                refine ⟨3700489393862367951301553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466992929241578634201035 3700489393862367951301553)
                ·
                  refine ⟨2775367045396775963476165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3700489393862367951301553 2775367045396775963476165)
                  ·
                    refine ⟨520381321011895493151781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775367045396775963476165 520381321011895493151781)
                    ·
                      rfl

theorem cell23_3040317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_3040317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040317 prefixEnd_3040317 := by exact prefixLift 3040317
  have htrace : WordTrace (prefixWord ++ tailWord_3040317) baseStart_3040317 baseEnd_3040317 := by
    simpa [prefixWord, tailWord_3040317, baseEnd_3040317] using wordTrace_append hprefix tailTrace_3040317
  have hstable : (prefixWord ++ tailWord_3040317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040317).length < 2 ^ (prefixWord ++ tailWord_3040317).sum := by decide
  have hdescent : baseEnd_3040317 < baseStart_3040317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040356 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_3040356 : Nat := 118140960795 + 3040356 * 2 ^ 59
def prefixEnd_3040356 : Nat := 4983230072969 + 3 ^ 40 * 3040356 * 2
def baseEnd_3040356 : Nat := 520387996260403942289221

theorem tailTrace_3040356 : CollatzResearch.WordTrace tailWord_3040356 prefixEnd_3040356 520387996260403942289221 := by
  unfold tailWord_3040356
  simp only [CollatzResearch.WordTrace]
  refine ⟨55445446686658469155094461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73927262248877958873459281 55445446686658469155094461)
  ·
    refine ⟨20792042507496925933160423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55445446686658469155094461 20792042507496925933160423)
    ·
      refine ⟨31188063761245388899740635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20792042507496925933160423 31188063761245388899740635)
      ·
        refine ⟨46782095641868083349610953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188063761245388899740635 46782095641868083349610953)
        ·
          refine ⟨35086571731401062512208215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46782095641868083349610953 35086571731401062512208215)
          ·
            refine ⟨52629857597101593768312323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35086571731401062512208215 52629857597101593768312323)
            ·
              refine ⟨78944786395652390652468485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52629857597101593768312323 78944786395652390652468485)
              ·
                refine ⟨14802147449184823247337841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78944786395652390652468485 14802147449184823247337841)
                ·
                  refine ⟨11101610586888617435503381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14802147449184823247337841 11101610586888617435503381)
                  ·
                    refine ⟨520387996260403942289221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11101610586888617435503381 520387996260403942289221)
                    ·
                      rfl

theorem cell23_3040356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_3040356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040356 prefixEnd_3040356 := by exact prefixLift 3040356
  have htrace : WordTrace (prefixWord ++ tailWord_3040356) baseStart_3040356 baseEnd_3040356 := by
    simpa [prefixWord, tailWord_3040356, baseEnd_3040356] using wordTrace_append hprefix tailTrace_3040356
  have hstable : (prefixWord ++ tailWord_3040356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040356).length < 2 ^ (prefixWord ++ tailWord_3040356).sum := by decide
  have hdescent : baseEnd_3040356 < baseStart_3040356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040376 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3040376 : Nat := 118140960795 + 3040376 * 2 ^ 59
def prefixEnd_3040376 : Nat := 4983230072969 + 3 ^ 40 * 3040376 * 2
def baseEnd_3040376 : Nat := 1561174258394301748617571

theorem tailTrace_3040376 : CollatzResearch.WordTrace tailWord_3040376 prefixEnd_3040376 1561174258394301748617571 := by
  unfold tailWord_3040376
  simp only [CollatzResearch.WordTrace]
  refine ⟨55445811416622240862958491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73927748555496321150611321 55445811416622240862958491)
  ·
    refine ⟨83168717124933361294437737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55445811416622240862958491 83168717124933361294437737)
    ·
      refine ⟨62376537843700020970828303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83168717124933361294437737 62376537843700020970828303)
      ·
        refine ⟨93564806765550031456242455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62376537843700020970828303 93564806765550031456242455)
        ·
          refine ⟨140347210148325047184363683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93564806765550031456242455 140347210148325047184363683)
          ·
            refine ⟨210520815222487570776545525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140347210148325047184363683 210520815222487570776545525)
            ·
              refine ⟨19736326427108209760301143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210520815222487570776545525 19736326427108209760301143)
              ·
                refine ⟨29604489640662314640451715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19736326427108209760301143 29604489640662314640451715)
                ·
                  refine ⟨44406734460993471960677573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29604489640662314640451715 44406734460993471960677573)
                  ·
                    refine ⟨8326262711436275992627045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44406734460993471960677573 8326262711436275992627045)
                    ·
                      refine ⟨1561174258394301748617571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8326262711436275992627045 1561174258394301748617571)
                      ·
                        rfl

theorem cell23_3040376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3040376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040376 prefixEnd_3040376 := by exact prefixLift 3040376
  have htrace : WordTrace (prefixWord ++ tailWord_3040376) baseStart_3040376 baseEnd_3040376 := by
    simpa [prefixWord, tailWord_3040376, baseEnd_3040376] using wordTrace_append hprefix tailTrace_3040376
  have hstable : (prefixWord ++ tailWord_3040376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040376).length < 2 ^ (prefixWord ++ tailWord_3040376).sum := by decide
  have hdescent : baseEnd_3040376 < baseStart_3040376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040380 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_3040380 : Nat := 118140960795 + 3040380 * 2 ^ 59
def prefixEnd_3040380 : Nat := 4983230072969 + 3 ^ 40 * 3040380 * 2
def baseEnd_3040380 : Nat := 1561176312316919732967553

theorem tailTrace_3040380 : CollatzResearch.WordTrace tailWord_3040380 prefixEnd_3040380 1561176312316919732967553 := by
  unfold tailWord_3040380
  simp only [CollatzResearch.WordTrace]
  refine ⟨55445884362614995204531297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73927845816819993606041729 55445884362614995204531297)
  ·
    refine ⟨41584413271961246403398473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55445884362614995204531297 41584413271961246403398473)
    ·
      refine ⟨31188309953970934802548855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41584413271961246403398473 31188309953970934802548855)
      ·
        refine ⟨46782464930956402203823283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188309953970934802548855 46782464930956402203823283)
        ·
          refine ⟨70173697396434603305734925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46782464930956402203823283 70173697396434603305734925)
          ·
            refine ⟨26315136523662976239650597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70173697396434603305734925 26315136523662976239650597)
            ·
              refine ⟨4934088098186808044934487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26315136523662976239650597 4934088098186808044934487)
              ·
                refine ⟨7401132147280212067401731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934088098186808044934487 7401132147280212067401731)
                ·
                  refine ⟨11101698220920318101102597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7401132147280212067401731 11101698220920318101102597)
                  ·
                    refine ⟨2081568416422559643956737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11101698220920318101102597 2081568416422559643956737)
                    ·
                      refine ⟨1561176312316919732967553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081568416422559643956737 1561176312316919732967553)
                      ·
                        rfl

theorem cell23_3040380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_3040380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040380 prefixEnd_3040380 := by exact prefixLift 3040380
  have htrace : WordTrace (prefixWord ++ tailWord_3040380) baseStart_3040380 baseEnd_3040380 := by
    simpa [prefixWord, tailWord_3040380, baseEnd_3040380] using wordTrace_append hprefix tailTrace_3040380
  have hstable : (prefixWord ++ tailWord_3040380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040380).length < 2 ^ (prefixWord ++ tailWord_3040380).sum := by decide
  have hdescent : baseEnd_3040380 < baseStart_3040380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040403 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 5]
def baseStart_3040403 : Nat := 118140960795 + 3040403 * 2 ^ 59
def prefixEnd_3040403 : Nat := 4983230072969 + 3 ^ 40 * 3040403 * 2
def baseEnd_3040403 : Nat := 173465346930219238108883

theorem tailTrace_3040403 : CollatzResearch.WordTrace tailWord_3040403 prefixEnd_3040403 173465346930219238108883 := by
  unfold tailWord_3040403
  simp only [CollatzResearch.WordTrace]
  refine ⟨110892607604146665337149863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73928405069431110224766575 110892607604146665337149863)
  ·
    refine ⟨166338911406219998005724795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110892607604146665337149863 166338911406219998005724795)
    ·
      refine ⟨249508367109329997008587193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166338911406219998005724795 249508367109329997008587193)
      ·
        refine ⟨187131275331997497756440395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249508367109329997008587193 187131275331997497756440395)
        ·
          refine ⟨280696912997996246634660593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187131275331997497756440395 280696912997996246634660593)
          ·
            refine ⟨210522684748497184975995445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280696912997996246634660593 210522684748497184975995445)
            ·
              refine ⟨19736501695171611091499573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210522684748497184975995445 19736501695171611091499573)
              ·
                refine ⟨1850297033922338539828085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19736501695171611091499573 1850297033922338539828085)
                ·
                  refine ⟨173465346930219238108883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850297033922338539828085 173465346930219238108883)
                  ·
                    rfl

theorem cell23_3040403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 5].length) (baseStart_3040403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040403 prefixEnd_3040403 := by exact prefixLift 3040403
  have htrace : WordTrace (prefixWord ++ tailWord_3040403) baseStart_3040403 baseEnd_3040403 := by
    simpa [prefixWord, tailWord_3040403, baseEnd_3040403] using wordTrace_append hprefix tailTrace_3040403
  have hstable : (prefixWord ++ tailWord_3040403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040403).length < 2 ^ (prefixWord ++ tailWord_3040403).sum := by decide
  have hdescent : baseEnd_3040403 < baseStart_3040403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040413 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3040413 : Nat := 118140960795 + 3040413 * 2 ^ 59
def prefixEnd_3040413 : Nat := 4983230072969 + 3 ^ 40 * 3040413 * 2
def baseEnd_3040413 : Nat := 1561193257178518103854901

theorem tailTrace_3040413 : CollatzResearch.WordTrace tailWord_3040413 prefixEnd_3040413 1561193257178518103854901 := by
  unfold tailWord_3040413
  simp only [CollatzResearch.WordTrace]
  refine ⟨110892972334110437045013893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73928648222740291363342595 110892972334110437045013893)
  ·
    refine ⟨20792432312645706945940105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110892972334110437045013893 20792432312645706945940105)
    ·
      refine ⟨15594324234484280209455079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20792432312645706945940105 15594324234484280209455079)
      ·
        refine ⟨23391486351726420314182619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15594324234484280209455079 23391486351726420314182619)
        ·
          refine ⟨35087229527589630471273929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23391486351726420314182619 35087229527589630471273929)
          ·
            refine ⟨26315422145692222853455447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35087229527589630471273929 26315422145692222853455447)
            ·
              refine ⟨39473133218538334280183171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26315422145692222853455447 39473133218538334280183171)
              ·
                refine ⟨59209699827807501420274757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39473133218538334280183171 59209699827807501420274757)
                ·
                  refine ⟨11101818717713906516301517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59209699827807501420274757 11101818717713906516301517)
                  ·
                    refine ⟨4163182019142714943613069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11101818717713906516301517 4163182019142714943613069)
                    ·
                      refine ⟨1561193257178518103854901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4163182019142714943613069 1561193257178518103854901)
                      ·
                        rfl

theorem cell23_3040413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3040413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040413 prefixEnd_3040413 := by exact prefixLift 3040413
  have htrace : WordTrace (prefixWord ++ tailWord_3040413) baseStart_3040413 baseEnd_3040413 := by
    simpa [prefixWord, tailWord_3040413, baseEnd_3040413] using wordTrace_append hprefix tailTrace_3040413
  have hstable : (prefixWord ++ tailWord_3040413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040413).length < 2 ^ (prefixWord ++ tailWord_3040413).sum := by decide
  have hdescent : baseEnd_3040413 < baseStart_3040413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040414 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_3040414 : Nat := 118140960795 + 3040414 * 2 ^ 59
def prefixEnd_3040414 : Nat := 4983230072969 + 3 ^ 40 * 3040414 * 2
def baseEnd_3040414 : Nat := 1561193770659172599942397

theorem tailTrace_3040414 : CollatzResearch.WordTrace tailWord_3040414 prefixEnd_3040414 1561193770659172599942397 := by
  unfold tailWord_3040414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13861626100888351776975037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73928672538071209477200197 13861626100888351776975037)
  ·
    refine ⟨5198109787833131916365639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13861626100888351776975037 5198109787833131916365639)
    ·
      refine ⟨7797164681749697874548459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5198109787833131916365639 7797164681749697874548459)
      ·
        refine ⟨11695747022624546811822689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7797164681749697874548459 11695747022624546811822689)
        ·
          refine ⟨8771810266968410108867017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11695747022624546811822689 8771810266968410108867017)
          ·
            refine ⟨6578857700226307581650263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8771810266968410108867017 6578857700226307581650263)
            ·
              refine ⟨9868286550339461372475395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578857700226307581650263 9868286550339461372475395)
              ·
                refine ⟨14802429825509192058713093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868286550339461372475395 14802429825509192058713093)
                ·
                  refine ⟨2775455592282973511008705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14802429825509192058713093 2775455592282973511008705)
                  ·
                    refine ⟨2081591694212230133256529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775455592282973511008705 2081591694212230133256529)
                    ·
                      refine ⟨1561193770659172599942397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081591694212230133256529 1561193770659172599942397)
                      ·
                        rfl

theorem cell23_3040414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_3040414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040414 prefixEnd_3040414 := by exact prefixLift 3040414
  have htrace : WordTrace (prefixWord ++ tailWord_3040414) baseStart_3040414 baseEnd_3040414 := by
    simpa [prefixWord, tailWord_3040414, baseEnd_3040414] using wordTrace_append hprefix tailTrace_3040414
  have hstable : (prefixWord ++ tailWord_3040414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040414).length < 2 ^ (prefixWord ++ tailWord_3040414).sum := by decide
  have hdescent : baseEnd_3040414 < baseStart_3040414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040420 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 5]
def baseStart_3040420 : Nat := 118140960795 + 3040420 * 2 ^ 59
def prefixEnd_3040420 : Nat := 4983230072969 + 3 ^ 40 * 3040420 * 2
def baseEnd_3040420 : Nat := 173466316838122175163041

theorem tailTrace_3040420 : CollatzResearch.WordTrace tailWord_3040420 prefixEnd_3040420 173466316838122175163041 := by
  unfold tailWord_3040420
  simp only [CollatzResearch.WordTrace]
  refine ⟨55446613822542538620259357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73928818430056718160345809 55446613822542538620259357)
  ·
    refine ⟨20792480183453451982597259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55446613822542538620259357 20792480183453451982597259)
    ·
      refine ⟨31188720275180177973895889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20792480183453451982597259 31188720275180177973895889)
      ·
        refine ⟨23391540206385133480421917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31188720275180177973895889 23391540206385133480421917)
        ·
          refine ⟨8771827577394425055158219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23391540206385133480421917 8771827577394425055158219)
          ·
            refine ⟨13157741366091637582737329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8771827577394425055158219 13157741366091637582737329)
            ·
              refine ⟨9868306024568728187052997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13157741366091637582737329 9868306024568728187052997)
              ·
                refine ⟨1850307379606636535072437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9868306024568728187052997 1850307379606636535072437)
                ·
                  refine ⟨173466316838122175163041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850307379606636535072437 173466316838122175163041)
                  ·
                    rfl

theorem cell23_3040420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_3040420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040420 prefixEnd_3040420 := by exact prefixLift 3040420
  have htrace : WordTrace (prefixWord ++ tailWord_3040420) baseStart_3040420 baseEnd_3040420 := by
    simpa [prefixWord, tailWord_3040420, baseEnd_3040420] using wordTrace_append hprefix tailTrace_3040420
  have hstable : (prefixWord ++ tailWord_3040420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040420).length < 2 ^ (prefixWord ++ tailWord_3040420).sum := by decide
  have hdescent : baseEnd_3040420 < baseStart_3040420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040433 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_3040433 : Nat := 118140960795 + 3040433 * 2 ^ 59
def prefixEnd_3040433 : Nat := 4983230072969 + 3 ^ 40 * 3040433 * 2
def baseEnd_3040433 : Nat := 520401175597202675201603

theorem tailTrace_3040433 : CollatzResearch.WordTrace tailWord_3040433 prefixEnd_3040433 520401175597202675201603 := by
  unfold tailWord_3040433
  simp only [CollatzResearch.WordTrace]
  refine ⟨110893701794037980460741953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73929134529358653640494635 110893701794037980460741953)
  ·
    refine ⟨83170276345528485345556465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110893701794037980460741953 83170276345528485345556465)
    ·
      refine ⟨62377707259146364009167349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83170276345528485345556465 62377707259146364009167349)
      ·
        refine ⟨5847910055544971625859439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62377707259146364009167349 5847910055544971625859439)
        ·
          refine ⟨8771865083317457438789159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847910055544971625859439 8771865083317457438789159)
          ·
            refine ⟨13157797624976186158183739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8771865083317457438789159 13157797624976186158183739)
            ·
              refine ⟨19736696437464279237275609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13157797624976186158183739 19736696437464279237275609)
              ·
                refine ⟨14802522328098209427956707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19736696437464279237275609 14802522328098209427956707)
                ·
                  refine ⟨22203783492147314141935061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14802522328098209427956707 22203783492147314141935061)
                  ·
                    refine ⟨520401175597202675201603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22203783492147314141935061 520401175597202675201603)
                    ·
                      rfl

theorem cell23_3040433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_3040433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040433 prefixEnd_3040433 := by exact prefixLift 3040433
  have htrace : WordTrace (prefixWord ++ tailWord_3040433) baseStart_3040433 baseEnd_3040433 := by
    simpa [prefixWord, tailWord_3040433, baseEnd_3040433] using wordTrace_append hprefix tailTrace_3040433
  have hstable : (prefixWord ++ tailWord_3040433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040433).length < 2 ^ (prefixWord ++ tailWord_3040433).sum := by decide
  have hdescent : baseEnd_3040433 < baseStart_3040433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040453 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_3040453 : Nat := 118140960795 + 3040453 * 2 ^ 59
def prefixEnd_3040453 : Nat := 4983230072969 + 3 ^ 40 * 3040453 * 2
def baseEnd_3040453 : Nat := 1561213796404697947354717

theorem tailTrace_3040453 : CollatzResearch.WordTrace tailWord_3040453 prefixEnd_3040453 1561213796404697947354717 := by
  unfold tailWord_3040453
  simp only [CollatzResearch.WordTrace]
  refine ⟨110894431253965523876470013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73929620835977015917646675 110894431253965523876470013)
  ·
    refine ⟨41585411720237071453676255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110894431253965523876470013 41585411720237071453676255)
    ·
      refine ⟨62378117580355607180514383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41585411720237071453676255 62378117580355607180514383)
      ·
        refine ⟨93567176370533410770771575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62378117580355607180514383 93567176370533410770771575)
        ·
          refine ⟨140350764555800116156157363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93567176370533410770771575 140350764555800116156157363)
          ·
            refine ⟨210526146833700174234236045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140350764555800116156157363 210526146833700174234236045)
            ·
              refine ⟨78947305062637565337838517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210526146833700174234236045 78947305062637565337838517)
              ·
                refine ⟨7401309849622271750422361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78947305062637565337838517 7401309849622271750422361)
                ·
                  refine ⟨5550982387216703812816771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7401309849622271750422361 5550982387216703812816771)
                  ·
                    refine ⟨8326473580825055719225157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5550982387216703812816771 8326473580825055719225157)
                    ·
                      refine ⟨1561213796404697947354717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8326473580825055719225157 1561213796404697947354717)
                      ·
                        rfl

theorem cell23_3040453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_3040453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040453 prefixEnd_3040453 := by exact prefixLift 3040453
  have htrace : WordTrace (prefixWord ++ tailWord_3040453) baseStart_3040453 baseEnd_3040453 := by
    simpa [prefixWord, tailWord_3040453, baseEnd_3040453] using wordTrace_append hprefix tailTrace_3040453
  have hstable : (prefixWord ++ tailWord_3040453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040453).length < 2 ^ (prefixWord ++ tailWord_3040453).sum := by decide
  have hdescent : baseEnd_3040453 < baseStart_3040453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040480 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_3040480 : Nat := 118140960795 + 3040480 * 2 ^ 59
def prefixEnd_3040480 : Nat := 4983230072969 + 3 ^ 40 * 3040480 * 2
def baseEnd_3040480 : Nat := 520409220127456447239031

theorem tailTrace_3040480 : CollatzResearch.WordTrace tailWord_3040480 prefixEnd_3040480 520409220127456447239031 := by
  unfold tailWord_3040480
  simp only [CollatzResearch.WordTrace]
  refine ⟨55447708012433853743851447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73930277349911804991801929 55447708012433853743851447)
  ·
    refine ⟨83171562018650780615777171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55447708012433853743851447 83171562018650780615777171)
    ·
      refine ⟨124757343027976170923665757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83171562018650780615777171 124757343027976170923665757)
      ·
        refine ⟨46784003635491064096374659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124757343027976170923665757 46784003635491064096374659)
        ·
          refine ⟨70176005453236596144561989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46784003635491064096374659 70176005453236596144561989)
          ·
            refine ⟨13158001022481861777105373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70176005453236596144561989 13158001022481861777105373)
            ·
              refine ⟨4934250383430698166414515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13158001022481861777105373 4934250383430698166414515)
              ·
                refine ⟨7401375575146047249621773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934250383430698166414515 7401375575146047249621773)
                ·
                  refine ⟨2775515840679767718608165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7401375575146047249621773 2775515840679767718608165)
                  ·
                    refine ⟨520409220127456447239031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775515840679767718608165 520409220127456447239031)
                    ·
                      rfl

theorem cell23_3040480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_3040480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040480 prefixEnd_3040480 := by exact prefixLift 3040480
  have htrace : WordTrace (prefixWord ++ tailWord_3040480) baseStart_3040480 baseEnd_3040480 := by
    simpa [prefixWord, tailWord_3040480, baseEnd_3040480] using wordTrace_append hprefix tailTrace_3040480
  have hstable : (prefixWord ++ tailWord_3040480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040480).length < 2 ^ (prefixWord ++ tailWord_3040480).sum := by decide
  have hdescent : baseEnd_3040480 < baseStart_3040480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040554 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3040554 : Nat := 118140960795 + 3040554 * 2 ^ 59
def prefixEnd_3040554 : Nat := 4983230072969 + 3 ^ 40 * 3040554 * 2
def baseEnd_3040554 : Nat := 1561265657950802052191753

theorem tailTrace_3040554 : CollatzResearch.WordTrace tailWord_3040554 prefixEnd_3040554 1561265657950802052191753 := by
  unfold tailWord_3040554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724528756649904531474179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73932076684399745417264477 27724528756649904531474179)
  ·
    refine ⟨41586793134974856797211269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724528756649904531474179 41586793134974856797211269)
    ·
      refine ⟨7797523712807785649477113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41586793134974856797211269 7797523712807785649477113)
      ·
        refine ⟨5848142784605839237107835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7797523712807785649477113 5848142784605839237107835)
        ·
          refine ⟨8772214176908758855661753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848142784605839237107835 8772214176908758855661753)
          ·
            refine ⟨6579160632681569141746315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8772214176908758855661753 6579160632681569141746315)
            ·
              refine ⟨9868740949022353712619473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579160632681569141746315 9868740949022353712619473)
              ·
                refine ⟨7401555711766765284464605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9868740949022353712619473 7401555711766765284464605)
                ·
                  refine ⟨2775583391912536981674227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7401555711766765284464605 2775583391912536981674227)
                  ·
                    refine ⟨4163375087868805472511341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2775583391912536981674227 4163375087868805472511341)
                    ·
                      refine ⟨1561265657950802052191753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4163375087868805472511341 1561265657950802052191753)
                      ·
                        rfl

theorem cell23_3040554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3040554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040554 prefixEnd_3040554 := by exact prefixLift 3040554
  have htrace : WordTrace (prefixWord ++ tailWord_3040554) baseStart_3040554 baseEnd_3040554 := by
    simpa [prefixWord, tailWord_3040554, baseEnd_3040554] using wordTrace_append hprefix tailTrace_3040554
  have hstable : (prefixWord ++ tailWord_3040554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040554).length < 2 ^ (prefixWord ++ tailWord_3040554).sum := by decide
  have hdescent : baseEnd_3040554 < baseStart_3040554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040557 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3040557 : Nat := 118140960795 + 3040557 * 2 ^ 59
def prefixEnd_3040557 : Nat := 4983230072969 + 3 ^ 40 * 3040557 * 2
def baseEnd_3040557 : Nat := 520422399464255180151413

theorem tailTrace_3040557 : CollatzResearch.WordTrace tailWord_3040557 prefixEnd_3040557 520422399464255180151413 := by
  unfold tailWord_3040557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110898224445588749638255925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73932149630392499758837283 110898224445588749638255925)
  ·
    refine ⟨10396708541773945278586493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110898224445588749638255925 10396708541773945278586493)
    ·
      refine ⟨3898765703165229479469935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10396708541773945278586493 3898765703165229479469935)
      ·
        refine ⟨5848148554747844219204903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898765703165229479469935 5848148554747844219204903)
        ·
          refine ⟨8772222832121766328807355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848148554747844219204903 8772222832121766328807355)
          ·
            refine ⟨13158334248182649493211033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8772222832121766328807355 13158334248182649493211033)
            ·
              refine ⟨9868750686136987119908275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13158334248182649493211033 9868750686136987119908275)
              ·
                refine ⟨14803126029205480679862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868750686136987119908275 14803126029205480679862413)
                ·
                  refine ⟨5551172260952055254948405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14803126029205480679862413 5551172260952055254948405)
                  ·
                    refine ⟨520422399464255180151413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5551172260952055254948405 520422399464255180151413)
                    ·
                      rfl

theorem cell23_3040557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3040557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040557 prefixEnd_3040557 := by exact prefixLift 3040557
  have htrace : WordTrace (prefixWord ++ tailWord_3040557) baseStart_3040557 baseEnd_3040557 := by
    simpa [prefixWord, tailWord_3040557, baseEnd_3040557] using wordTrace_append hprefix tailTrace_3040557
  have hstable : (prefixWord ++ tailWord_3040557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040557).length < 2 ^ (prefixWord ++ tailWord_3040557).sum := by decide
  have hdescent : baseEnd_3040557 < baseStart_3040557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040560 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_3040560 : Nat := 118140960795 + 3040560 * 2 ^ 59
def prefixEnd_3040560 : Nat := 4983230072969 + 3 ^ 40 * 3040560 * 2
def baseEnd_3040560 : Nat := 1561268738834729028716725

theorem tailTrace_3040560 : CollatzResearch.WordTrace tailWord_3040560 prefixEnd_3040560 1561268738834729028716725 := by
  unfold tailWord_3040560
  simp only [CollatzResearch.WordTrace]
  refine ⟨55449166932288940575307567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73932222576385254100410089 55449166932288940575307567)
  ·
    refine ⟨83173750398433410862961351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55449166932288940575307567 83173750398433410862961351)
    ·
      refine ⟨124760625597650116294442027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83173750398433410862961351 124760625597650116294442027)
      ·
        refine ⟨187140938396475174441663041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124760625597650116294442027 187140938396475174441663041)
        ·
          refine ⟨140355703797356380831247281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187140938396475174441663041 140355703797356380831247281)
          ·
            refine ⟨105266777848017285623435461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140355703797356380831247281 105266777848017285623435461)
            ·
              refine ⟨19737520846503241054394149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105266777848017285623435461 19737520846503241054394149)
              ·
                refine ⟨3700785158719357697698903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19737520846503241054394149 3700785158719357697698903)
                ·
                  refine ⟨5551177738079036546548355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700785158719357697698903 5551177738079036546548355)
                  ·
                    refine ⟨8326766607118554819822533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5551177738079036546548355 8326766607118554819822533)
                    ·
                      refine ⟨1561268738834729028716725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8326766607118554819822533 1561268738834729028716725)
                      ·
                        rfl

theorem cell23_3040560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_3040560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040560 prefixEnd_3040560 := by exact prefixLift 3040560
  have htrace : WordTrace (prefixWord ++ tailWord_3040560) baseStart_3040560 baseEnd_3040560 := by
    simpa [prefixWord, tailWord_3040560, baseEnd_3040560] using wordTrace_append hprefix tailTrace_3040560
  have hstable : (prefixWord ++ tailWord_3040560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040560).length < 2 ^ (prefixWord ++ tailWord_3040560).sum := by decide
  have hdescent : baseEnd_3040560 < baseStart_3040560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040570 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_3040570 : Nat := 118140960795 + 3040570 * 2 ^ 59
def prefixEnd_3040570 : Nat := 4983230072969 + 3 ^ 40 * 3040570 * 2
def baseEnd_3040570 : Nat := 520424624547091329863893

theorem tailTrace_3040570 : CollatzResearch.WordTrace tailWord_3040570 prefixEnd_3040570 520424624547091329863893 := by
  unfold tailWord_3040570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724674648635413214619791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73932465729694435238986109 27724674648635413214619791)
  ·
    refine ⟨41587011972953119821929687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724674648635413214619791 41587011972953119821929687)
    ·
      refine ⟨62380517959429679732894531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41587011972953119821929687 62380517959429679732894531)
      ·
        refine ⟨93570776939144519599341797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62380517959429679732894531 93570776939144519599341797)
        ·
          refine ⟨17544520676089597424876587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93570776939144519599341797 17544520676089597424876587)
          ·
            refine ⟨26316781014134396137314881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17544520676089597424876587 26316781014134396137314881)
            ·
              refine ⟨19737585760600797102986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26316781014134396137314881 19737585760600797102986161)
              ·
                refine ⟨14803189320450597827239621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19737585760600797102986161 14803189320450597827239621)
                ·
                  refine ⟨2775597997584487092607429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14803189320450597827239621 2775597997584487092607429)
                  ·
                    refine ⟨520424624547091329863893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775597997584487092607429 520424624547091329863893)
                    ·
                      rfl

theorem cell23_3040570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_3040570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040570 prefixEnd_3040570 := by exact prefixLift 3040570
  have htrace : WordTrace (prefixWord ++ tailWord_3040570) baseStart_3040570 baseEnd_3040570 := by
    simpa [prefixWord, tailWord_3040570, baseEnd_3040570] using wordTrace_append hprefix tailTrace_3040570
  have hstable : (prefixWord ++ tailWord_3040570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040570).length < 2 ^ (prefixWord ++ tailWord_3040570).sum := by decide
  have hdescent : baseEnd_3040570 < baseStart_3040570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040583 : List Nat := [1, 1, 4, 1, 2, 4, 10]
def baseStart_3040583 : Nat := 118140960795 + 3040583 * 2 ^ 59
def prefixEnd_3040583 : Nat := 4983230072969 + 3 ^ 40 * 3040583 * 2
def baseEnd_3040583 : Nat := 19275068504812128873199

theorem tailTrace_3040583 : CollatzResearch.WordTrace tailWord_3040583 prefixEnd_3040583 19275068504812128873199 := by
  unfold tailWord_3040583
  simp only [CollatzResearch.WordTrace]
  refine ⟨110899172743494556078702403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73932781828996370719134935 110899172743494556078702403)
  ·
    refine ⟨166348759115241834118053605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110899172743494556078702403 166348759115241834118053605)
    ·
      refine ⟨31190392334107843897135051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166348759115241834118053605 31190392334107843897135051)
      ·
        refine ⟨46785588501161765845702577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31190392334107843897135051 46785588501161765845702577)
        ·
          refine ⟨35089191375871324384276933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46785588501161765845702577 35089191375871324384276933)
          ·
            refine ⟨6579223382975873322051925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35089191375871324384276933 6579223382975873322051925)
            ·
              refine ⟨19275068504812128873199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6579223382975873322051925 19275068504812128873199)
              ·
                rfl

theorem cell23_3040583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 10].length) (baseStart_3040583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040583 prefixEnd_3040583 := by exact prefixLift 3040583
  have htrace : WordTrace (prefixWord ++ tailWord_3040583) baseStart_3040583 baseEnd_3040583 := by
    simpa [prefixWord, tailWord_3040583, baseEnd_3040583] using wordTrace_append hprefix tailTrace_3040583
  have hstable : (prefixWord ++ tailWord_3040583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040583).length < 2 ^ (prefixWord ++ tailWord_3040583).sum := by decide
  have hdescent : baseEnd_3040583 < baseStart_3040583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040623 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_3040623 : Nat := 118140960795 + 3040623 * 2 ^ 59
def prefixEnd_3040623 : Nat := 4983230072969 + 3 ^ 40 * 3040623 * 2
def baseEnd_3040623 : Nat := 1561301088115962282228935

theorem tailTrace_3040623 : CollatzResearch.WordTrace tailWord_3040623 prefixEnd_3040623 1561301088115962282228935 := by
  unfold tailWord_3040623
  simp only [CollatzResearch.WordTrace]
  refine ⟨110900631663349642910158523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73933754442233095273439015 110900631663349642910158523)
  ·
    refine ⟨166350947495024464365237785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110900631663349642910158523 166350947495024464365237785)
    ·
      refine ⟨124763210621268348273928339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166350947495024464365237785 124763210621268348273928339)
      ·
        refine ⟨187144815931902522410892509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124763210621268348273928339 187144815931902522410892509)
        ·
          refine ⟨70179305974463445904084691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187144815931902522410892509 70179305974463445904084691)
          ·
            refine ⟨105268958961695168856127037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70179305974463445904084691 105268958961695168856127037)
            ·
              refine ⟨39475859610635688321047639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105268958961695168856127037 39475859610635688321047639)
              ·
                refine ⟨59213789415953532481571459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39475859610635688321047639 59213789415953532481571459)
                ·
                  refine ⟨88820684123930298722357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59213789415953532481571459 88820684123930298722357189)
                  ·
                    refine ⟨16653878273236931010441973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88820684123930298722357189 16653878273236931010441973)
                    ·
                      refine ⟨1561301088115962282228935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16653878273236931010441973 1561301088115962282228935)
                      ·
                        rfl

theorem cell23_3040623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_3040623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040623 prefixEnd_3040623 := by exact prefixLift 3040623
  have htrace : WordTrace (prefixWord ++ tailWord_3040623) baseStart_3040623 baseEnd_3040623 := by
    simpa [prefixWord, tailWord_3040623, baseEnd_3040623] using wordTrace_append hprefix tailTrace_3040623
  have hstable : (prefixWord ++ tailWord_3040623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040623).length < 2 ^ (prefixWord ++ tailWord_3040623).sum := by decide
  have hdescent : baseEnd_3040623 < baseStart_3040623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040671 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 1, 3, 2]
def baseStart_3040671 : Nat := 118140960795 + 3040671 * 2 ^ 59
def prefixEnd_3040671 : Nat := 4983230072969 + 3 ^ 40 * 3040671 * 2
def baseEnd_3040671 : Nat := 1561325735187378094428715

theorem tailTrace_3040671 : CollatzResearch.WordTrace tailWord_3040671 prefixEnd_3040671 1561325735187378094428715 := by
  unfold tailWord_3040671
  simp only [CollatzResearch.WordTrace]
  refine ⟨110902382367175747107905867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73934921578117164738603911 110902382367175747107905867)
  ·
    refine ⟨166353573550763620661858801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110902382367175747107905867 166353573550763620661858801)
    ·
      refine ⟨124765180163072715496394101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166353573550763620661858801 124765180163072715496394101)
      ·
        refine ⟨11696735640288067077786947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124765180163072715496394101 11696735640288067077786947)
        ·
          refine ⟨17545103460432100616680421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11696735640288067077786947 17545103460432100616680421)
          ·
            refine ⟨3289706898831018865627579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17545103460432100616680421 3289706898831018865627579)
            ·
              refine ⟨4934560348246528298441369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289706898831018865627579 4934560348246528298441369)
              ·
                refine ⟨3700920261184896223831027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934560348246528298441369 3700920261184896223831027)
                ·
                  refine ⟨5551380391777344335746541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700920261184896223831027 5551380391777344335746541)
                  ·
                    refine ⟨2081767646916504125904953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5551380391777344335746541 2081767646916504125904953)
                    ·
                      refine ⟨1561325735187378094428715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081767646916504125904953 1561325735187378094428715)
                      ·
                        rfl

theorem cell23_3040671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_3040671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040671 prefixEnd_3040671 := by exact prefixLift 3040671
  have htrace : WordTrace (prefixWord ++ tailWord_3040671) baseStart_3040671 baseEnd_3040671 := by
    simpa [prefixWord, tailWord_3040671, baseEnd_3040671] using wordTrace_append hprefix tailTrace_3040671
  have hstable : (prefixWord ++ tailWord_3040671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040671).length < 2 ^ (prefixWord ++ tailWord_3040671).sum := by decide
  have hdescent : baseEnd_3040671 < baseStart_3040671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040683 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_3040683 : Nat := 118140960795 + 3040683 * 2 ^ 59
def prefixEnd_3040683 : Nat := 4983230072969 + 3 ^ 40 * 3040683 * 2
def baseEnd_3040683 : Nat := 1561331896955232047478659

theorem tailTrace_3040683 : CollatzResearch.WordTrace tailWord_3040683 prefixEnd_3040683 1561331896955232047478659 := by
  unfold tailWord_3040683
  simp only [CollatzResearch.WordTrace]
  refine ⟨110902820043132273157342703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73935213362088182104895135 110902820043132273157342703)
  ·
    refine ⟨166354230064698409736014055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110902820043132273157342703 166354230064698409736014055)
    ·
      refine ⟨249531345097047614604021083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166354230064698409736014055 249531345097047614604021083)
      ·
        refine ⟨374297017645571421906031625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249531345097047614604021083 374297017645571421906031625)
        ·
          refine ⟨280722763234178566429523719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374297017645571421906031625 280722763234178566429523719)
          ·
            refine ⟨421084144851267849644285579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280722763234178566429523719 421084144851267849644285579)
            ·
              refine ⟨631626217276901774466428369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421084144851267849644285579 631626217276901774466428369)
              ·
                refine ⟨473719662957676330849821277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631626217276901774466428369 473719662957676330849821277)
                ·
                  refine ⟨177644873609128624068682979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473719662957676330849821277 177644873609128624068682979)
                  ·
                    refine ⟨266467310413692936103024469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177644873609128624068682979 266467310413692936103024469)
                    ·
                      refine ⟨1561331896955232047478659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 266467310413692936103024469 1561331896955232047478659)
                      ·
                        rfl

theorem cell23_3040683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_3040683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040683 prefixEnd_3040683 := by exact prefixLift 3040683
  have htrace : WordTrace (prefixWord ++ tailWord_3040683) baseStart_3040683 baseEnd_3040683 := by
    simpa [prefixWord, tailWord_3040683, baseEnd_3040683] using wordTrace_append hprefix tailTrace_3040683
  have hstable : (prefixWord ++ tailWord_3040683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040683).length < 2 ^ (prefixWord ++ tailWord_3040683).sum := by decide
  have hdescent : baseEnd_3040683 < baseStart_3040683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040701 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_3040701 : Nat := 118140960795 + 3040701 * 2 ^ 59
def prefixEnd_3040701 : Nat := 4983230072969 + 3 ^ 40 * 3040701 * 2
def baseEnd_3040701 : Nat := 1561341139607012977053577

theorem tailTrace_3040701 : CollatzResearch.WordTrace tailWord_3040701 prefixEnd_3040701 1561341139607012977053577 := by
  unfold tailWord_3040701
  simp only [CollatzResearch.WordTrace]
  refine ⟨110903476557067062231497957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73935651038044708154331971 110903476557067062231497957)
  ·
    refine ⟨20794401854450074168405867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110903476557067062231497957 20794401854450074168405867)
    ·
      refine ⟨31191602781675111252608801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20794401854450074168405867 31191602781675111252608801)
      ·
        refine ⟨23393702086256333439456601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31191602781675111252608801 23393702086256333439456601)
        ·
          refine ⟨17545276564692250079592451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23393702086256333439456601 17545276564692250079592451)
          ·
            refine ⟨26317914847038375119388677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17545276564692250079592451 26317914847038375119388677)
            ·
              refine ⟨4934609033819695334885377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26317914847038375119388677 4934609033819695334885377)
              ·
                refine ⟨3700956775364771501164033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934609033819695334885377 3700956775364771501164033)
                ·
                  refine ⟨2775717581523578625873025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3700956775364771501164033 2775717581523578625873025)
                  ·
                    refine ⟨2081788186142683969404769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775717581523578625873025 2081788186142683969404769)
                    ·
                      refine ⟨1561341139607012977053577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081788186142683969404769 1561341139607012977053577)
                      ·
                        rfl

theorem cell23_3040701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_3040701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040701 prefixEnd_3040701 := by exact prefixLift 3040701
  have htrace : WordTrace (prefixWord ++ tailWord_3040701) baseStart_3040701 baseEnd_3040701 := by
    simpa [prefixWord, tailWord_3040701, baseEnd_3040701] using wordTrace_append hprefix tailTrace_3040701
  have hstable : (prefixWord ++ tailWord_3040701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040701).length < 2 ^ (prefixWord ++ tailWord_3040701).sum := by decide
  have hdescent : baseEnd_3040701 < baseStart_3040701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040737 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_3040737 : Nat := 118140960795 + 3040737 * 2 ^ 59
def prefixEnd_3040737 : Nat := 4983230072969 + 3 ^ 40 * 3040737 * 2
def baseEnd_3040737 : Nat := 520453208303524945401137

theorem tailTrace_3040737 : CollatzResearch.WordTrace tailWord_3040737 prefixEnd_3040737 520453208303524945401137 := by
  unfold tailWord_3040737
  simp only [CollatzResearch.WordTrace]
  refine ⟨110904789584936640379808465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73936526389957760253205643 110904789584936640379808465)
  ·
    refine ⟨83178592188702480284856349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110904789584936640379808465 83178592188702480284856349)
    ·
      refine ⟨31191972070763430106821131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83178592188702480284856349 31191972070763430106821131)
      ·
        refine ⟨46787958106145145160231697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31191972070763430106821131 46787958106145145160231697)
        ·
          refine ⟨35090968579608858870173773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46787958106145145160231697 35090968579608858870173773)
          ·
            refine ⟨13159113217353322076315165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35090968579608858870173773 13159113217353322076315165)
            ·
              refine ⟨4934667456507495778618187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13159113217353322076315165 4934667456507495778618187)
              ·
                refine ⟨7402001184761243667927281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934667456507495778618187 7402001184761243667927281)
                ·
                  refine ⟨5551500888570932750945461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7402001184761243667927281 5551500888570932750945461)
                  ·
                    refine ⟨520453208303524945401137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5551500888570932750945461 520453208303524945401137)
                    ·
                      rfl

theorem cell23_3040737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_3040737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040737 prefixEnd_3040737 := by exact prefixLift 3040737
  have htrace : WordTrace (prefixWord ++ tailWord_3040737) baseStart_3040737 baseEnd_3040737 := by
    simpa [prefixWord, tailWord_3040737, baseEnd_3040737] using wordTrace_append hprefix tailTrace_3040737
  have hstable : (prefixWord ++ tailWord_3040737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040737).length < 2 ^ (prefixWord ++ tailWord_3040737).sum := by decide
  have hdescent : baseEnd_3040737 < baseStart_3040737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040801 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 1, 4]
def baseStart_3040801 : Nat := 118140960795 + 3040801 * 2 ^ 59
def prefixEnd_3040801 : Nat := 4983230072969 + 3 ^ 40 * 3040801 * 2
def baseEnd_3040801 : Nat := 520464162557487528601039

theorem tailTrace_3040801 : CollatzResearch.WordTrace tailWord_3040801 prefixEnd_3040801 520464162557487528601039 := by
  unfold tailWord_3040801
  simp only [CollatzResearch.WordTrace]
  refine ⟨110907123856704779310138257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73938082571136519540092171 110907123856704779310138257)
  ·
    refine ⟨83180342892528584482603693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110907123856704779310138257 83180342892528584482603693)
    ·
      refine ⟨31192628584698219180976385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83180342892528584482603693 31192628584698219180976385)
      ·
        refine ⟨23394471438523664385732289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31192628584698219180976385 23394471438523664385732289)
        ·
          refine ⟨17545853578892748289299217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23394471438523664385732289 17545853578892748289299217)
          ·
            refine ⟨13159390184169561216974413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17545853578892748289299217 13159390184169561216974413)
            ·
              refine ⟨4934771319063585456365405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13159390184169561216974413 4934771319063585456365405)
              ·
                refine ⟨1850539244648844546137027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4934771319063585456365405 1850539244648844546137027)
                ·
                  refine ⟨2775808866973266819205541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850539244648844546137027 2775808866973266819205541)
                  ·
                    refine ⟨520464162557487528601039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775808866973266819205541 520464162557487528601039)
                    ·
                      rfl

theorem cell23_3040801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_3040801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040801 prefixEnd_3040801 := by exact prefixLift 3040801
  have htrace : WordTrace (prefixWord ++ tailWord_3040801) baseStart_3040801 baseEnd_3040801 := by
    simpa [prefixWord, tailWord_3040801, baseEnd_3040801] using wordTrace_append hprefix tailTrace_3040801
  have hstable : (prefixWord ++ tailWord_3040801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040801).length < 2 ^ (prefixWord ++ tailWord_3040801).sum := by decide
  have hdescent : baseEnd_3040801 < baseStart_3040801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040844 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_3040844 : Nat := 118140960795 + 3040844 * 2 ^ 59
def prefixEnd_3040844 : Nat := 4983230072969 + 3 ^ 40 * 3040844 * 2
def baseEnd_3040844 : Nat := 520471522446868639188473

theorem tailTrace_3040844 : CollatzResearch.WordTrace tailWord_3040844 prefixEnd_3040844 520471522446868639188473 := by
  unfold tailWord_3040844
  simp only [CollatzResearch.WordTrace]
  refine ⟨55454346097774498826976793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73939128130365998435969057 55454346097774498826976793)
  ·
    refine ⟨41590759573330874120232595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55454346097774498826976793 41590759573330874120232595)
    ·
      refine ⟨62386139359996311180348893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41590759573330874120232595 62386139359996311180348893)
      ·
        refine ⟨23394802259998616692630835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62386139359996311180348893 23394802259998616692630835)
        ·
          refine ⟨35092203389997925038946253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23394802259998616692630835 35092203389997925038946253)
          ·
            refine ⟨13159576271249221889604845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35092203389997925038946253 13159576271249221889604845)
            ·
              refine ⟨4934841101718458208601817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13159576271249221889604845 4934841101718458208601817)
              ·
                refine ⟨3701130826288843656451363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934841101718458208601817 3701130826288843656451363)
                ·
                  refine ⟨5551696239433265484677045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701130826288843656451363 5551696239433265484677045)
                  ·
                    refine ⟨520471522446868639188473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5551696239433265484677045 520471522446868639188473)
                    ·
                      rfl

theorem cell23_3040844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_3040844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040844 prefixEnd_3040844 := by exact prefixLift 3040844
  have htrace : WordTrace (prefixWord ++ tailWord_3040844) baseStart_3040844 baseEnd_3040844 := by
    simpa [prefixWord, tailWord_3040844, baseEnd_3040844] using wordTrace_append hprefix tailTrace_3040844
  have hstable : (prefixWord ++ tailWord_3040844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040844).length < 2 ^ (prefixWord ++ tailWord_3040844).sum := by decide
  have hdescent : baseEnd_3040844 < baseStart_3040844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040857 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_3040857 : Nat := 118140960795 + 3040857 * 2 ^ 59
def prefixEnd_3040857 : Nat := 4983230072969 + 3 ^ 40 * 3040857 * 2
def baseEnd_3040857 : Nat := 520473747529704788900953

theorem tailTrace_3040857 : CollatzResearch.WordTrace tailWord_3040857 prefixEnd_3040857 520473747529704788900953 := by
  unfold tailWord_3040857
  simp only [CollatzResearch.WordTrace]
  refine ⟨110909166344501900874176825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73939444229667933916117883 110909166344501900874176825)
  ·
    refine ⟨83181874758376425655632619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110909166344501900874176825 83181874758376425655632619)
    ·
      refine ⟨124772812137564638483448929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83181874758376425655632619 124772812137564638483448929)
      ·
        refine ⟨93579609103173478862586697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124772812137564638483448929 93579609103173478862586697)
        ·
          refine ⟨70184706827380109146940023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93579609103173478862586697 70184706827380109146940023)
          ·
            refine ⟨105277060241070163720410035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70184706827380109146940023 105277060241070163720410035)
            ·
              refine ⟨157915590361605245580615053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105277060241070163720410035 157915590361605245580615053)
              ·
                refine ⟨59218346385601967092730645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157915590361605245580615053 59218346385601967092730645)
                ·
                  refine ⟨2775859986825092207471749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59218346385601967092730645 2775859986825092207471749)
                  ·
                    refine ⟨520473747529704788900953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775859986825092207471749 520473747529704788900953)
                    ·
                      rfl

theorem cell23_3040857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_3040857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040857 prefixEnd_3040857 := by exact prefixLift 3040857
  have htrace : WordTrace (prefixWord ++ tailWord_3040857) baseStart_3040857 baseEnd_3040857 := by
    simpa [prefixWord, tailWord_3040857, baseEnd_3040857] using wordTrace_append hprefix tailTrace_3040857
  have hstable : (prefixWord ++ tailWord_3040857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040857).length < 2 ^ (prefixWord ++ tailWord_3040857).sum := by decide
  have hdescent : baseEnd_3040857 < baseStart_3040857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040947 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 2, 6]
def baseStart_3040947 : Nat := 118140960795 + 3040947 * 2 ^ 59
def prefixEnd_3040947 : Nat := 4983230072969 + 3 ^ 40 * 3040947 * 2
def baseEnd_3040947 : Nat := 520489151949339671525815

theorem tailTrace_3040947 : CollatzResearch.WordTrace tailWord_3040947 prefixEnd_3040947 520489151949339671525815 := by
  unfold tailWord_3040947
  simp only [CollatzResearch.WordTrace]
  refine ⟨110912448914175846244953095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73941632609450564163302063 110912448914175846244953095)
  ·
    refine ⟨166368673371263769367429643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110912448914175846244953095 166368673371263769367429643)
    ·
      refine ⟨249553010056895654051144465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166368673371263769367429643 249553010056895654051144465)
      ·
        refine ⟨187164757542671740538358349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249553010056895654051144465 187164757542671740538358349)
        ·
          refine ⟨70186784078501902701884381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187164757542671740538358349 70186784078501902701884381)
          ·
            refine ⟨26320044029438213513206643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70186784078501902701884381 26320044029438213513206643)
            ·
              refine ⟨39480066044157320269809965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26320044029438213513206643 39480066044157320269809965)
              ·
                refine ⟨14805024766558995101178737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39480066044157320269809965 14805024766558995101178737)
                ·
                  refine ⟨11103768574919246325884053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14805024766558995101178737 11103768574919246325884053)
                  ·
                    refine ⟨520489151949339671525815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11103768574919246325884053 520489151949339671525815)
                    ·
                      rfl

theorem cell23_3040947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_3040947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040947 prefixEnd_3040947 := by exact prefixLift 3040947
  have htrace : WordTrace (prefixWord ++ tailWord_3040947) baseStart_3040947 baseEnd_3040947 := by
    simpa [prefixWord, tailWord_3040947, baseEnd_3040947] using wordTrace_append hprefix tailTrace_3040947
  have hstable : (prefixWord ++ tailWord_3040947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040947).length < 2 ^ (prefixWord ++ tailWord_3040947).sum := by decide
  have hdescent : baseEnd_3040947 < baseStart_3040947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040958 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_3040958 : Nat := 118140960795 + 3040958 * 2 ^ 59
def prefixEnd_3040958 : Nat := 4983230072969 + 3 ^ 40 * 3040958 * 2
def baseEnd_3040958 : Nat := 1561473104135218471539895

theorem tailTrace_3040958 : CollatzResearch.WordTrace tailWord_3040958 prefixEnd_3040958 1561473104135218471539895 := by
  unfold tailWord_3040958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864106264641999390450441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73941900078090663415735685 13864106264641999390450441)
  ·
    refine ⟨10398079698481499542837831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13864106264641999390450441 10398079698481499542837831)
    ·
      refine ⟨15597119547722249314256747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398079698481499542837831 15597119547722249314256747)
      ·
        refine ⟨23395679321583373971385121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15597119547722249314256747 23395679321583373971385121)
        ·
          refine ⟨17546759491187530478538841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23395679321583373971385121 17546759491187530478538841)
          ·
            refine ⟨13160069618390647858904131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17546759491187530478538841 13160069618390647858904131)
            ·
              refine ⟨19740104427585971788356197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160069618390647858904131 19740104427585971788356197)
              ·
                refine ⟨3701269580172369710316787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19740104427585971788356197 3701269580172369710316787)
                ·
                  refine ⟨5551904370258554565475181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701269580172369710316787 5551904370258554565475181)
                  ·
                    refine ⟨2081964138846957962053193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5551904370258554565475181 2081964138846957962053193)
                    ·
                      refine ⟨1561473104135218471539895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081964138846957962053193 1561473104135218471539895)
                      ·
                        rfl

theorem cell23_3040958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_3040958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040958 prefixEnd_3040958 := by exact prefixLift 3040958
  have htrace : WordTrace (prefixWord ++ tailWord_3040958) baseStart_3040958 baseEnd_3040958 := by
    simpa [prefixWord, tailWord_3040958, baseEnd_3040958] using wordTrace_append hprefix tailTrace_3040958
  have hstable : (prefixWord ++ tailWord_3040958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040958).length < 2 ^ (prefixWord ++ tailWord_3040958).sum := by decide
  have hdescent : baseEnd_3040958 < baseStart_3040958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040966 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3040966 : Nat := 118140960795 + 3040966 * 2 ^ 59
def prefixEnd_3040966 : Nat := 4983230072969 + 3 ^ 40 * 3040966 * 2
def baseEnd_3040966 : Nat := 1561477211980454440239859

theorem tailTrace_3040966 : CollatzResearch.WordTrace tailWord_3040966 prefixEnd_3040966 1561477211980454440239859 := by
  unfold tailWord_3040966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466035684409594140309211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73942094600738008326596501 3466035684409594140309211)
  ·
    refine ⟨5199053526614391210463817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3466035684409594140309211 5199053526614391210463817)
    ·
      refine ⟨3899290144960793407847863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5199053526614391210463817 3899290144960793407847863)
      ·
        refine ⟨5848935217441190111771795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899290144960793407847863 5848935217441190111771795)
        ·
          refine ⟨8773402826161785167657693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848935217441190111771795 8773402826161785167657693)
          ·
            refine ⟨3290026059810669437871635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8773402826161785167657693 3290026059810669437871635)
            ·
              refine ⟨4935039089716004156807453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290026059810669437871635 4935039089716004156807453)
              ·
                refine ⟨1850639658643501558802795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4935039089716004156807453 1850639658643501558802795)
                ·
                  refine ⟨2775959487965252338204193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850639658643501558802795 2775959487965252338204193)
                  ·
                    refine ⟨2081969615973939253653145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775959487965252338204193 2081969615973939253653145)
                    ·
                      refine ⟨1561477211980454440239859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081969615973939253653145 1561477211980454440239859)
                      ·
                        rfl

theorem cell23_3040966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3040966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040966 prefixEnd_3040966 := by exact prefixLift 3040966
  have htrace : WordTrace (prefixWord ++ tailWord_3040966) baseStart_3040966 baseEnd_3040966 := by
    simpa [prefixWord, tailWord_3040966, baseEnd_3040966] using wordTrace_append hprefix tailTrace_3040966
  have hstable : (prefixWord ++ tailWord_3040966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040966).length < 2 ^ (prefixWord ++ tailWord_3040966).sum := by decide
  have hdescent : baseEnd_3040966 < baseStart_3040966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040974 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3040974 : Nat := 118140960795 + 3040974 * 2 ^ 59
def prefixEnd_3040974 : Nat := 4983230072969 + 3 ^ 40 * 3040974 * 2
def baseEnd_3040974 : Nat := 1561481319825690408939821

theorem tailTrace_3040974 : CollatzResearch.WordTrace tailWord_3040974 prefixEnd_3040974 1561481319825690408939821 := by
  unfold tailWord_3040974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864179210634753732023247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73942289123385353237457317 13864179210634753732023247)
  ·
    refine ⟨20796268815952130598034871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13864179210634753732023247 20796268815952130598034871)
    ·
      refine ⟨31194403223928195897052307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20796268815952130598034871 31194403223928195897052307)
      ·
        refine ⟨46791604835892293845578461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31194403223928195897052307 46791604835892293845578461)
        ·
          refine ⟨17546851813459610192091923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46791604835892293845578461 17546851813459610192091923)
          ·
            refine ⟨26320277720189415288137885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17546851813459610192091923 26320277720189415288137885)
            ·
              refine ⟨9870104145071030733051707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26320277720189415288137885 9870104145071030733051707)
              ·
                refine ⟨14805156217606546099577561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870104145071030733051707 14805156217606546099577561)
                ·
                  refine ⟨11103867163204909574683171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14805156217606546099577561 11103867163204909574683171)
                  ·
                    refine ⟨16655800744807364362024757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11103867163204909574683171 16655800744807364362024757)
                    ·
                      refine ⟨1561481319825690408939821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16655800744807364362024757 1561481319825690408939821)
                      ·
                        rfl

theorem cell23_3040974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3040974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040974 prefixEnd_3040974 := by exact prefixLift 3040974
  have htrace : WordTrace (prefixWord ++ tailWord_3040974) baseStart_3040974 baseEnd_3040974 := by
    simpa [prefixWord, tailWord_3040974, baseEnd_3040974] using wordTrace_append hprefix tailTrace_3040974
  have hstable : (prefixWord ++ tailWord_3040974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040974).length < 2 ^ (prefixWord ++ tailWord_3040974).sum := by decide
  have hdescent : baseEnd_3040974 < baseStart_3040974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040999 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3040999 : Nat := 118140960795 + 3040999 * 2 ^ 59
def prefixEnd_3040999 : Nat := 4983230072969 + 3 ^ 40 * 3040999 * 2
def baseEnd_3040999 : Nat := 1561494156842052811127207

theorem tailTrace_3040999 : CollatzResearch.WordTrace tailWord_3040999 prefixEnd_3040999 1561494156842052811127207 := by
  unfold tailWord_3040999
  simp only [CollatzResearch.WordTrace]
  refine ⟨110914345509987459125846051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73942897006658306083897367 110914345509987459125846051)
  ·
    refine ⟨166371518264981188688769077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110914345509987459125846051 166371518264981188688769077)
    ·
      refine ⟨15597329837341986439572101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166371518264981188688769077 15597329837341986439572101)
      ·
        refine ⟨2924499344501622457419769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15597329837341986439572101 2924499344501622457419769)
        ·
          refine ⟨2193374508376216843064827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924499344501622457419769 2193374508376216843064827)
          ·
            refine ⟨3290061762564325264597241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193374508376216843064827 3290061762564325264597241)
            ·
              refine ⟨2467546321923243948447931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290061762564325264597241 2467546321923243948447931)
              ·
                refine ⟨3701319482884865922671897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467546321923243948447931 3701319482884865922671897)
                ·
                  refine ⟨2775989612163649442003923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701319482884865922671897 2775989612163649442003923)
                  ·
                    refine ⟨4163984418245474163005885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2775989612163649442003923 4163984418245474163005885)
                    ·
                      refine ⟨1561494156842052811127207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4163984418245474163005885 1561494156842052811127207)
                      ·
                        rfl

theorem cell23_3040999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3040999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3040999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3040999 prefixEnd_3040999 := by exact prefixLift 3040999
  have htrace : WordTrace (prefixWord ++ tailWord_3040999) baseStart_3040999 baseEnd_3040999 := by
    simpa [prefixWord, tailWord_3040999, baseEnd_3040999] using wordTrace_append hprefix tailTrace_3040999
  have hstable : (prefixWord ++ tailWord_3040999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040999).length < 2 ^ (prefixWord ++ tailWord_3040999).sum := by decide
  have hdescent : baseEnd_3040999 < baseStart_3040999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041004 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_3041004 : Nat := 118140960795 + 3041004 * 2 ^ 59
def prefixEnd_3041004 : Nat := 4983230072969 + 3 ^ 40 * 3041004 * 2
def baseEnd_3041004 : Nat := 1561496724245325291564683

theorem tailTrace_3041004 : CollatzResearch.WordTrace tailWord_3041004 prefixEnd_3041004 1561496724245325291564683 := by
  unfold tailWord_3041004
  simp only [CollatzResearch.WordTrace]
  refine ⟨55457263937484672489889033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73943018583312896653185377 55457263937484672489889033)
  ·
    refine ⟨41592947953113504367416775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55457263937484672489889033 41592947953113504367416775)
    ·
      refine ⟨62389421929670256551125163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41592947953113504367416775 62389421929670256551125163)
      ·
        refine ⟨93584132894505384826687745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62389421929670256551125163 93584132894505384826687745)
        ·
          refine ⟨70188099670879038620015809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93584132894505384826687745 70188099670879038620015809)
          ·
            refine ⟨52641074753159278965011857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70188099670879038620015809 52641074753159278965011857)
            ·
              refine ⟨39480806064869459223758893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52641074753159278965011857 39480806064869459223758893)
              ·
                refine ⟨14805302274326047208909585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39480806064869459223758893 14805302274326047208909585)
                ·
                  refine ⟨11103976705744535406682189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14805302274326047208909585 11103976705744535406682189)
                  ·
                    refine ⟨4163991264654200777505821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11103976705744535406682189 4163991264654200777505821)
                    ·
                      refine ⟨1561496724245325291564683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4163991264654200777505821 1561496724245325291564683)
                      ·
                        rfl

theorem cell23_3041004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_3041004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041004 prefixEnd_3041004 := by exact prefixLift 3041004
  have htrace : WordTrace (prefixWord ++ tailWord_3041004) baseStart_3041004 baseEnd_3041004 := by
    simpa [prefixWord, tailWord_3041004, baseEnd_3041004] using wordTrace_append hprefix tailTrace_3041004
  have hstable : (prefixWord ++ tailWord_3041004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041004).length < 2 ^ (prefixWord ++ tailWord_3041004).sum := by decide
  have hdescent : baseEnd_3041004 < baseStart_3041004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041005 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3041005 : Nat := 118140960795 + 3041005 * 2 ^ 59
def prefixEnd_3041005 : Nat := 4983230072969 + 3 ^ 40 * 3041005 * 2
def baseEnd_3041005 : Nat := 1561497237725979787652179

theorem tailTrace_3041005 : CollatzResearch.WordTrace tailWord_3041005 prefixEnd_3041005 1561497237725979787652179 := by
  unfold tailWord_3041005
  simp only [CollatzResearch.WordTrace]
  refine ⟨110914564347965722150564469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73943042898643814767042979 110914564347965722150564469)
  ·
    refine ⟨10398240407621786451615419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110914564347965722150564469 10398240407621786451615419)
    ·
      refine ⟨15597360611432679677423129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398240407621786451615419 15597360611432679677423129)
      ·
        refine ⟨11698020458574509758067347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15597360611432679677423129 11698020458574509758067347)
        ·
          refine ⟨17547030687861764637101021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698020458574509758067347 17547030687861764637101021)
          ·
            refine ⟨6580136507948161738912883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17547030687861764637101021 6580136507948161738912883)
            ·
              refine ⟨9870204761922242608369325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580136507948161738912883 9870204761922242608369325)
              ·
                refine ⟨3701326785720840978138497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9870204761922242608369325 3701326785720840978138497)
                ·
                  refine ⟨2775995089290630733603873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701326785720840978138497 2775995089290630733603873)
                  ·
                    refine ⟨2081996316967973050202905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775995089290630733603873 2081996316967973050202905)
                    ·
                      refine ⟨1561497237725979787652179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2081996316967973050202905 1561497237725979787652179)
                      ·
                        rfl

theorem cell23_3041005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3041005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041005 prefixEnd_3041005 := by exact prefixLift 3041005
  have htrace : WordTrace (prefixWord ++ tailWord_3041005) baseStart_3041005 baseEnd_3041005 := by
    simpa [prefixWord, tailWord_3041005, baseEnd_3041005] using wordTrace_append hprefix tailTrace_3041005
  have hstable : (prefixWord ++ tailWord_3041005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041005).length < 2 ^ (prefixWord ++ tailWord_3041005).sum := by decide
  have hdescent : baseEnd_3041005 < baseStart_3041005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041034 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3041034 : Nat := 118140960795 + 3041034 * 2 ^ 59
def prefixEnd_3041034 : Nat := 4983230072969 + 3 ^ 40 * 3041034 * 2
def baseEnd_3041034 : Nat := 1561512128664960174189545

theorem tailTrace_3041034 : CollatzResearch.WordTrace tailWord_3041034 prefixEnd_3041034 1561512128664960174189545 := by
  unfold tailWord_3041034
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728905516215165025842539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73943748043240440068913437 27728905516215165025842539)
  ·
    refine ⟨41593358274322747538763809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27728905516215165025842539 41593358274322747538763809)
    ·
      refine ⟨31195018705742060654072857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41593358274322747538763809 31195018705742060654072857)
      ·
        refine ⟨23396264029306545490554643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31195018705742060654072857 23396264029306545490554643)
        ·
          refine ⟨35094396043959818235831965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23396264029306545490554643 35094396043959818235831965)
          ·
            refine ⟨13160398516484931838436987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35094396043959818235831965 13160398516484931838436987)
            ·
              refine ⟨19740597774727397757655481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160398516484931838436987 19740597774727397757655481)
              ·
                refine ⟨14805448331045548318241611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19740597774727397757655481 14805448331045548318241611)
                ·
                  refine ⟨22208172496568322477362417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14805448331045548318241611 22208172496568322477362417)
                  ·
                    refine ⟨16656129372426241858021813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22208172496568322477362417 16656129372426241858021813)
                    ·
                      refine ⟨1561512128664960174189545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16656129372426241858021813 1561512128664960174189545)
                      ·
                        rfl

theorem cell23_3041034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3041034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041034 prefixEnd_3041034 := by exact prefixLift 3041034
  have htrace : WordTrace (prefixWord ++ tailWord_3041034) baseStart_3041034 baseEnd_3041034 := by
    simpa [prefixWord, tailWord_3041034, baseEnd_3041034] using wordTrace_append hprefix tailTrace_3041034
  have hstable : (prefixWord ++ tailWord_3041034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041034).length < 2 ^ (prefixWord ++ tailWord_3041034).sum := by decide
  have hdescent : baseEnd_3041034 < baseStart_3041034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041061 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_3041061 : Nat := 118140960795 + 3041061 * 2 ^ 59
def prefixEnd_3041061 : Nat := 4983230072969 + 3 ^ 40 * 3041061 * 2
def baseEnd_3041061 : Nat := 1561525992642631568551921

theorem tailTrace_3041061 : CollatzResearch.WordTrace tailWord_3041061 prefixEnd_3041061 1561525992642631568551921 := by
  unfold tailWord_3041061
  simp only [CollatzResearch.WordTrace]
  refine ⟨110916606835762843714603037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73944404557175229143068691 110916606835762843714603037)
  ·
    refine ⟨41593727563411066392976139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110916606835762843714603037 41593727563411066392976139)
    ·
      refine ⟨62390591345116599589464209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41593727563411066392976139 62390591345116599589464209)
      ·
        refine ⟨46792943508837449692098157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62390591345116599589464209 46792943508837449692098157)
        ·
          refine ⟨17547353815814043634536809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46792943508837449692098157 17547353815814043634536809)
          ·
            refine ⟨13160515361860532725902607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17547353815814043634536809 13160515361860532725902607)
            ·
              refine ⟨19740773042790799088853911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160515361860532725902607 19740773042790799088853911)
              ·
                refine ⟨29611159564186198633280867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19740773042790799088853911 29611159564186198633280867)
                ·
                  refine ⟨44416739346279297949921301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29611159564186198633280867 44416739346279297949921301)
                  ·
                    refine ⟨2082034656856842091402561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44416739346279297949921301 2082034656856842091402561)
                    ·
                      refine ⟨1561525992642631568551921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082034656856842091402561 1561525992642631568551921)
                      ·
                        rfl

theorem cell23_3041061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_3041061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041061 prefixEnd_3041061 := by exact prefixLift 3041061
  have htrace : WordTrace (prefixWord ++ tailWord_3041061) baseStart_3041061 baseEnd_3041061 := by
    simpa [prefixWord, tailWord_3041061, baseEnd_3041061] using wordTrace_append hprefix tailTrace_3041061
  have hstable : (prefixWord ++ tailWord_3041061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041061).length < 2 ^ (prefixWord ++ tailWord_3041061).sum := by decide
  have hdescent : baseEnd_3041061 < baseStart_3041061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041078 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3041078 : Nat := 118140960795 + 3041078 * 2 ^ 59
def prefixEnd_3041078 : Nat := 4983230072969 + 3 ^ 40 * 3041078 * 2
def baseEnd_3041078 : Nat := 1561534721813758002039343

theorem tailTrace_3041078 : CollatzResearch.WordTrace tailWord_3041078 prefixEnd_3041078 1561534721813758002039343 := by
  unfold tailWord_3041078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932326679793828476123243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73944817917800837078647925 6932326679793828476123243)
  ·
    refine ⟨10398490019690742714184865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6932326679793828476123243 10398490019690742714184865)
    ·
      refine ⟨7798867514768057035638649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10398490019690742714184865 7798867514768057035638649)
      ·
        refine ⟨5849150636076042776728987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7798867514768057035638649 5849150636076042776728987)
        ·
          refine ⟨8773725954114064165093481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849150636076042776728987 8773725954114064165093481)
          ·
            refine ⟨6580294465585548123820111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8773725954114064165093481 6580294465585548123820111)
            ·
              refine ⟨9870441698378322185730167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580294465585548123820111 9870441698378322185730167)
              ·
                refine ⟨14805662547567483278595251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870441698378322185730167 14805662547567483278595251)
                ·
                  refine ⟨22208493821351224917892877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14805662547567483278595251 22208493821351224917892877)
                  ·
                    refine ⟨8328185183006709344209829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22208493821351224917892877 8328185183006709344209829)
                    ·
                      refine ⟨1561534721813758002039343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8328185183006709344209829 1561534721813758002039343)
                      ·
                        rfl

theorem cell23_3041078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3041078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041078 prefixEnd_3041078 := by exact prefixLift 3041078
  have htrace : WordTrace (prefixWord ++ tailWord_3041078) baseStart_3041078 baseEnd_3041078 := by
    simpa [prefixWord, tailWord_3041078, baseEnd_3041078] using wordTrace_append hprefix tailTrace_3041078
  have hstable : (prefixWord ++ tailWord_3041078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041078).length < 2 ^ (prefixWord ++ tailWord_3041078).sum := by decide
  have hdescent : baseEnd_3041078 < baseStart_3041078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041121 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_3041121 : Nat := 118140960795 + 3041121 * 2 ^ 59
def prefixEnd_3041121 : Nat := 4983230072969 + 3 ^ 40 * 3041121 * 2
def baseEnd_3041121 : Nat := 1561556801481901333801645

theorem tailTrace_3041121 : CollatzResearch.WordTrace tailWord_3041121 prefixEnd_3041121 1561556801481901333801645 := by
  unfold tailWord_3041121
  simp only [CollatzResearch.WordTrace]
  refine ⟨110918795215545473961787217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73945863477030315974524811 110918795215545473961787217)
  ·
    refine ⟨83189096411659105471340413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110918795215545473961787217 83189096411659105471340413)
    ·
      refine ⟨31195911154372164551752655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83189096411659105471340413 31195911154372164551752655)
      ·
        refine ⟨46793866731558246827628983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31195911154372164551752655 46793866731558246827628983)
        ·
          refine ⟨70190800097337370241443475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46793866731558246827628983 70190800097337370241443475)
          ·
            refine ⟨105286200146006055362165213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70190800097337370241443475 105286200146006055362165213)
            ·
              refine ⟨39482325054752270760811955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105286200146006055362165213 39482325054752270760811955)
              ·
                refine ⟨59223487582128406141217933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39482325054752270760811955 59223487582128406141217933)
                ·
                  refine ⟨22208807843298152302956725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59223487582128406141217933 22208807843298152302956725)
                  ·
                    refine ⟨2082075735309201778402193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22208807843298152302956725 2082075735309201778402193)
                    ·
                      refine ⟨1561556801481901333801645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082075735309201778402193 1561556801481901333801645)
                      ·
                        rfl

theorem cell23_3041121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_3041121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041121 prefixEnd_3041121 := by exact prefixLift 3041121
  have htrace : WordTrace (prefixWord ++ tailWord_3041121) baseStart_3041121 baseEnd_3041121 := by
    simpa [prefixWord, tailWord_3041121, baseEnd_3041121] using wordTrace_append hprefix tailTrace_3041121
  have hstable : (prefixWord ++ tailWord_3041121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041121).length < 2 ^ (prefixWord ++ tailWord_3041121).sum := by decide
  have hdescent : baseEnd_3041121 < baseStart_3041121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041128 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3041128 : Nat := 118140960795 + 3041128 * 2 ^ 59
def prefixEnd_3041128 : Nat := 4983230072969 + 3 ^ 40 * 3041128 * 2
def baseEnd_3041128 : Nat := 1561560395846482806414113

theorem tailTrace_3041128 : CollatzResearch.WordTrace tailWord_3041128 prefixEnd_3041128 1561560395846482806414113 := by
  unfold tailWord_3041128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55459525263260057078646019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73946033684346742771528025 55459525263260057078646019)
  ·
    refine ⟨83189287894890085617969029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55459525263260057078646019 83189287894890085617969029)
    ·
      refine ⟨15597991480291891053369193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83189287894890085617969029 15597991480291891053369193)
      ·
        refine ⟨11698493610218918290026895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15597991480291891053369193 11698493610218918290026895)
        ·
          refine ⟨17547740415328377435040343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698493610218918290026895 17547740415328377435040343)
          ·
            refine ⟨26321610622992566152560515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17547740415328377435040343 26321610622992566152560515)
            ·
              refine ⟨39482415934488849228840773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26321610622992566152560515 39482415934488849228840773)
              ·
                refine ⟨7402952987716659230407645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39482415934488849228840773 7402952987716659230407645)
                ·
                  refine ⟨2776107370393747211402867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7402952987716659230407645 2776107370393747211402867)
                  ·
                    refine ⟨4164161055590620817104301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2776107370393747211402867 4164161055590620817104301)
                    ·
                      refine ⟨1561560395846482806414113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4164161055590620817104301 1561560395846482806414113)
                      ·
                        rfl

theorem cell23_3041128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3041128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041128 prefixEnd_3041128 := by exact prefixLift 3041128
  have htrace : WordTrace (prefixWord ++ tailWord_3041128) baseStart_3041128 baseEnd_3041128 := by
    simpa [prefixWord, tailWord_3041128, baseEnd_3041128] using wordTrace_append hprefix tailTrace_3041128
  have hstable : (prefixWord ++ tailWord_3041128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041128).length < 2 ^ (prefixWord ++ tailWord_3041128).sum := by decide
  have hdescent : baseEnd_3041128 < baseStart_3041128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041138 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3041138 : Nat := 118140960795 + 3041138 * 2 ^ 59
def prefixEnd_3041138 : Nat := 4983230072969 + 3 ^ 40 * 3041138 * 2
def baseEnd_3041138 : Nat := 1561565530653027767289067

theorem tailTrace_3041138 : CollatzResearch.WordTrace tailWord_3041138 prefixEnd_3041138 1561565530653027767289067 := by
  unfold tailWord_3041138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27729853814120971466289017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73946276837655923910104045 27729853814120971466289017)
  ·
    refine ⟨20797390360590728599716763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27729853814120971466289017 20797390360590728599716763)
    ·
      refine ⟨31196085540886092899575145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797390360590728599716763 31196085540886092899575145)
      ·
        refine ⟨23397064155664569674681359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31196085540886092899575145 23397064155664569674681359)
        ·
          refine ⟨35095596233496854512022039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23397064155664569674681359 35095596233496854512022039)
          ·
            refine ⟨52643394350245281768033059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35095596233496854512022039 52643394350245281768033059)
            ·
              refine ⟨78965091525367922652049589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52643394350245281768033059 78965091525367922652049589)
              ·
                refine ⟨7402977330503242748629649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78965091525367922652049589 7402977330503242748629649)
                ·
                  refine ⟨5552232997877432061472237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7402977330503242748629649 5552232997877432061472237)
                  ·
                    refine ⟨2082087374204037023052089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5552232997877432061472237 2082087374204037023052089)
                    ·
                      refine ⟨1561565530653027767289067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082087374204037023052089 1561565530653027767289067)
                      ·
                        rfl

theorem cell23_3041138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3041138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041138 prefixEnd_3041138 := by exact prefixLift 3041138
  have htrace : WordTrace (prefixWord ++ tailWord_3041138) baseStart_3041138 baseEnd_3041138 := by
    simpa [prefixWord, tailWord_3041138, baseEnd_3041138] using wordTrace_append hprefix tailTrace_3041138
  have hstable : (prefixWord ++ tailWord_3041138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041138).length < 2 ^ (prefixWord ++ tailWord_3041138).sum := by decide
  have hdescent : baseEnd_3041138 < baseStart_3041138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041161 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_3041161 : Nat := 118140960795 + 3041161 * 2 ^ 59
def prefixEnd_3041161 : Nat := 4983230072969 + 3 ^ 40 * 3041161 * 2
def baseEnd_3041161 : Nat := 520525780236027059100487

theorem tailTrace_3041161 : CollatzResearch.WordTrace tailWord_3041161 prefixEnd_3041161 520525780236027059100487 := by
  unfold tailWord_3041161
  simp only [CollatzResearch.WordTrace]
  refine ⟨110920254135400560793243337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73946836090267040528828891 110920254135400560793243337)
  ·
    refine ⟨83190190601550420594932503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110920254135400560793243337 83190190601550420594932503)
    ·
      refine ⟨124785285902325630892398755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83190190601550420594932503 124785285902325630892398755)
      ·
        refine ⟨187177928853488446338598133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124785285902325630892398755 187177928853488446338598133)
        ·
          refine ⟨17547930830014541844243575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187177928853488446338598133 17547930830014541844243575)
          ·
            refine ⟨26321896245021812766365363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17547930830014541844243575 26321896245021812766365363)
            ·
              refine ⟨39482844367532719149548045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26321896245021812766365363 39482844367532719149548045)
              ·
                refine ⟨14806066637824769681080517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39482844367532719149548045 14806066637824769681080517)
                ·
                  refine ⟨2776137494592144315202597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14806066637824769681080517 2776137494592144315202597)
                  ·
                    refine ⟨520525780236027059100487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2776137494592144315202597 520525780236027059100487)
                    ·
                      rfl

theorem cell23_3041161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_3041161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041161 prefixEnd_3041161 := by exact prefixLift 3041161
  have htrace : WordTrace (prefixWord ++ tailWord_3041161) baseStart_3041161 baseEnd_3041161 := by
    simpa [prefixWord, tailWord_3041161, baseEnd_3041161] using wordTrace_append hprefix tailTrace_3041161
  have hstable : (prefixWord ++ tailWord_3041161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041161).length < 2 ^ (prefixWord ++ tailWord_3041161).sum := by decide
  have hdescent : baseEnd_3041161 < baseStart_3041161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041162 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3041162 : Nat := 118140960795 + 3041162 * 2 ^ 59
def prefixEnd_3041162 : Nat := 4983230072969 + 3 ^ 40 * 3041162 * 2
def baseEnd_3041162 : Nat := 1561577854188735673388957

theorem tailTrace_3041162 : CollatzResearch.WordTrace tailWord_3041162 prefixEnd_3041162 1561577854188735673388957 := by
  unfold tailWord_3041162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27730072652099234491007435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73946860405597958642686493 27730072652099234491007435)
  ·
    refine ⟨41595108978148851736511153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27730072652099234491007435 41595108978148851736511153)
    ·
      refine ⟨31196331733611638802383365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41595108978148851736511153 31196331733611638802383365)
      ·
        refine ⟨5849312200052182275446881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31196331733611638802383365 5849312200052182275446881)
        ·
          refine ⟨4386984150039136706585161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849312200052182275446881 4386984150039136706585161)
          ·
            refine ⟨3290238112529352529938871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386984150039136706585161 3290238112529352529938871)
            ·
              refine ⟨4935357168794028794908307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290238112529352529938871 4935357168794028794908307)
              ·
                refine ⟨7403035753191043192362461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935357168794028794908307 7403035753191043192362461)
                ·
                  refine ⟨2776138407446641197135923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7403035753191043192362461 2776138407446641197135923)
                  ·
                    refine ⟨4164207611169961795703885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2776138407446641197135923 4164207611169961795703885)
                    ·
                      refine ⟨1561577854188735673388957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4164207611169961795703885 1561577854188735673388957)
                      ·
                        rfl

theorem cell23_3041162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3041162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041162 prefixEnd_3041162 := by exact prefixLift 3041162
  have htrace : WordTrace (prefixWord ++ tailWord_3041162) baseStart_3041162 baseEnd_3041162 := by
    simpa [prefixWord, tailWord_3041162, baseEnd_3041162] using wordTrace_append hprefix tailTrace_3041162
  have hstable : (prefixWord ++ tailWord_3041162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041162).length < 2 ^ (prefixWord ++ tailWord_3041162).sum := by decide
  have hdescent : baseEnd_3041162 < baseStart_3041162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041181 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3041181 : Nat := 118140960795 + 3041181 * 2 ^ 59
def prefixEnd_3041181 : Nat := 4983230072969 + 3 ^ 40 * 3041181 * 2
def baseEnd_3041181 : Nat := 1561587610321171099051369

theorem tailTrace_3041181 : CollatzResearch.WordTrace tailWord_3041181 prefixEnd_3041181 1561587610321171099051369 := by
  unfold tailWord_3041181
  simp only [CollatzResearch.WordTrace]
  refine ⟨110920983595328104208971397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73947322396885402805980931 110920983595328104208971397)
  ·
    refine ⟨20797684424124019539182137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110920983595328104208971397 20797684424124019539182137)
    ·
      refine ⟨15598263318093014654386603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20797684424124019539182137 15598263318093014654386603)
      ·
        refine ⟨23397394977139521981579905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15598263318093014654386603 23397394977139521981579905)
        ·
          refine ⟨17548046232854641486184929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23397394977139521981579905 17548046232854641486184929)
          ·
            refine ⟨13161034674640981114638697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17548046232854641486184929 13161034674640981114638697)
            ·
              refine ⟨9870776005980735835979023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13161034674640981114638697 9870776005980735835979023)
              ·
                refine ⟨14806164008971103753968535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870776005980735835979023 14806164008971103753968535)
                ·
                  refine ⟨22209246013456655630952803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14806164008971103753968535 22209246013456655630952803)
                  ·
                    refine ⟨33313869020184983446429205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22209246013456655630952803 33313869020184983446429205)
                    ·
                      refine ⟨1561587610321171099051369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33313869020184983446429205 1561587610321171099051369)
                      ·
                        rfl

theorem cell23_3041181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3041181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041181 prefixEnd_3041181 := by exact prefixLift 3041181
  have htrace : WordTrace (prefixWord ++ tailWord_3041181) baseStart_3041181 baseEnd_3041181 := by
    simpa [prefixWord, tailWord_3041181, baseEnd_3041181] using wordTrace_append hprefix tailTrace_3041181
  have hstable : (prefixWord ++ tailWord_3041181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041181).length < 2 ^ (prefixWord ++ tailWord_3041181).sum := by decide
  have hdescent : baseEnd_3041181 < baseStart_3041181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041188 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_3041188 : Nat := 118140960795 + 3041188 * 2 ^ 59
def prefixEnd_3041188 : Nat := 4983230072969 + 3 ^ 40 * 3041188 * 2
def baseEnd_3041188 : Nat := 1561591204685752571663837

theorem tailTrace_3041188 : CollatzResearch.WordTrace tailWord_3041188 prefixEnd_3041188 1561591204685752571663837 := by
  unfold tailWord_3041188
  simp only [CollatzResearch.WordTrace]
  refine ⟨55460619453151372202238109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73947492604201829602984145 55460619453151372202238109)
  ·
    refine ⟨20797732294931764575839291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55460619453151372202238109 20797732294931764575839291)
    ·
      refine ⟨31196598442397646863758937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797732294931764575839291 31196598442397646863758937)
      ·
        refine ⟨23397448831798235147819203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31196598442397646863758937 23397448831798235147819203)
        ·
          refine ⟨35096173247697352721728805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23397448831798235147819203 35096173247697352721728805)
          ·
            refine ⟨6580532483943253635324151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35096173247697352721728805 6580532483943253635324151)
            ·
              refine ⟨9870798725914880452986227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580532483943253635324151 9870798725914880452986227)
              ·
                refine ⟨14806198088872320679479341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870798725914880452986227 14806198088872320679479341)
                ·
                  refine ⟨5552324283327120254804753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14806198088872320679479341 5552324283327120254804753)
                  ·
                    refine ⟨4164243212495340191103565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5552324283327120254804753 4164243212495340191103565)
                    ·
                      refine ⟨1561591204685752571663837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4164243212495340191103565 1561591204685752571663837)
                      ·
                        rfl

theorem cell23_3041188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_3041188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041188 prefixEnd_3041188 := by exact prefixLift 3041188
  have htrace : WordTrace (prefixWord ++ tailWord_3041188) baseStart_3041188 baseEnd_3041188 := by
    simpa [prefixWord, tailWord_3041188, baseEnd_3041188] using wordTrace_append hprefix tailTrace_3041188
  have hstable : (prefixWord ++ tailWord_3041188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041188).length < 2 ^ (prefixWord ++ tailWord_3041188).sum := by decide
  have hdescent : baseEnd_3041188 < baseStart_3041188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041191 : List Nat := [1, 1, 6, 1, 2, 1, 2, 9]
def baseStart_3041191 : Nat := 118140960795 + 3041191 * 2 ^ 59
def prefixEnd_3041191 : Nat := 4983230072969 + 3 ^ 40 * 3041191 * 2
def baseEnd_3041191 : Nat := 57836768338063557775049

theorem tailTrace_3041191 : CollatzResearch.WordTrace tailWord_3041191 prefixEnd_3041191 57836768338063557775049 := by
  unfold tailWord_3041191
  simp only [CollatzResearch.WordTrace]
  refine ⟨110921348325291875916835427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73947565550194583944556951 110921348325291875916835427)
  ·
    refine ⟨166382022487937813875253141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110921348325291875916835427 166382022487937813875253141)
    ·
      refine ⟨7799157304122085025402491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166382022487937813875253141 7799157304122085025402491)
      ·
        refine ⟨11698735956183127538103737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7799157304122085025402491 11698735956183127538103737)
        ·
          refine ⟨8774051967137345653577803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11698735956183127538103737 8774051967137345653577803)
          ·
            refine ⟨13161077950706018480366705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8774051967137345653577803 13161077950706018480366705)
            ·
              refine ⟨9870808463029513860275029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13161077950706018480366705 9870808463029513860275029)
              ·
                refine ⟨57836768338063557775049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9870808463029513860275029 57836768338063557775049)
                ·
                  rfl

theorem cell23_3041191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 9].length) (baseStart_3041191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041191 prefixEnd_3041191 := by exact prefixLift 3041191
  have htrace : WordTrace (prefixWord ++ tailWord_3041191) baseStart_3041191 baseEnd_3041191 := by
    simpa [prefixWord, tailWord_3041191, baseEnd_3041191] using wordTrace_append hprefix tailTrace_3041191
  have hstable : (prefixWord ++ tailWord_3041191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041191).length < 2 ^ (prefixWord ++ tailWord_3041191).sum := by decide
  have hdescent : baseEnd_3041191 < baseStart_3041191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041212 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_3041212 : Nat := 118140960795 + 3041212 * 2 ^ 59
def prefixEnd_3041212 : Nat := 4983230072969 + 3 ^ 40 * 3041212 * 2
def baseEnd_3041212 : Nat := 520534509407153492587909

theorem tailTrace_3041212 : CollatzResearch.WordTrace tailWord_3041212 prefixEnd_3041212 520534509407153492587909 := by
  unfold tailWord_3041212
  simp only [CollatzResearch.WordTrace]
  refine ⟨55461057129107898251674945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73948076172143864335566593 55461057129107898251674945)
  ·
    refine ⟨41595792846830923688756209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55461057129107898251674945 41595792846830923688756209)
    ·
      refine ⟨31196844635123192766567157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41595792846830923688756209 31196844635123192766567157)
      ·
        refine ⟨2924704184542799321865671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31196844635123192766567157 2924704184542799321865671)
        ·
          refine ⟨4387056276814198982798507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924704184542799321865671 4387056276814198982798507)
          ·
            refine ⟨6580584415221298474197761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387056276814198982798507 6580584415221298474197761)
            ·
              refine ⟨4935438311415973855648321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6580584415221298474197761 4935438311415973855648321)
              ·
                refine ⟨3701578733561980391736241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4935438311415973855648321 3701578733561980391736241)
                ·
                  refine ⟨2776184050171485293802181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701578733561980391736241 2776184050171485293802181)
                  ·
                    refine ⟨520534509407153492587909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2776184050171485293802181 520534509407153492587909)
                    ·
                      rfl

theorem cell23_3041212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_3041212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041212 prefixEnd_3041212 := by exact prefixLift 3041212
  have htrace : WordTrace (prefixWord ++ tailWord_3041212) baseStart_3041212 baseEnd_3041212 := by
    simpa [prefixWord, tailWord_3041212, baseEnd_3041212] using wordTrace_append hprefix tailTrace_3041212
  have hstable : (prefixWord ++ tailWord_3041212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041212).length < 2 ^ (prefixWord ++ tailWord_3041212).sum := by decide
  have hdescent : baseEnd_3041212 < baseStart_3041212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041262 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_3041262 : Nat := 118140960795 + 3041262 * 2 ^ 59
def prefixEnd_3041262 : Nat := 4983230072969 + 3 ^ 40 * 3041262 * 2
def baseEnd_3041262 : Nat := 1561629202254185282138497

theorem tailTrace_3041262 : CollatzResearch.WordTrace tailWord_3041262 prefixEnd_3041262 1561629202254185282138497 := by
  unfold tailWord_3041262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865492238504331880333755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73949291938689770028446693 13865492238504331880333755)
  ·
    refine ⟨20798238357756497820500633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13865492238504331880333755 20798238357756497820500633)
    ·
      refine ⟨15598678768317373365375475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20798238357756497820500633 15598678768317373365375475)
      ·
        refine ⟨23398018152476060048063213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15598678768317373365375475 23398018152476060048063213)
        ·
          refine ⟨8774256807178522518023705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23398018152476060048063213 8774256807178522518023705)
          ·
            refine ⟨6580692605383891888517779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8774256807178522518023705 6580692605383891888517779)
            ·
              refine ⟨9871038908075837832776669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580692605383891888517779 9871038908075837832776669)
              ·
                refine ⟨3701639590528439187291251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9871038908075837832776669 3701639590528439187291251)
                ·
                  refine ⟨5552459385792658780936877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701639590528439187291251 5552459385792658780936877)
                  ·
                    refine ⟨2082172269672247042851329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5552459385792658780936877 2082172269672247042851329)
                    ·
                      refine ⟨1561629202254185282138497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082172269672247042851329 1561629202254185282138497)
                      ·
                        rfl

theorem cell23_3041262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_3041262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041262 prefixEnd_3041262 := by exact prefixLift 3041262
  have htrace : WordTrace (prefixWord ++ tailWord_3041262) baseStart_3041262 baseEnd_3041262 := by
    simpa [prefixWord, tailWord_3041262, baseEnd_3041262] using wordTrace_append hprefix tailTrace_3041262
  have hstable : (prefixWord ++ tailWord_3041262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041262).length < 2 ^ (prefixWord ++ tailWord_3041262).sum := by decide
  have hdescent : baseEnd_3041262 < baseStart_3041262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041311 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 7]
def baseStart_3041311 : Nat := 118140960795 + 3041311 * 2 ^ 59
def prefixEnd_3041311 : Nat := 4983230072969 + 3 ^ 40 * 3041311 * 2
def baseEnd_3041311 : Nat := 520551454268751863475257

theorem tailTrace_3041311 : CollatzResearch.WordTrace tailWord_3041311 prefixEnd_3041311 520551454268751863475257 := by
  unfold tailWord_3041311
  simp only [CollatzResearch.WordTrace]
  refine ⟨110925725084857136411203787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73950483389904757607469191 110925725084857136411203787)
  ·
    refine ⟨166388587627285704616805681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110925725084857136411203787 166388587627285704616805681)
    ·
      refine ⟨124791440720464278462604261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166388587627285704616805681 124791440720464278462604261)
      ·
        refine ⟨23398395135087052211738299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124791440720464278462604261 23398395135087052211738299)
        ·
          refine ⟨35097592702630578317607449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23398395135087052211738299 35097592702630578317607449)
          ·
            refine ⟨26323194526972933738205587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35097592702630578317607449 26323194526972933738205587)
            ·
              refine ⟨39484791790459400607308381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26323194526972933738205587 39484791790459400607308381)
              ·
                refine ⟨14806796921422275227740643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39484791790459400607308381 14806796921422275227740643)
                ·
                  refine ⟨22210195382133412841610965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14806796921422275227740643 22210195382133412841610965)
                  ·
                    refine ⟨520551454268751863475257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22210195382133412841610965 520551454268751863475257)
                    ·
                      rfl

theorem cell23_3041311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_3041311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041311 prefixEnd_3041311 := by exact prefixLift 3041311
  have htrace : WordTrace (prefixWord ++ tailWord_3041311) baseStart_3041311 baseEnd_3041311 := by
    simpa [prefixWord, tailWord_3041311, baseEnd_3041311] using wordTrace_append hprefix tailTrace_3041311
  have hstable : (prefixWord ++ tailWord_3041311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041311).length < 2 ^ (prefixWord ++ tailWord_3041311).sum := by decide
  have hdescent : baseEnd_3041311 < baseStart_3041311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041328 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_3041328 : Nat := 118140960795 + 3041328 * 2 ^ 59
def prefixEnd_3041328 : Nat := 4983230072969 + 3 ^ 40 * 3041328 * 2
def baseEnd_3041328 : Nat := 520554363992460674637731

theorem tailTrace_3041328 : CollatzResearch.WordTrace tailWord_3041328 prefixEnd_3041328 520554363992460674637731 := by
  unfold tailWord_3041328
  simp only [CollatzResearch.WordTrace]
  refine ⟨55463172562897774157286319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73950896750530365543048425 55463172562897774157286319)
  ·
    refine ⟨83194758844346661235929479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55463172562897774157286319 83194758844346661235929479)
    ·
      refine ⟨124792138266519991853894219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83194758844346661235929479 124792138266519991853894219)
      ·
        refine ⟨187188207399779987780841329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124792138266519991853894219 187188207399779987780841329)
        ·
          refine ⟨140391155549834990835630997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187188207399779987780841329 140391155549834990835630997)
          ·
            refine ⟨6580835416398515195420203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140391155549834990835630997 6580835416398515195420203)
            ·
              refine ⟨9871253124597772793130305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580835416398515195420203 9871253124597772793130305)
              ·
                refine ⟨7403439843448329594847729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9871253124597772793130305 7403439843448329594847729)
                ·
                  refine ⟨5552579882586247196135797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7403439843448329594847729 5552579882586247196135797)
                  ·
                    refine ⟨520554363992460674637731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5552579882586247196135797 520554363992460674637731)
                    ·
                      rfl

theorem cell23_3041328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_3041328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041328 prefixEnd_3041328 := by exact prefixLift 3041328
  have htrace : WordTrace (prefixWord ++ tailWord_3041328) baseStart_3041328 baseEnd_3041328 := by
    simpa [prefixWord, tailWord_3041328, baseEnd_3041328] using wordTrace_append hprefix tailTrace_3041328
  have hstable : (prefixWord ++ tailWord_3041328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041328).length < 2 ^ (prefixWord ++ tailWord_3041328).sum := by decide
  have hdescent : baseEnd_3041328 < baseStart_3041328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041332 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3041332 : Nat := 118140960795 + 3041332 * 2 ^ 59
def prefixEnd_3041332 : Nat := 4983230072969 + 3 ^ 40 * 3041332 * 2
def baseEnd_3041332 : Nat := 173518349544444445362575

theorem tailTrace_3041332 : CollatzResearch.WordTrace tailWord_3041332 prefixEnd_3041332 173518349544444445362575 := by
  unfold tailWord_3041332
  simp only [CollatzResearch.WordTrace]
  refine ⟨55463245508890528498859125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73950994011854037998478833 55463245508890528498859125)
  ·
    refine ⟨5199679266458487046768043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55463245508890528498859125 5199679266458487046768043)
    ·
      refine ⟨7799518899687730570152065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5199679266458487046768043 7799518899687730570152065)
      ·
        refine ⟨5849639174765797927614049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7799518899687730570152065 5849639174765797927614049)
        ·
          refine ⟨4387229381074348445710537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849639174765797927614049 4387229381074348445710537)
          ·
            refine ⟨3290422035805761334282903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4387229381074348445710537 3290422035805761334282903)
            ·
              refine ⟨4935633053708642001424355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290422035805761334282903 4935633053708642001424355)
              ·
                refine ⟨7403449580562963002136533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935633053708642001424355 7403449580562963002136533)
                ·
                  refine ⟨173518349544444445362575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7403449580562963002136533 173518349544444445362575)
                  ·
                    rfl

theorem cell23_3041332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3041332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041332 prefixEnd_3041332 := by exact prefixLift 3041332
  have htrace : WordTrace (prefixWord ++ tailWord_3041332) baseStart_3041332 baseEnd_3041332 := by
    simpa [prefixWord, tailWord_3041332, baseEnd_3041332] using wordTrace_append hprefix tailTrace_3041332
  have hstable : (prefixWord ++ tailWord_3041332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041332).length < 2 ^ (prefixWord ++ tailWord_3041332).sum := by decide
  have hdescent : baseEnd_3041332 < baseStart_3041332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041361 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_3041361 : Nat := 118140960795 + 3041361 * 2 ^ 59
def prefixEnd_3041361 : Nat := 4983230072969 + 3 ^ 40 * 3041361 * 2
def baseEnd_3041361 : Nat := 1561680036838980394800541

theorem tailTrace_3041361 : CollatzResearch.WordTrace tailWord_3041361 prefixEnd_3041361 1561680036838980394800541 := by
  unfold tailWord_3041361
  simp only [CollatzResearch.WordTrace]
  refine ⟨110927548734675994950523937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73951699156450663300349291 110927548734675994950523937)
  ·
    refine ⟨83195661551006996212892953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110927548734675994950523937 83195661551006996212892953)
    ·
      refine ⟨62396746163255247159669715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83195661551006996212892953 62396746163255247159669715)
      ·
        refine ⟨93595119244882870739504573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62396746163255247159669715 93595119244882870739504573)
        ·
          refine ⟨35098169716831076527314215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93595119244882870739504573 35098169716831076527314215)
          ·
            refine ⟨52647254575246614790971323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35098169716831076527314215 52647254575246614790971323)
            ·
              refine ⟨78970881862869922186456985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52647254575246614790971323 78970881862869922186456985)
              ·
                refine ⟨59228161397152441639842739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78970881862869922186456985 59228161397152441639842739)
                ·
                  refine ⟨88842242095728662459764109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59228161397152441639842739 88842242095728662459764109)
                  ·
                    refine ⟨33315840785898248422411541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88842242095728662459764109 33315840785898248422411541)
                    ·
                      refine ⟨1561680036838980394800541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33315840785898248422411541 1561680036838980394800541)
                      ·
                        rfl

theorem cell23_3041361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_3041361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041361 prefixEnd_3041361 := by exact prefixLift 3041361
  have htrace : WordTrace (prefixWord ++ tailWord_3041361) baseStart_3041361 baseEnd_3041361 := by
    simpa [prefixWord, tailWord_3041361, baseEnd_3041361] using wordTrace_append hprefix tailTrace_3041361
  have hstable : (prefixWord ++ tailWord_3041361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041361).length < 2 ^ (prefixWord ++ tailWord_3041361).sum := by decide
  have hdescent : baseEnd_3041361 < baseStart_3041361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041365 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3041365 : Nat := 118140960795 + 3041365 * 2 ^ 59
def prefixEnd_3041365 : Nat := 4983230072969 + 3 ^ 40 * 3041365 * 2
def baseEnd_3041365 : Nat := 1561682090761598379150523

theorem tailTrace_3041365 : CollatzResearch.WordTrace tailWord_3041365 prefixEnd_3041365 1561682090761598379150523 := by
  unfold tailWord_3041365
  simp only [CollatzResearch.WordTrace]
  refine ⟨110927694626661503633669549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73951796417774335755779699 110927694626661503633669549)
  ·
    refine ⟨41597885484998063862626081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110927694626661503633669549 41597885484998063862626081)
    ·
      refine ⟨31198414113748547896969561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41597885484998063862626081 31198414113748547896969561)
      ·
        refine ⟨23398810585311410922727171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31198414113748547896969561 23398810585311410922727171)
        ·
          refine ⟨35098215877967116384090757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23398810585311410922727171 35098215877967116384090757)
          ·
            refine ⟨6580915477118834322017017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35098215877967116384090757 6580915477118834322017017)
            ·
              refine ⟨4935686607839125741512763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6580915477118834322017017 4935686607839125741512763)
              ·
                refine ⟨7403529911758688612269145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935686607839125741512763 7403529911758688612269145)
                ·
                  refine ⟨5552647433819016459201859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7403529911758688612269145 5552647433819016459201859)
                  ·
                    refine ⟨8328971150728524688802789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5552647433819016459201859 8328971150728524688802789)
                    ·
                      refine ⟨1561682090761598379150523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8328971150728524688802789 1561682090761598379150523)
                      ·
                        rfl

theorem cell23_3041365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3041365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041365 prefixEnd_3041365 := by exact prefixLift 3041365
  have htrace : WordTrace (prefixWord ++ tailWord_3041365) baseStart_3041365 baseEnd_3041365 := by
    simpa [prefixWord, tailWord_3041365, baseEnd_3041365] using wordTrace_append hprefix tailTrace_3041365
  have hstable : (prefixWord ++ tailWord_3041365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041365).length < 2 ^ (prefixWord ++ tailWord_3041365).sum := by decide
  have hdescent : baseEnd_3041365 < baseStart_3041365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041388 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 6]
def baseStart_3041388 : Nat := 118140960795 + 3041388 * 2 ^ 59
def prefixEnd_3041388 : Nat := 4983230072969 + 3 ^ 40 * 3041388 * 2
def baseEnd_3041388 : Nat := 173521544535183532129213

theorem tailTrace_3041388 : CollatzResearch.WordTrace tailWord_3041388 prefixEnd_3041388 173521544535183532129213 := by
  unfold tailWord_3041388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55464266752789089280878409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73952355670385452374504545 55464266752789089280878409)
  ·
    refine ⟨41598200064591816960658807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55464266752789089280878409 41598200064591816960658807)
    ·
      refine ⟨62397300096887725440988211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41598200064591816960658807 62397300096887725440988211)
      ·
        refine ⟨93595950145331588161482317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62397300096887725440988211 93595950145331588161482317)
        ·
          refine ⟨35098481304499345560555869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93595950145331588161482317 35098481304499345560555869)
          ·
            refine ⟨13161930489187254585208451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35098481304499345560555869 13161930489187254585208451)
            ·
              refine ⟨19742895733780881877812677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13161930489187254585208451 19742895733780881877812677)
              ·
                refine ⟨3701792950083915352089877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19742895733780881877812677 3701792950083915352089877)
                ·
                  refine ⟨173521544535183532129213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3701792950083915352089877 173521544535183532129213)
                  ·
                    rfl

theorem cell23_3041388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_3041388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041388 prefixEnd_3041388 := by exact prefixLift 3041388
  have htrace : WordTrace (prefixWord ++ tailWord_3041388) baseStart_3041388 baseEnd_3041388 := by
    simpa [prefixWord, tailWord_3041388, baseEnd_3041388] using wordTrace_append hprefix tailTrace_3041388
  have hstable : (prefixWord ++ tailWord_3041388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041388).length < 2 ^ (prefixWord ++ tailWord_3041388).sum := by decide
  have hdescent : baseEnd_3041388 < baseStart_3041388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041392 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 1, 4]
def baseStart_3041392 : Nat := 118140960795 + 3041392 * 2 ^ 59
def prefixEnd_3041392 : Nat := 4983230072969 + 3 ^ 40 * 3041392 * 2
def baseEnd_3041392 : Nat := 520565318246423257837633

theorem tailTrace_3041392 : CollatzResearch.WordTrace tailWord_3041392 prefixEnd_3041392 520565318246423257837633 := by
  unfold tailWord_3041392
  simp only [CollatzResearch.WordTrace]
  refine ⟨55464339698781843622451215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73952452931709124829934953 55464339698781843622451215)
  ·
    refine ⟨83196509548172765433676823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55464339698781843622451215 83196509548172765433676823)
    ·
      refine ⟨124794764322259148150515235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83196509548172765433676823 124794764322259148150515235)
      ·
        refine ⟨187192146483388722225772853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124794764322259148150515235 187192146483388722225772853)
        ·
          refine ⟨17549263732817692708666205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187192146483388722225772853 17549263732817692708666205)
          ·
            refine ⟨6580973899806634765749827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17549263732817692708666205 6580973899806634765749827)
            ·
              refine ⟨9871460849709952148624741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580973899806634765749827 9871460849709952148624741)
              ·
                refine ⟨1850898909320616027867139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9871460849709952148624741 1850898909320616027867139)
                ·
                  refine ⟨2776348363980924041800709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850898909320616027867139 2776348363980924041800709)
                  ·
                    refine ⟨520565318246423257837633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2776348363980924041800709 520565318246423257837633)
                    ·
                      rfl

theorem cell23_3041392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 4].length) (baseStart_3041392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041392 prefixEnd_3041392 := by exact prefixLift 3041392
  have htrace : WordTrace (prefixWord ++ tailWord_3041392) baseStart_3041392 baseEnd_3041392 := by
    simpa [prefixWord, tailWord_3041392, baseEnd_3041392] using wordTrace_append hprefix tailTrace_3041392
  have hstable : (prefixWord ++ tailWord_3041392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041392).length < 2 ^ (prefixWord ++ tailWord_3041392).sum := by decide
  have hdescent : baseEnd_3041392 < baseStart_3041392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041415 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_3041415 : Nat := 118140960795 + 3041415 * 2 ^ 59
def prefixEnd_3041415 : Nat := 4983230072969 + 3 ^ 40 * 3041415 * 2
def baseEnd_3041415 : Nat := 1561707764794323183525293

theorem tailTrace_3041415 : CollatzResearch.WordTrace tailWord_3041415 prefixEnd_3041415 1561707764794323183525293 := by
  unfold tailWord_3041415
  simp only [CollatzResearch.WordTrace]
  refine ⟨110929518276480362172989699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73953012184320241448659799 110929518276480362172989699)
  ·
    refine ⟨166394277414720543259484549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110929518276480362172989699 166394277414720543259484549)
    ·
      refine ⟨31198927015260101861153353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166394277414720543259484549 31198927015260101861153353)
      ·
        refine ⟨23399195261445076395865015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31198927015260101861153353 23399195261445076395865015)
        ·
          refine ⟨35098792892167614593797523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23399195261445076395865015 35098792892167614593797523)
          ·
            refine ⟨52648189338251421890696285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35098792892167614593797523 52648189338251421890696285)
            ·
              refine ⟨19743071001844283209011107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52648189338251421890696285 19743071001844283209011107)
              ·
                refine ⟨29614606502766424813516661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19743071001844283209011107 29614606502766424813516661)
                ·
                  refine ⟨2776369359634352326267187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29614606502766424813516661 2776369359634352326267187)
                  ·
                    refine ⟨4164554039451528489400781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2776369359634352326267187 4164554039451528489400781)
                    ·
                      refine ⟨1561707764794323183525293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4164554039451528489400781 1561707764794323183525293)
                      ·
                        rfl

theorem cell23_3041415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_3041415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041415 prefixEnd_3041415 := by exact prefixLift 3041415
  have htrace : WordTrace (prefixWord ++ tailWord_3041415) baseStart_3041415 baseEnd_3041415 := by
    simpa [prefixWord, tailWord_3041415, baseEnd_3041415] using wordTrace_append hprefix tailTrace_3041415
  have hstable : (prefixWord ++ tailWord_3041415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041415).length < 2 ^ (prefixWord ++ tailWord_3041415).sum := by decide
  have hdescent : baseEnd_3041415 < baseStart_3041415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041472 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_3041472 : Nat := 118140960795 + 3041472 * 2 ^ 59
def prefixEnd_3041472 : Nat := 4983230072969 + 3 ^ 40 * 3041472 * 2
def baseEnd_3041472 : Nat := 1561737033191629460512531

theorem tailTrace_3041472 : CollatzResearch.WordTrace tailWord_3041472 prefixEnd_3041472 1561737033191629460512531 := by
  unfold tailWord_3041472
  simp only [CollatzResearch.WordTrace]
  refine ⟨55465798618636930453907335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73954398158182573938543113 55465798618636930453907335)
  ·
    refine ⟨83198697927955395680861003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55465798618636930453907335 83198697927955395680861003)
    ·
      refine ⟨124798046891933093521291505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83198697927955395680861003 124798046891933093521291505)
      ·
        refine ⟨93598535168949820140968629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124798046891933093521291505 93598535168949820140968629)
        ·
          refine ⟨8774862672089045638215809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93598535168949820140968629 8774862672089045638215809)
          ·
            refine ⟨6581147004066784228661857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8774862672089045638215809 6581147004066784228661857)
            ·
              refine ⟨4935860253050088171496393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581147004066784228661857 4935860253050088171496393)
              ·
                refine ⟨3701895189787566128622295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4935860253050088171496393 3701895189787566128622295)
                ·
                  refine ⟨5552842784681349192933443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701895189787566128622295 5552842784681349192933443)
                  ·
                    refine ⟨8329264177022023789400165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5552842784681349192933443 8329264177022023789400165)
                    ·
                      refine ⟨1561737033191629460512531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8329264177022023789400165 1561737033191629460512531)
                      ·
                        rfl

theorem cell23_3041472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_3041472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041472 prefixEnd_3041472 := by exact prefixLift 3041472
  have htrace : WordTrace (prefixWord ++ tailWord_3041472) baseStart_3041472 baseEnd_3041472 := by
    simpa [prefixWord, tailWord_3041472, baseEnd_3041472] using wordTrace_append hprefix tailTrace_3041472
  have hstable : (prefixWord ++ tailWord_3041472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041472).length < 2 ^ (prefixWord ++ tailWord_3041472).sum := by decide
  have hdescent : baseEnd_3041472 < baseStart_3041472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041500 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3041500 : Nat := 118140960795 + 3041500 * 2 ^ 59
def prefixEnd_3041500 : Nat := 4983230072969 + 3 ^ 40 * 3041500 * 2
def baseEnd_3041500 : Nat := 1561751410649955350962403

theorem tailTrace_3041500 : CollatzResearch.WordTrace tailWord_3041500 prefixEnd_3041500 1561751410649955350962403 := by
  unfold tailWord_3041500
  simp only [CollatzResearch.WordTrace]
  refine ⟨55466309240586210844916977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73955078987448281126555969 55466309240586210844916977)
  ·
    refine ⟨41599731930439658133687733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55466309240586210844916977 41599731930439658133687733)
    ·
      refine ⟨3899974868478717950033225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41599731930439658133687733 3899974868478717950033225)
      ·
        refine ⟨2924981151359038462524919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3899974868478717950033225 2924981151359038462524919)
        ·
          refine ⟨4387471727038557693787379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924981151359038462524919 4387471727038557693787379)
          ·
            refine ⟨6581207590557836540681069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387471727038557693787379 6581207590557836540681069)
            ·
              refine ⟨2467952846459188702755401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6581207590557836540681069 2467952846459188702755401)
              ·
                refine ⟨1850964634844391527066551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467952846459188702755401 1850964634844391527066551)
                ·
                  refine ⟨2776446952266587290599827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850964634844391527066551 2776446952266587290599827)
                  ·
                    refine ⟨4164670428399880935899741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2776446952266587290599827 4164670428399880935899741)
                    ·
                      refine ⟨1561751410649955350962403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4164670428399880935899741 1561751410649955350962403)
                      ·
                        rfl

theorem cell23_3041500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3041500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041500 prefixEnd_3041500 := by exact prefixLift 3041500
  have htrace : WordTrace (prefixWord ++ tailWord_3041500) baseStart_3041500 baseEnd_3041500 := by
    simpa [prefixWord, tailWord_3041500, baseEnd_3041500] using wordTrace_append hprefix tailTrace_3041500
  have hstable : (prefixWord ++ tailWord_3041500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041500).length < 2 ^ (prefixWord ++ tailWord_3041500).sum := by decide
  have hdescent : baseEnd_3041500 < baseStart_3041500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041508 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_3041508 : Nat := 118140960795 + 3041508 * 2 ^ 59
def prefixEnd_3041508 : Nat := 4983230072969 + 3 ^ 40 * 3041508 * 2
def baseEnd_3041508 : Nat := 520585172831730439887455

theorem tailTrace_3041508 : CollatzResearch.WordTrace tailWord_3041508 prefixEnd_3041508 520585172831730439887455 := by
  unfold tailWord_3041508
  simp only [CollatzResearch.WordTrace]
  refine ⟨55466455132571719528062589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73955273510095626037416785 55466455132571719528062589)
  ·
    refine ⟨20799920674714394823023471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55466455132571719528062589 20799920674714394823023471)
    ·
      refine ⟨31199881012071592234535207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20799920674714394823023471 31199881012071592234535207)
      ·
        refine ⟨46799821518107388351802811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31199881012071592234535207 46799821518107388351802811)
        ·
          refine ⟨70199732277161082527704217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46799821518107388351802811 70199732277161082527704217)
          ·
            refine ⟨52649799207870811895778163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70199732277161082527704217 52649799207870811895778163)
            ·
              refine ⟨78974698811806217843667245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52649799207870811895778163 78974698811806217843667245)
              ·
                refine ⟨29615512054427331691375217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78974698811806217843667245 29615512054427331691375217)
                ·
                  refine ⟨22211634040820498768531413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29615512054427331691375217 22211634040820498768531413)
                  ·
                    refine ⟨520585172831730439887455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22211634040820498768531413 520585172831730439887455)
                    ·
                      rfl

theorem cell23_3041508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_3041508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041508 prefixEnd_3041508 := by exact prefixLift 3041508
  have htrace : WordTrace (prefixWord ++ tailWord_3041508) baseStart_3041508 baseEnd_3041508 := by
    simpa [prefixWord, tailWord_3041508, baseEnd_3041508] using wordTrace_append hprefix tailTrace_3041508
  have hstable : (prefixWord ++ tailWord_3041508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041508).length < 2 ^ (prefixWord ++ tailWord_3041508).sum := by decide
  have hdescent : baseEnd_3041508 < baseStart_3041508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041566 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3041566 : Nat := 118140960795 + 3041566 * 2 ^ 59
def prefixEnd_3041566 : Nat := 4983230072969 + 3 ^ 40 * 3041566 * 2
def baseEnd_3041566 : Nat := 1561785300373152092737099

theorem tailTrace_3041566 : CollatzResearch.WordTrace tailWord_3041566 prefixEnd_3041566 1561785300373152092737099 := by
  unfold tailWord_3041566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866878212366664370217069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73956683799288876641157701 13866878212366664370217069)
  ·
    refine ⟨5200079329637499138831401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13866878212366664370217069 5200079329637499138831401)
    ·
      refine ⟨3900059497228124354123551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5200079329637499138831401 3900059497228124354123551)
      ·
        refine ⟨5850089245842186531185327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900059497228124354123551 5850089245842186531185327)
        ·
          refine ⟨8775133868763279796777991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850089245842186531185327 8775133868763279796777991)
          ·
            refine ⟨13162700803144919695166987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775133868763279796777991 13162700803144919695166987)
            ·
              refine ⟨19744051204717379542750481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13162700803144919695166987 19744051204717379542750481)
              ·
                refine ⟨14808038403538034657062861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19744051204717379542750481 14808038403538034657062861)
                ·
                  refine ⟨5553014401326762996398573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14808038403538034657062861 5553014401326762996398573)
                  ·
                    refine ⟨2082380400497536123649465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5553014401326762996398573 2082380400497536123649465)
                    ·
                      refine ⟨1561785300373152092737099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082380400497536123649465 1561785300373152092737099)
                      ·
                        rfl

theorem cell23_3041566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3041566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041566 prefixEnd_3041566 := by exact prefixLift 3041566
  have htrace : WordTrace (prefixWord ++ tailWord_3041566) baseStart_3041566 baseEnd_3041566 := by
    simpa [prefixWord, tailWord_3041566, baseEnd_3041566] using wordTrace_append hprefix tailTrace_3041566
  have hstable : (prefixWord ++ tailWord_3041566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041566).length < 2 ^ (prefixWord ++ tailWord_3041566).sum := by decide
  have hdescent : baseEnd_3041566 < baseStart_3041566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041635 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3041635 : Nat := 118140960795 + 3041635 * 2 ^ 59
def prefixEnd_3041635 : Nat := 4983230072969 + 3 ^ 40 * 3041635 * 2
def baseEnd_3041635 : Nat := 1561820730538312322774281

theorem tailTrace_3041635 : CollatzResearch.WordTrace tailWord_3041635 prefixEnd_3041635 1561820730538312322774281 := by
  unfold tailWord_3041635
  simp only [CollatzResearch.WordTrace]
  refine ⟨110937542335683339745998359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73958361557122226497332239 110937542335683339745998359)
  ·
    refine ⟨166406313503525009618997539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110937542335683339745998359 166406313503525009618997539)
    ·
      refine ⟨249609470255287514428496309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166406313503525009618997539 249609470255287514428496309)
      ·
        refine ⟨23400887836433204477671529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249609470255287514428496309 23400887836433204477671529)
        ·
          refine ⟨17550665877324903358253647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23400887836433204477671529 17550665877324903358253647)
          ·
            refine ⟨26325998815987355037380471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17550665877324903358253647 26325998815987355037380471)
            ·
              refine ⟨39488998223981032556070707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26325998815987355037380471 39488998223981032556070707)
              ·
                refine ⟨59233497335971548834106061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39488998223981032556070707 59233497335971548834106061)
                ·
                  refine ⟨22212561500989330812789773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59233497335971548834106061 22212561500989330812789773)
                  ·
                    refine ⟨8329710562870999054796165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22212561500989330812789773 8329710562870999054796165)
                    ·
                      refine ⟨1561820730538312322774281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8329710562870999054796165 1561820730538312322774281)
                      ·
                        rfl

theorem cell23_3041635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3041635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041635 prefixEnd_3041635 := by exact prefixLift 3041635
  have htrace : WordTrace (prefixWord ++ tailWord_3041635) baseStart_3041635 baseEnd_3041635 := by
    simpa [prefixWord, tailWord_3041635, baseEnd_3041635] using wordTrace_append hprefix tailTrace_3041635
  have hstable : (prefixWord ++ tailWord_3041635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041635).length < 2 ^ (prefixWord ++ tailWord_3041635).sum := by decide
  have hdescent : baseEnd_3041635 < baseStart_3041635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041645 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3041645 : Nat := 118140960795 + 3041645 * 2 ^ 59
def prefixEnd_3041645 : Nat := 4983230072969 + 3 ^ 40 * 3041645 * 2
def baseEnd_3041645 : Nat := 520608621781619094549745

theorem tailTrace_3041645 : CollatzResearch.WordTrace tailWord_3041645 prefixEnd_3041645 520608621781619094549745 := by
  unfold tailWord_3041645
  simp only [CollatzResearch.WordTrace]
  refine ⟨110937907065647111453862389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73958604710431407635908259 110937907065647111453862389)
  ·
    refine ⟨10400428787404416698799599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110937907065647111453862389 10400428787404416698799599)
    ·
      refine ⟨15600643181106625048199399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400428787404416698799599 15600643181106625048199399)
      ·
        refine ⟨23400964771659937572299099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600643181106625048199399 23400964771659937572299099)
        ·
          refine ⟨35101447157489906358448649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23400964771659937572299099 35101447157489906358448649)
          ·
            refine ⟨26326085368117429768836487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35101447157489906358448649 26326085368117429768836487)
            ·
              refine ⟨39489128052176144653254731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26326085368117429768836487 39489128052176144653254731)
              ·
                refine ⟨59233692078264216979882097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39489128052176144653254731 59233692078264216979882097)
                ·
                  refine ⟨44425269058698162734911573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59233692078264216979882097 44425269058698162734911573)
                  ·
                    refine ⟨520608621781619094549745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44425269058698162734911573 520608621781619094549745)
                    ·
                      rfl

theorem cell23_3041645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3041645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041645 prefixEnd_3041645 := by exact prefixLift 3041645
  have htrace : WordTrace (prefixWord ++ tailWord_3041645) baseStart_3041645 baseEnd_3041645 := by
    simpa [prefixWord, tailWord_3041645, baseEnd_3041645] using wordTrace_append hprefix tailTrace_3041645
  have hstable : (prefixWord ++ tailWord_3041645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041645).length < 2 ^ (prefixWord ++ tailWord_3041645).sum := by decide
  have hdescent : baseEnd_3041645 < baseStart_3041645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041666 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3041666 : Nat := 118140960795 + 3041666 * 2 ^ 59
def prefixEnd_3041666 : Nat := 4983230072969 + 3 ^ 40 * 3041666 * 2
def baseEnd_3041666 : Nat := 520612216146200567162213

theorem tailTrace_3041666 : CollatzResearch.WordTrace tailWord_3041666 prefixEnd_3041666 520612216146200567162213 := by
  unfold tailWord_3041666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27734668249642758010094213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73959115332380688026917901 27734668249642758010094213)
  ·
    refine ⟨5200250296808017126892665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27734668249642758010094213 5200250296808017126892665)
    ·
      refine ⟨3900187722606012845169499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5200250296808017126892665 3900187722606012845169499)
      ·
        refine ⟨5850281583909019267754249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900187722606012845169499 5850281583909019267754249)
        ·
          refine ⟨4387711187931764450815687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5850281583909019267754249 4387711187931764450815687)
          ·
            refine ⟨6581566781897646676223531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387711187931764450815687 6581566781897646676223531)
            ·
              refine ⟨9872350172846470014335297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581566781897646676223531 9872350172846470014335297)
              ·
                refine ⟨7404262629634852510751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9872350172846470014335297 7404262629634852510751473)
                ·
                  refine ⟨5553196972226139383063605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404262629634852510751473 5553196972226139383063605)
                  ·
                    refine ⟨520612216146200567162213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553196972226139383063605 520612216146200567162213)
                    ·
                      rfl

theorem cell23_3041666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3041666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041666 prefixEnd_3041666 := by exact prefixLift 3041666
  have htrace : WordTrace (prefixWord ++ tailWord_3041666) baseStart_3041666 baseEnd_3041666 := by
    simpa [prefixWord, tailWord_3041666, baseEnd_3041666] using wordTrace_append hprefix tailTrace_3041666
  have hstable : (prefixWord ++ tailWord_3041666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041666).length < 2 ^ (prefixWord ++ tailWord_3041666).sum := by decide
  have hdescent : baseEnd_3041666 < baseStart_3041666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041675 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 8]
def baseStart_3041675 : Nat := 118140960795 + 3041675 * 2 ^ 59
def prefixEnd_3041675 : Nat := 4983230072969 + 3 ^ 40 * 3041675 * 2
def baseEnd_3041675 : Nat := 173537918862721351808233

theorem tailTrace_3041675 : CollatzResearch.WordTrace tailWord_3041675 prefixEnd_3041675 173537918862721351808233 := by
  unfold tailWord_3041675
  simp only [CollatzResearch.WordTrace]
  refine ⟨110939001255538426577454479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73959334170358951051636319 110939001255538426577454479)
  ·
    refine ⟨166408501883307639866181719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110939001255538426577454479 166408501883307639866181719)
    ·
      refine ⟨249612752824961459799272579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166408501883307639866181719 249612752824961459799272579)
      ·
        refine ⟨374419129237442189698908869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249612752824961459799272579 374419129237442189698908869)
        ·
          refine ⟨70203586732020410568545413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374419129237442189698908869 70203586732020410568545413)
          ·
            refine ⟨13163172512253826981602265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70203586732020410568545413 13163172512253826981602265)
            ·
              refine ⟨9872379384190370236201699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13163172512253826981602265 9872379384190370236201699)
              ·
                refine ⟨14808569076285555354302549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9872379384190370236201699 14808569076285555354302549)
                ·
                  refine ⟨173537918862721351808233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14808569076285555354302549 173537918862721351808233)
                  ·
                    rfl

theorem cell23_3041675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 8].length) (baseStart_3041675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041675 prefixEnd_3041675 := by exact prefixLift 3041675
  have htrace : WordTrace (prefixWord ++ tailWord_3041675) baseStart_3041675 baseEnd_3041675 := by
    simpa [prefixWord, tailWord_3041675, baseEnd_3041675] using wordTrace_append hprefix tailTrace_3041675
  have hstable : (prefixWord ++ tailWord_3041675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041675).length < 2 ^ (prefixWord ++ tailWord_3041675).sum := by decide
  have hdescent : baseEnd_3041675 < baseStart_3041675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041712 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2]
def baseStart_3041712 : Nat := 118140960795 + 3041712 * 2 ^ 59
def prefixEnd_3041712 : Nat := 4983230072969 + 3 ^ 40 * 3041712 * 2
def baseEnd_3041712 : Nat := 1561860268548708521511427

theorem tailTrace_3041712 : CollatzResearch.WordTrace tailWord_3041712 prefixEnd_3041712 1561860268548708521511427 := by
  unfold tailWord_3041712
  simp only [CollatzResearch.WordTrace]
  refine ⟨55470175378202190948275695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73960233837602921264367593 55470175378202190948275695)
  ·
    refine ⟨83205263067303286422413543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55470175378202190948275695 83205263067303286422413543)
    ·
      refine ⟨124807894600954929633620315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83205263067303286422413543 124807894600954929633620315)
      ·
        refine ⟨187211841901432394450430473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124807894600954929633620315 187211841901432394450430473)
        ·
          refine ⟨140408881426074295837822855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187211841901432394450430473 140408881426074295837822855)
          ·
            refine ⟨210613322139111443756734283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140408881426074295837822855 210613322139111443756734283)
            ·
              refine ⟨315919983208667165635101425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210613322139111443756734283 315919983208667165635101425)
              ·
                refine ⟨236939987406500374226326069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315919983208667165635101425 236939987406500374226326069)
                ·
                  refine ⟨22213123819359410083718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236939987406500374226326069 22213123819359410083718069)
                  ·
                    refine ⟨2082480358064944695348569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22213123819359410083718069 2082480358064944695348569)
                    ·
                      refine ⟨1561860268548708521511427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082480358064944695348569 1561860268548708521511427)
                      ·
                        rfl

theorem cell23_3041712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2].length) (baseStart_3041712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041712 prefixEnd_3041712 := by exact prefixLift 3041712
  have htrace : WordTrace (prefixWord ++ tailWord_3041712) baseStart_3041712 baseEnd_3041712 := by
    simpa [prefixWord, tailWord_3041712, baseEnd_3041712] using wordTrace_append hprefix tailTrace_3041712
  have hstable : (prefixWord ++ tailWord_3041712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041712).length < 2 ^ (prefixWord ++ tailWord_3041712).sum := by decide
  have hdescent : baseEnd_3041712 < baseStart_3041712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041722 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_3041722 : Nat := 118140960795 + 3041722 * 2 ^ 59
def prefixEnd_3041722 : Nat := 4983230072969 + 3 ^ 40 * 3041722 * 2
def baseEnd_3041722 : Nat := 520621801118417827462127

theorem tailTrace_3041722 : CollatzResearch.WordTrace tailWord_3041722 prefixEnd_3041722 520621801118417827462127 := by
  unfold tailWord_3041722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27735178871592038401103855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73960476990912102402943613 27735178871592038401103855)
  ·
    refine ⟨41602768307388057601655783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27735178871592038401103855 41602768307388057601655783)
    ·
      refine ⟨62404152461082086402483675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41602768307388057601655783 62404152461082086402483675)
      ·
        refine ⟨93606228691623129603725513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62404152461082086402483675 93606228691623129603725513)
        ·
          refine ⟨70204671518717347202794135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93606228691623129603725513 70204671518717347202794135)
          ·
            refine ⟨105307007278076020804191203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70204671518717347202794135 105307007278076020804191203)
            ·
              refine ⟨157960510917114031206286805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105307007278076020804191203 157960510917114031206286805)
              ·
                refine ⟨3702199474619860106397347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157960510917114031206286805 3702199474619860106397347)
                ·
                  refine ⟨5553299211929790159596021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702199474619860106397347 5553299211929790159596021)
                  ·
                    refine ⟨520621801118417827462127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553299211929790159596021 520621801118417827462127)
                    ·
                      rfl

theorem cell23_3041722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_3041722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041722 prefixEnd_3041722 := by exact prefixLift 3041722
  have htrace : WordTrace (prefixWord ++ tailWord_3041722) baseStart_3041722 baseEnd_3041722 := by
    simpa [prefixWord, tailWord_3041722, baseEnd_3041722] using wordTrace_append hprefix tailTrace_3041722
  have hstable : (prefixWord ++ tailWord_3041722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041722).length < 2 ^ (prefixWord ++ tailWord_3041722).sum := by decide
  have hdescent : baseEnd_3041722 < baseStart_3041722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041752 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_3041752 : Nat := 118140960795 + 3041752 * 2 ^ 59
def prefixEnd_3041752 : Nat := 4983230072969 + 3 ^ 40 * 3041752 * 2
def baseEnd_3041752 : Nat := 520626935924962788337081

theorem tailTrace_3041752 : CollatzResearch.WordTrace tailWord_3041752 prefixEnd_3041752 520626935924962788337081 := by
  unfold tailWord_3041752
  simp only [CollatzResearch.WordTrace]
  refine ⟨55470904838129734364003755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73961206450839645818671673 55470904838129734364003755)
  ·
    refine ⟨83206357257194601546005633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55470904838129734364003755 83206357257194601546005633)
    ·
      refine ⟨62404767942895951159504225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83206357257194601546005633 62404767942895951159504225)
      ·
        refine ⟨46803575957171963369628169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62404767942895951159504225 46803575957171963369628169)
        ·
          refine ⟨35102681967878972527221127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46803575957171963369628169 35102681967878972527221127)
          ·
            refine ⟨52654022951818458790831691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35102681967878972527221127 52654022951818458790831691)
            ·
              refine ⟨78981034427727688186247537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52654022951818458790831691 78981034427727688186247537)
              ·
                refine ⟨59235775820795766139685653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78981034427727688186247537 59235775820795766139685653)
                ·
                  refine ⟨2776676991599801537797765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59235775820795766139685653 2776676991599801537797765)
                  ·
                    refine ⟨520626935924962788337081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2776676991599801537797765 520626935924962788337081)
                    ·
                      rfl

theorem cell23_3041752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_3041752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041752 prefixEnd_3041752 := by exact prefixLift 3041752
  have htrace : WordTrace (prefixWord ++ tailWord_3041752) baseStart_3041752 baseEnd_3041752 := by
    simpa [prefixWord, tailWord_3041752, baseEnd_3041752] using wordTrace_append hprefix tailTrace_3041752
  have hstable : (prefixWord ++ tailWord_3041752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041752).length < 2 ^ (prefixWord ++ tailWord_3041752).sum := by decide
  have hdescent : baseEnd_3041752 < baseStart_3041752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041763 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3041763 : Nat := 118140960795 + 3041763 * 2 ^ 59
def prefixEnd_3041763 : Nat := 4983230072969 + 3 ^ 40 * 3041763 * 2
def baseEnd_3041763 : Nat := 1561886456062087821973693

theorem tailTrace_3041763 : CollatzResearch.WordTrace tailWord_3041763 prefixEnd_3041763 1561886456062087821973693 := by
  unfold tailWord_3041763
  simp only [CollatzResearch.WordTrace]
  refine ⟨110942210879219617606657943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73961473919479745071105295 110942210879219617606657943)
  ·
    refine ⟨166413316318829426409986915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110942210879219617606657943 166413316318829426409986915)
    ·
      refine ⟨249619974478244139614980373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166413316318829426409986915 249619974478244139614980373)
      ·
        refine ⟨11700936303667694044452205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249619974478244139614980373 11700936303667694044452205)
        ·
          refine ⟨4387851113875385266669577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11700936303667694044452205 4387851113875385266669577)
          ·
            refine ⟨3290888335406538950002183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4387851113875385266669577 3290888335406538950002183)
            ·
              refine ⟨4936332503109808425003275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290888335406538950002183 4936332503109808425003275)
              ·
                refine ⟨7404498754664712637504913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936332503109808425003275 7404498754664712637504913)
                ·
                  refine ⟨5553374065998534478128685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404498754664712637504913 5553374065998534478128685)
                  ·
                    refine ⟨2082515274749450429298257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5553374065998534478128685 2082515274749450429298257)
                    ·
                      refine ⟨1561886456062087821973693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082515274749450429298257 1561886456062087821973693)
                      ·
                        rfl

theorem cell23_3041763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3041763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041763 prefixEnd_3041763 := by exact prefixLift 3041763
  have htrace : WordTrace (prefixWord ++ tailWord_3041763) baseStart_3041763 baseEnd_3041763 := by
    simpa [prefixWord, tailWord_3041763, baseEnd_3041763] using wordTrace_append hprefix tailTrace_3041763
  have hstable : (prefixWord ++ tailWord_3041763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041763).length < 2 ^ (prefixWord ++ tailWord_3041763).sum := by decide
  have hdescent : baseEnd_3041763 < baseStart_3041763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041772 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3041772 : Nat := 118140960795 + 3041772 * 2 ^ 59
def prefixEnd_3041772 : Nat := 4983230072969 + 3 ^ 40 * 3041772 * 2
def baseEnd_3041772 : Nat := 1561891077387978286761151

theorem tailTrace_3041772 : CollatzResearch.WordTrace tailWord_3041772 prefixEnd_3041772 1561891077387978286761151 := by
  unfold tailWord_3041772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55471269568093506071867785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73961692757458008095823713 55471269568093506071867785)
  ·
    refine ⟨41603452176070129553900839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55471269568093506071867785 41603452176070129553900839)
    ·
      refine ⟨62405178264105194330851259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41603452176070129553900839 62405178264105194330851259)
      ·
        refine ⟨93607767396157791496276889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62405178264105194330851259 93607767396157791496276889)
        ·
          refine ⟨70205825547118343622207667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93607767396157791496276889 70205825547118343622207667)
          ·
            refine ⟨105308738320677515433311501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70205825547118343622207667 105308738320677515433311501)
            ·
              refine ⟨39490776870254068287491813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105308738320677515433311501 39490776870254068287491813)
              ·
                refine ⟨7404520663172637803904715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39490776870254068287491813 7404520663172637803904715)
                ·
                  refine ⟨11106780994758956705857073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7404520663172637803904715 11106780994758956705857073)
                  ·
                    refine ⟨8330085746069217529392805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11106780994758956705857073 8330085746069217529392805)
                    ·
                      refine ⟨1561891077387978286761151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8330085746069217529392805 1561891077387978286761151)
                      ·
                        rfl

theorem cell23_3041772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3041772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041772 prefixEnd_3041772 := by exact prefixLift 3041772
  have htrace : WordTrace (prefixWord ++ tailWord_3041772) baseStart_3041772 baseEnd_3041772 := by
    simpa [prefixWord, tailWord_3041772, baseEnd_3041772] using wordTrace_append hprefix tailTrace_3041772
  have hstable : (prefixWord ++ tailWord_3041772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041772).length < 2 ^ (prefixWord ++ tailWord_3041772).sum := by decide
  have hdescent : baseEnd_3041772 < baseStart_3041772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041773 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_3041773 : Nat := 118140960795 + 3041773 * 2 ^ 59
def prefixEnd_3041773 : Nat := 4983230072969 + 3 ^ 40 * 3041773 * 2
def baseEnd_3041773 : Nat := 520630530289544260949549

theorem tailTrace_3041773 : CollatzResearch.WordTrace tailWord_3041773 prefixEnd_3041773 520630530289544260949549 := by
  unfold tailWord_3041773
  simp only [CollatzResearch.WordTrace]
  refine ⟨110942575609183389314521973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73961717072788926209681315 110942575609183389314521973)
  ·
    refine ⟨10400866463360942748236435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110942575609183389314521973 10400866463360942748236435)
    ·
      refine ⟨15601299695041414122354653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400866463360942748236435 15601299695041414122354653)
      ·
        refine ⟨5850487385640530295882995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15601299695041414122354653 5850487385640530295882995)
        ·
          refine ⟨8775731078460795443824493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850487385640530295882995 8775731078460795443824493)
          ·
            refine ⟨3290899154422798291434185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8775731078460795443824493 3290899154422798291434185)
            ·
              refine ⟨2468174365817098718575639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290899154422798291434185 2468174365817098718575639)
              ·
                refine ⟨3702261548725648077863459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468174365817098718575639 3702261548725648077863459)
                ·
                  refine ⟨5553392323088472116795189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702261548725648077863459 5553392323088472116795189)
                  ·
                    refine ⟨520630530289544260949549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553392323088472116795189 520630530289544260949549)
                    ·
                      rfl

theorem cell23_3041773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_3041773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041773 prefixEnd_3041773 := by exact prefixLift 3041773
  have htrace : WordTrace (prefixWord ++ tailWord_3041773) baseStart_3041773 baseEnd_3041773 := by
    simpa [prefixWord, tailWord_3041773, baseEnd_3041773] using wordTrace_append hprefix tailTrace_3041773
  have hstable : (prefixWord ++ tailWord_3041773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041773).length < 2 ^ (prefixWord ++ tailWord_3041773).sum := by decide
  have hdescent : baseEnd_3041773 < baseStart_3041773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041779 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 3]
def baseStart_3041779 : Nat := 118140960795 + 3041779 * 2 ^ 59
def prefixEnd_3041779 : Nat := 4983230072969 + 3 ^ 40 * 3041779 * 2
def baseEnd_3041779 : Nat := 1561894671752559759373619

theorem tailTrace_3041779 : CollatzResearch.WordTrace tailWord_3041779 prefixEnd_3041779 1561894671752559759373619 := by
  unfold tailWord_3041779
  simp only [CollatzResearch.WordTrace]
  refine ⟨110942794447161652339240391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73961862964774434892826927 110942794447161652339240391)
  ·
    refine ⟨166414191670742478508860587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110942794447161652339240391 166414191670742478508860587)
    ·
      refine ⟨249621287506113717763290881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166414191670742478508860587 249621287506113717763290881)
      ·
        refine ⟨187215965629585288322468161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249621287506113717763290881 187215965629585288322468161)
        ·
          refine ⟨140411974222188966241851121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187215965629585288322468161 140411974222188966241851121)
          ·
            refine ⟨105308980666641724681388341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140411974222188966241851121 105308980666641724681388341)
            ·
              refine ⟨9872716937497661688880157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105308980666641724681388341 9872716937497661688880157)
              ·
                refine ⟨3702268851561623133330059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9872716937497661688880157 3702268851561623133330059)
                ·
                  refine ⟨5553403277342434699995089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702268851561623133330059 5553403277342434699995089)
                  ·
                    refine ⟨4165052458006826024996317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553403277342434699995089 4165052458006826024996317)
                    ·
                      refine ⟨1561894671752559759373619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165052458006826024996317 1561894671752559759373619)
                      ·
                        rfl

theorem cell23_3041779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_3041779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041779 prefixEnd_3041779 := by exact prefixLift 3041779
  have htrace : WordTrace (prefixWord ++ tailWord_3041779) baseStart_3041779 baseEnd_3041779 := by
    simpa [prefixWord, tailWord_3041779, baseEnd_3041779] using wordTrace_append hprefix tailTrace_3041779
  have hstable : (prefixWord ++ tailWord_3041779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041779).length < 2 ^ (prefixWord ++ tailWord_3041779).sum := by decide
  have hdescent : baseEnd_3041779 < baseStart_3041779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041782 : List Nat := [5, 1, 1, 1, 2, 1, 12]
def baseStart_3041782 : Nat := 118140960795 + 3041782 * 2 ^ 59
def prefixEnd_3041782 : Nat := 4983230072969 + 3 ^ 40 * 3041782 * 2
def baseEnd_3041782 : Nat := 19282669286352138859705

theorem tailTrace_3041782 : CollatzResearch.WordTrace tailWord_3041782 prefixEnd_3041782 19282669286352138859705 := by
  unfold tailWord_3041782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933931491634423990724975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73961935910767189234399733 6933931491634423990724975)
  ·
    refine ⟨10400897237451635986087463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6933931491634423990724975 10400897237451635986087463)
    ·
      refine ⟨15601345856177453979131195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400897237451635986087463 15601345856177453979131195)
      ·
        refine ⟨23402018784266180968696793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15601345856177453979131195 23402018784266180968696793)
        ·
          refine ⟨17551514088199635726522595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23402018784266180968696793 17551514088199635726522595)
          ·
            refine ⟨26327271132299453589783893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17551514088199635726522595 26327271132299453589783893)
            ·
              refine ⟨19282669286352138859705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 26327271132299453589783893 19282669286352138859705)
              ·
                rfl

theorem cell23_3041782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 12].length) (baseStart_3041782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041782 prefixEnd_3041782 := by exact prefixLift 3041782
  have htrace : WordTrace (prefixWord ++ tailWord_3041782) baseStart_3041782 baseEnd_3041782 := by
    simpa [prefixWord, tailWord_3041782, baseEnd_3041782] using wordTrace_append hprefix tailTrace_3041782
  have hstable : (prefixWord ++ tailWord_3041782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041782).length < 2 ^ (prefixWord ++ tailWord_3041782).sum := by decide
  have hdescent : baseEnd_3041782 < baseStart_3041782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041793 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_3041793 : Nat := 118140960795 + 3041793 * 2 ^ 59
def prefixEnd_3041793 : Nat := 4983230072969 + 3 ^ 40 * 3041793 * 2
def baseEnd_3041793 : Nat := 1561901860481722704598555

theorem tailTrace_3041793 : CollatzResearch.WordTrace tailWord_3041793 prefixEnd_3041793 1561901860481722704598555 := by
  unfold tailWord_3041793
  simp only [CollatzResearch.WordTrace]
  refine ⟨110943305069110932730250033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73962203379407288486833355 110943305069110932730250033)
  ·
    refine ⟨83207478801833199547687525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110943305069110932730250033 83207478801833199547687525)
    ·
      refine ⟨15601402275343724915191411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83207478801833199547687525 15601402275343724915191411)
      ·
        refine ⟨23402103413015587372787117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15601402275343724915191411 23402103413015587372787117)
        ·
          refine ⟨8775788779880845264795169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23402103413015587372787117 8775788779880845264795169)
          ·
            refine ⟨6581841584910633948596377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775788779880845264795169 6581841584910633948596377)
            ·
              refine ⟨4936381188682975461447283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581841584910633948596377 4936381188682975461447283)
              ·
                refine ⟨7404571783024463192170925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936381188682975461447283 7404571783024463192170925)
                ·
                  refine ⟨2776714418634173697064097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7404571783024463192170925 2776714418634173697064097)
                  ·
                    refine ⟨2082535813975630272798073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2776714418634173697064097 2082535813975630272798073)
                    ·
                      refine ⟨1561901860481722704598555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082535813975630272798073 1561901860481722704598555)
                      ·
                        rfl

theorem cell23_3041793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_3041793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041793 prefixEnd_3041793 := by exact prefixLift 3041793
  have htrace : WordTrace (prefixWord ++ tailWord_3041793) baseStart_3041793 baseEnd_3041793 := by
    simpa [prefixWord, tailWord_3041793, baseEnd_3041793] using wordTrace_append hprefix tailTrace_3041793
  have hstable : (prefixWord ++ tailWord_3041793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041793).length < 2 ^ (prefixWord ++ tailWord_3041793).sum := by decide
  have hdescent : baseEnd_3041793 < baseStart_3041793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041806 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3041806 : Nat := 118140960795 + 3041806 * 2 ^ 59
def prefixEnd_3041806 : Nat := 4983230072969 + 3 ^ 40 * 3041806 * 2
def baseEnd_3041806 : Nat := 1561908535730231153735995

theorem tailTrace_3041806 : CollatzResearch.WordTrace tailWord_3041806 prefixEnd_3041806 1561908535730231153735995 := by
  unfold tailWord_3041806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867972402257979493809159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73962519478709223966982181 13867972402257979493809159)
  ·
    refine ⟨20801958603386969240713739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13867972402257979493809159 20801958603386969240713739)
    ·
      refine ⟨31202937905080453861070609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20801958603386969240713739 31202937905080453861070609)
      ·
        refine ⟨23402203428810340395802957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31202937905080453861070609 23402203428810340395802957)
        ·
          refine ⟨8775826285803877648426109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23402203428810340395802957 8775826285803877648426109)
          ·
            refine ⟨3290934857176454118159791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8775826285803877648426109 3290934857176454118159791)
            ·
              refine ⟨4936402285764681177239687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290934857176454118159791 4936402285764681177239687)
              ·
                refine ⟨7404603428647021765859531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936402285764681177239687 7404603428647021765859531)
                ·
                  refine ⟨11106905142970532648789297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7404603428647021765859531 11106905142970532648789297)
                  ·
                    refine ⟨8330178857227899486591973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11106905142970532648789297 8330178857227899486591973)
                    ·
                      refine ⟨1561908535730231153735995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8330178857227899486591973 1561908535730231153735995)
                      ·
                        rfl

theorem cell23_3041806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3041806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041806 prefixEnd_3041806 := by exact prefixLift 3041806
  have htrace : WordTrace (prefixWord ++ tailWord_3041806) baseStart_3041806 baseEnd_3041806 := by
    simpa [prefixWord, tailWord_3041806, baseEnd_3041806] using wordTrace_append hprefix tailTrace_3041806
  have hstable : (prefixWord ++ tailWord_3041806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041806).length < 2 ^ (prefixWord ++ tailWord_3041806).sum := by decide
  have hdescent : baseEnd_3041806 < baseStart_3041806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041842 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3041842 : Nat := 118140960795 + 3041842 * 2 ^ 59
def prefixEnd_3041842 : Nat := 4983230072969 + 3 ^ 40 * 3041842 * 2
def baseEnd_3041842 : Nat := 520642340344597670961943

theorem tailTrace_3041842 : CollatzResearch.WordTrace tailWord_3041842 prefixEnd_3041842 520642340344597670961943 := by
  unfold tailWord_3041842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27736273061483353524695945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73963394830622276065855853 27736273061483353524695945)
  ·
    refine ⟨20802204796112515143521959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27736273061483353524695945 20802204796112515143521959)
    ·
      refine ⟨31203307194168772715282939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20802204796112515143521959 31203307194168772715282939)
      ·
        refine ⟨46804960791253159072924409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31203307194168772715282939 46804960791253159072924409)
        ·
          refine ⟨35103720593439869304693307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46804960791253159072924409 35103720593439869304693307)
          ·
            refine ⟨52655580890159803957039961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35103720593439869304693307 52655580890159803957039961)
            ·
              refine ⟨39491685667619852967779971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52655580890159803957039961 39491685667619852967779971)
              ·
                refine ⟨59237528501429779451669957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39491685667619852967779971 59237528501429779451669957)
                ·
                  refine ⟨11107036594018083647188117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59237528501429779451669957 11107036594018083647188117)
                  ·
                    refine ⟨520642340344597670961943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11107036594018083647188117 520642340344597670961943)
                    ·
                      rfl

theorem cell23_3041842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3041842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041842 prefixEnd_3041842 := by exact prefixLift 3041842
  have htrace : WordTrace (prefixWord ++ tailWord_3041842) baseStart_3041842 baseEnd_3041842 := by
    simpa [prefixWord, tailWord_3041842, baseEnd_3041842] using wordTrace_append hprefix tailTrace_3041842
  have hstable : (prefixWord ++ tailWord_3041842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041842).length < 2 ^ (prefixWord ++ tailWord_3041842).sum := by decide
  have hdescent : baseEnd_3041842 < baseStart_3041842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041844 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3041844 : Nat := 118140960795 + 3041844 * 2 ^ 59
def prefixEnd_3041844 : Nat := 4983230072969 + 3 ^ 40 * 3041844 * 2
def baseEnd_3041844 : Nat := 1561928047995102005060821

theorem tailTrace_3041844 : CollatzResearch.WordTrace tailWord_3041844 prefixEnd_3041844 1561928047995102005060821 := by
  unfold tailWord_3041844
  simp only [CollatzResearch.WordTrace]
  refine ⟨55472582595963084220178293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73963443461284112293571057 55472582595963084220178293)
  ·
    refine ⟨5200554618371539145641715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55472582595963084220178293 5200554618371539145641715)
    ·
      refine ⟨7800831927557308718462573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200554618371539145641715 7800831927557308718462573)
      ·
        refine ⟨2925311972833990769423465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7800831927557308718462573 2925311972833990769423465)
        ·
          refine ⟨2193983979625493077067599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925311972833990769423465 2193983979625493077067599)
          ·
            refine ⟨3290975969438239615601399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193983979625493077067599 3290975969438239615601399)
            ·
              refine ⟨4936463954157359423402099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290975969438239615601399 4936463954157359423402099)
              ·
                refine ⟨7404695931236039135103149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936463954157359423402099 7404695931236039135103149)
                ·
                  refine ⟨2776760974213514675663681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7404695931236039135103149 2776760974213514675663681)
                  ·
                    refine ⟨2082570730660136006747761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2776760974213514675663681 2082570730660136006747761)
                    ·
                      refine ⟨1561928047995102005060821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082570730660136006747761 1561928047995102005060821)
                      ·
                        rfl

theorem cell23_3041844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3041844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041844 prefixEnd_3041844 := by exact prefixLift 3041844
  have htrace : WordTrace (prefixWord ++ tailWord_3041844) baseStart_3041844 baseEnd_3041844 := by
    simpa [prefixWord, tailWord_3041844, baseEnd_3041844] using wordTrace_append hprefix tailTrace_3041844
  have hstable : (prefixWord ++ tailWord_3041844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041844).length < 2 ^ (prefixWord ++ tailWord_3041844).sum := by decide
  have hdescent : baseEnd_3041844 < baseStart_3041844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041932 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_3041932 : Nat := 118140960795 + 3041932 * 2 ^ 59
def prefixEnd_3041932 : Nat := 4983230072969 + 3 ^ 40 * 3041932 * 2
def baseEnd_3041932 : Nat := 520657744764232553586805

theorem tailTrace_3041932 : CollatzResearch.WordTrace tailWord_3041932 prefixEnd_3041932 520657744764232553586805 := by
  unfold tailWord_3041932
  simp only [CollatzResearch.WordTrace]
  refine ⟨55474187407803679734780025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73965583210404906313040033 55474187407803679734780025)
  ·
    refine ⟨41605640555852759801085019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55474187407803679734780025 41605640555852759801085019)
    ·
      refine ⟨62408460833779139701627529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41605640555852759801085019 62408460833779139701627529)
      ·
        refine ⟨46806345625334354776220647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62408460833779139701627529 46806345625334354776220647)
        ·
          refine ⟨70209518438001532164330971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46806345625334354776220647 70209518438001532164330971)
          ·
            refine ⟨105314277657002298246496457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70209518438001532164330971 105314277657002298246496457)
            ·
              refine ⟨78985708242751723684872343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105314277657002298246496457 78985708242751723684872343)
              ·
                refine ⟨118478562364127585527308515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78985708242751723684872343 118478562364127585527308515)
                ·
                  refine ⟨177717843546191378290962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118478562364127585527308515 177717843546191378290962773)
                  ·
                    refine ⟨520657744764232553586805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 177717843546191378290962773 520657744764232553586805)
                    ·
                      rfl

theorem cell23_3041932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_3041932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041932 prefixEnd_3041932 := by exact prefixLift 3041932
  have htrace : WordTrace (prefixWord ++ tailWord_3041932) baseStart_3041932 baseEnd_3041932 := by
    simpa [prefixWord, tailWord_3041932, baseEnd_3041932] using wordTrace_append hprefix tailTrace_3041932
  have hstable : (prefixWord ++ tailWord_3041932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041932).length < 2 ^ (prefixWord ++ tailWord_3041932).sum := by decide
  have hdescent : baseEnd_3041932 < baseStart_3041932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041956 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_3041956 : Nat := 118140960795 + 3041956 * 2 ^ 59
def prefixEnd_3041956 : Nat := 4983230072969 + 3 ^ 40 * 3041956 * 2
def baseEnd_3041956 : Nat := 1561985557828405566860305

theorem tailTrace_3041956 : CollatzResearch.WordTrace tailWord_3041956 prefixEnd_3041956 1561985557828405566860305 := by
  unfold tailWord_3041956
  simp only [CollatzResearch.WordTrace]
  refine ⟨55474625083760205784216861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73966166778346941045622481 55474625083760205784216861)
  ·
    refine ⟨20802984406410077169081323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55474625083760205784216861 20802984406410077169081323)
    ·
      refine ⟨31204476609615115753621985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20802984406410077169081323 31204476609615115753621985)
      ·
        refine ⟨23403357457211336815216489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31204476609615115753621985 23403357457211336815216489)
        ·
          refine ⟨17552518092908502611412367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23403357457211336815216489 17552518092908502611412367)
          ·
            refine ⟨26328777139362753917118551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17552518092908502611412367 26328777139362753917118551)
            ·
              refine ⟨39493165709044130875677827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26328777139362753917118551 39493165709044130875677827)
              ·
                refine ⟨59239748563566196313516741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39493165709044130875677827 59239748563566196313516741)
                ·
                  refine ⟨11107452855668661808784389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59239748563566196313516741 11107452855668661808784389)
                  ·
                    refine ⟨2082647410437874089147073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11107452855668661808784389 2082647410437874089147073)
                    ·
                      refine ⟨1561985557828405566860305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082647410437874089147073 1561985557828405566860305)
                      ·
                        rfl

theorem cell23_3041956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_3041956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041956 prefixEnd_3041956 := by exact prefixLift 3041956
  have htrace : WordTrace (prefixWord ++ tailWord_3041956) baseStart_3041956 baseEnd_3041956 := by
    simpa [prefixWord, tailWord_3041956, baseEnd_3041956] using wordTrace_append hprefix tailTrace_3041956
  have hstable : (prefixWord ++ tailWord_3041956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041956).length < 2 ^ (prefixWord ++ tailWord_3041956).sum := by decide
  have hdescent : baseEnd_3041956 < baseStart_3041956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041973 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3041973 : Nat := 118140960795 + 3041973 * 2 ^ 59
def prefixEnd_3041973 : Nat := 4983230072969 + 3 ^ 40 * 3041973 * 2
def baseEnd_3041973 : Nat := 1561994286999532000347727

theorem tailTrace_3041973 : CollatzResearch.WordTrace tailWord_3041973 prefixEnd_3041973 1561994286999532000347727 := by
  unfold tailWord_3041973
  simp only [CollatzResearch.WordTrace]
  refine ⟨110949870208458823471802573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73966580138972548981201715 110949870208458823471802573)
  ·
    refine ⟨41606201328172058801925965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110949870208458823471802573 41606201328172058801925965)
    ·
      refine ⟨15602325498064522050722237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41606201328172058801925965 15602325498064522050722237)
      ·
        refine ⟨5850872061774195769020839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15602325498064522050722237 5850872061774195769020839)
        ·
          refine ⟨8776308092661293653531259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850872061774195769020839 8776308092661293653531259)
          ·
            refine ⟨13164462138991940480296889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776308092661293653531259 13164462138991940480296889)
            ·
              refine ⟨9873346604243955360222667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13164462138991940480296889 9873346604243955360222667)
              ·
                refine ⟨14810019906365933040334001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873346604243955360222667 14810019906365933040334001)
                ·
                  refine ⟨11107514929774449780250501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14810019906365933040334001 11107514929774449780250501)
                  ·
                    refine ⟨2082659049332709333796969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11107514929774449780250501 2082659049332709333796969)
                    ·
                      refine ⟨1561994286999532000347727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082659049332709333796969 1561994286999532000347727)
                      ·
                        rfl

theorem cell23_3041973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3041973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3041973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3041973 prefixEnd_3041973 := by exact prefixLift 3041973
  have htrace : WordTrace (prefixWord ++ tailWord_3041973) baseStart_3041973 baseEnd_3041973 := by
    simpa [prefixWord, tailWord_3041973, baseEnd_3041973] using wordTrace_append hprefix tailTrace_3041973
  have hstable : (prefixWord ++ tailWord_3041973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041973).length < 2 ^ (prefixWord ++ tailWord_3041973).sum := by decide
  have hdescent : baseEnd_3041973 < baseStart_3041973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042039 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 1, 6]
def baseStart_3042039 : Nat := 118140960795 + 3042039 * 2 ^ 59
def prefixEnd_3042039 : Nat := 4983230072969 + 3 ^ 40 * 3042039 * 2
def baseEnd_3042039 : Nat := 520676058907576247374141

theorem tailTrace_3042039 : CollatzResearch.WordTrace tailWord_3042039 prefixEnd_3042039 520676058907576247374141 := by
  unfold tailWord_3042039
  simp only [CollatzResearch.WordTrace]
  refine ⟨110952277426219716743705171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73968184950813144495803447 110952277426219716743705171)
  ·
    refine ⟨166428416139329575115557757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110952277426219716743705171 166428416139329575115557757)
    ·
      refine ⟨62410656052248590668334159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166428416139329575115557757 62410656052248590668334159)
      ·
        refine ⟨93615984078372886002501239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62410656052248590668334159 93615984078372886002501239)
        ·
          refine ⟨140423976117559329003751859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93615984078372886002501239 140423976117559329003751859)
          ·
            refine ⟨210635964176338993505627789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140423976117559329003751859 210635964176338993505627789)
            ·
              refine ⟨78988486566127122564610421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210635964176338993505627789 78988486566127122564610421)
              ·
                refine ⟨7405170615574417740432227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78988486566127122564610421 7405170615574417740432227)
                ·
                  refine ⟨11107755923361626610648341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405170615574417740432227 11107755923361626610648341)
                  ·
                    refine ⟨520676058907576247374141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11107755923361626610648341 520676058907576247374141)
                    ·
                      rfl

theorem cell23_3042039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_3042039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042039 prefixEnd_3042039 := by exact prefixLift 3042039
  have htrace : WordTrace (prefixWord ++ tailWord_3042039) baseStart_3042039 baseEnd_3042039 := by
    simpa [prefixWord, tailWord_3042039, baseEnd_3042039] using wordTrace_append hprefix tailTrace_3042039
  have hstable : (prefixWord ++ tailWord_3042039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042039).length < 2 ^ (prefixWord ++ tailWord_3042039).sum := by decide
  have hdescent : baseEnd_3042039 < baseStart_3042039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042050 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3042050 : Nat := 118140960795 + 3042050 * 2 ^ 59
def prefixEnd_3042050 : Nat := 4983230072969 + 3 ^ 40 * 3042050 * 2
def baseEnd_3042050 : Nat := 1562033825009928199084873

theorem tailTrace_3042050 : CollatzResearch.WordTrace tailWord_3042050 prefixEnd_3042050 1562033825009928199084873 := by
  unfold tailWord_3042050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27738169657294966405588901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73968452419453243748237069 27738169657294966405588901)
  ·
    refine ⟨5200906810742806201047919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27738169657294966405588901 5200906810742806201047919)
    ·
      refine ⟨7801360216114209301571879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200906810742806201047919 7801360216114209301571879)
      ·
        refine ⟨11702040324171313952357819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801360216114209301571879 11702040324171313952357819)
        ·
          refine ⟨17553060486256970928536729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11702040324171313952357819 17553060486256970928536729)
          ·
            refine ⟨13164795364692728196402547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17553060486256970928536729 13164795364692728196402547)
            ·
              refine ⟨19747193047039092294603821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13164795364692728196402547 19747193047039092294603821)
              ·
                refine ⟨7405197392639659610476433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19747193047039092294603821 7405197392639659610476433)
                ·
                  refine ⟨5553898044479744707857325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7405197392639659610476433 5553898044479744707857325)
                  ·
                    refine ⟨2082711766679904265446497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5553898044479744707857325 2082711766679904265446497)
                    ·
                      refine ⟨1562033825009928199084873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082711766679904265446497 1562033825009928199084873)
                      ·
                        rfl

theorem cell23_3042050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3042050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042050 prefixEnd_3042050 := by exact prefixLift 3042050
  have htrace : WordTrace (prefixWord ++ tailWord_3042050) baseStart_3042050 baseEnd_3042050 := by
    simpa [prefixWord, tailWord_3042050, baseEnd_3042050] using wordTrace_append hprefix tailTrace_3042050
  have hstable : (prefixWord ++ tailWord_3042050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042050).length < 2 ^ (prefixWord ++ tailWord_3042050).sum := by decide
  have hdescent : baseEnd_3042050 < baseStart_3042050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042056 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_3042056 : Nat := 118140960795 + 3042056 * 2 ^ 59
def prefixEnd_3042056 : Nat := 4983230072969 + 3 ^ 40 * 3042056 * 2
def baseEnd_3042056 : Nat := 520678968631285058536615

theorem tailTrace_3042056 : CollatzResearch.WordTrace tailWord_3042056 prefixEnd_3042056 520678968631285058536615 := by
  unfold tailWord_3042056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55476448733579064323537011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73968598311438752431382681 55476448733579064323537011)
  ·
    refine ⟨83214673100368596485305517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55476448733579064323537011 83214673100368596485305517)
    ·
      refine ⟨31205502412638223681989569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83214673100368596485305517 31205502412638223681989569)
      ·
        refine ⟨23404126809478667761492177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31205502412638223681989569 23404126809478667761492177)
        ·
          refine ⟨17553095107109000821119133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23404126809478667761492177 17553095107109000821119133)
          ·
            refine ⟨6582410665165875307919675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17553095107109000821119133 6582410665165875307919675)
            ·
              refine ⟨9873615997748812961879513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582410665165875307919675 9873615997748812961879513)
              ·
                refine ⟨7405211998311609721409635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9873615997748812961879513 7405211998311609721409635)
                ·
                  refine ⟨11107817997467414582114453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405211998311609721409635 11107817997467414582114453)
                  ·
                    refine ⟨520678968631285058536615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11107817997467414582114453 520678968631285058536615)
                    ·
                      rfl

theorem cell23_3042056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_3042056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042056 prefixEnd_3042056 := by exact prefixLift 3042056
  have htrace : WordTrace (prefixWord ++ tailWord_3042056) baseStart_3042056 baseEnd_3042056 := by
    simpa [prefixWord, tailWord_3042056, baseEnd_3042056] using wordTrace_append hprefix tailTrace_3042056
  have hstable : (prefixWord ++ tailWord_3042056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042056).length < 2 ^ (prefixWord ++ tailWord_3042056).sum := by decide
  have hdescent : baseEnd_3042056 < baseStart_3042056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042063 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 1, 1, 4]
def baseStart_3042063 : Nat := 118140960795 + 3042063 * 2 ^ 59
def prefixEnd_3042063 : Nat := 4983230072969 + 3 ^ 40 * 3042063 * 2
def baseEnd_3042063 : Nat := 1562040500258436648222313

theorem tailTrace_3042063 : CollatzResearch.WordTrace tailWord_3042063 prefixEnd_3042063 1562040500258436648222313 := by
  unfold tailWord_3042063
  simp only [CollatzResearch.WordTrace]
  refine ⟨110953152778132768842578843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73968768518755179228385895 110953152778132768842578843)
  ·
    refine ⟨166429729167199153263868265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110953152778132768842578843 166429729167199153263868265)
    ·
      refine ⟨124822296875399364947901199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166429729167199153263868265 124822296875399364947901199)
      ·
        refine ⟨187233445313099047421851799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124822296875399364947901199 187233445313099047421851799)
        ·
          refine ⟨280850167969648571132777699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187233445313099047421851799 280850167969648571132777699)
          ·
            refine ⟨421275251954472856699166549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280850167969648571132777699 421275251954472856699166549)
            ·
              refine ⟨2468409679420739394721679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 421275251954472856699166549 2468409679420739394721679)
              ·
                refine ⟨3702614519131109092082519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468409679420739394721679 3702614519131109092082519)
                ·
                  refine ⟨5553921778696663638123779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702614519131109092082519 5553921778696663638123779)
                  ·
                    refine ⟨8330882668044995457185669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553921778696663638123779 8330882668044995457185669)
                    ·
                      refine ⟨1562040500258436648222313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8330882668044995457185669 1562040500258436648222313)
                      ·
                        rfl

theorem cell23_3042063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 1, 4].length) (baseStart_3042063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042063 prefixEnd_3042063 := by exact prefixLift 3042063
  have htrace : WordTrace (prefixWord ++ tailWord_3042063) baseStart_3042063 baseEnd_3042063 := by
    simpa [prefixWord, tailWord_3042063, baseEnd_3042063] using wordTrace_append hprefix tailTrace_3042063
  have hstable : (prefixWord ++ tailWord_3042063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042063).length < 2 ^ (prefixWord ++ tailWord_3042063).sum := by decide
  have hdescent : baseEnd_3042063 < baseStart_3042063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042090 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3042090 : Nat := 118140960795 + 3042090 * 2 ^ 59
def prefixEnd_3042090 : Nat := 4983230072969 + 3 ^ 40 * 3042090 * 2
def baseEnd_3042090 : Nat := 520684788078702680861563

theorem tailTrace_3042090 : CollatzResearch.WordTrace tailWord_3042090 prefixEnd_3042090 520684788078702680861563 := by
  unfold tailWord_3042090
  simp only [CollatzResearch.WordTrace]
  refine ⟨27738534387258738113452931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73969425032689968302541149 27738534387258738113452931)
  ·
    refine ⟨41607801580888107170179397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27738534387258738113452931 41607801580888107170179397)
    ·
      refine ⟨7801462796416520094408637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41607801580888107170179397 7801462796416520094408637)
      ·
        refine ⟨2925548548656195035403239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7801462796416520094408637 2925548548656195035403239)
        ·
          refine ⟨4388322822984292553104859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925548548656195035403239 4388322822984292553104859)
          ·
            refine ⟨6582484234476438829657289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388322822984292553104859 6582484234476438829657289)
            ·
              refine ⟨4936863175857329122242967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6582484234476438829657289 4936863175857329122242967)
              ·
                refine ⟨7405294763785993683364451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936863175857329122242967 7405294763785993683364451)
                ·
                  refine ⟨11107942145678990525046677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405294763785993683364451 11107942145678990525046677)
                  ·
                    refine ⟨520684788078702680861563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11107942145678990525046677 520684788078702680861563)
                    ·
                      rfl

theorem cell23_3042090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3042090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042090 prefixEnd_3042090 := by exact prefixLift 3042090
  have htrace : WordTrace (prefixWord ++ tailWord_3042090) baseStart_3042090 baseEnd_3042090 := by
    simpa [prefixWord, tailWord_3042090, baseEnd_3042090] using wordTrace_append hprefix tailTrace_3042090
  have hstable : (prefixWord ++ tailWord_3042090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042090).length < 2 ^ (prefixWord ++ tailWord_3042090).sum := by decide
  have hdescent : baseEnd_3042090 < baseStart_3042090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042147 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 2, 1, 3]
def baseStart_3042147 : Nat := 118140960795 + 3042147 * 2 ^ 59
def prefixEnd_3042147 : Nat := 4983230072969 + 3 ^ 40 * 3042147 * 2
def baseEnd_3042147 : Nat := 1562083632633414319571927

theorem tailTrace_3042147 : CollatzResearch.WordTrace tailWord_3042147 prefixEnd_3042147 1562083632633414319571927 := by
  unfold tailWord_3042147
  simp only [CollatzResearch.WordTrace]
  refine ⟨110956216509828451188636695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73970811006552300792424463 110956216509828451188636695)
  ·
    refine ⟨166434324764742676782955043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110956216509828451188636695 166434324764742676782955043)
    ·
      refine ⟨249651487147114015174432565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166434324764742676782955043 249651487147114015174432565)
      ·
        refine ⟨23404826920041938922603053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249651487147114015174432565 23404826920041938922603053)
        ·
          refine ⟨8776810095015727095976145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23404826920041938922603053 8776810095015727095976145)
          ·
            refine ⟨6582607571261795321982109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8776810095015727095976145 6582607571261795321982109)
            ·
              refine ⟨2468477839223173245743291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6582607571261795321982109 2468477839223173245743291)
              ·
                refine ⟨3702716758834759868614937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468477839223173245743291 3702716758834759868614937)
                ·
                  refine ⟨2777037569126069901461203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702716758834759868614937 2777037569126069901461203)
                  ·
                    refine ⟨4165556353689104852191805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777037569126069901461203 4165556353689104852191805)
                    ·
                      refine ⟨1562083632633414319571927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165556353689104852191805 1562083632633414319571927)
                      ·
                        rfl

theorem cell23_3042147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_3042147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042147 prefixEnd_3042147 := by exact prefixLift 3042147
  have htrace : WordTrace (prefixWord ++ tailWord_3042147) baseStart_3042147 baseEnd_3042147 := by
    simpa [prefixWord, tailWord_3042147, baseEnd_3042147] using wordTrace_append hprefix tailTrace_3042147
  have hstable : (prefixWord ++ tailWord_3042147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042147).length < 2 ^ (prefixWord ++ tailWord_3042147).sum := by decide
  have hdescent : baseEnd_3042147 < baseStart_3042147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042156 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3042156 : Nat := 118140960795 + 3042156 * 2 ^ 59
def prefixEnd_3042156 : Nat := 4983230072969 + 3 ^ 40 * 3042156 * 2
def baseEnd_3042156 : Nat := 1562088253959304784359385

theorem tailTrace_3042156 : CollatzResearch.WordTrace tailWord_3042156 prefixEnd_3042156 1562088253959304784359385 := by
  unfold tailWord_3042156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55478272383397922862857161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73971029844530563817142881 55478272383397922862857161)
  ·
    refine ⟨41608704287548442147142871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55478272383397922862857161 41608704287548442147142871)
    ·
      refine ⟨62413056431322663220714307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41608704287548442147142871 62413056431322663220714307)
      ·
        refine ⟨93619584646983994831071461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62413056431322663220714307 93619584646983994831071461)
        ·
          refine ⟨17553672121309499030825899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93619584646983994831071461 17553672121309499030825899)
          ·
            refine ⟨26330508181964248546238849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17553672121309499030825899 26330508181964248546238849)
            ·
              refine ⟨19747881136473186409679137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26330508181964248546238849 19747881136473186409679137)
              ·
                refine ⟨14810910852354889807259353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19747881136473186409679137 14810910852354889807259353)
                ·
                  refine ⟨11108183139266167355444515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14810910852354889807259353 11108183139266167355444515)
                  ·
                    refine ⟨16662274708899251033166773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11108183139266167355444515 16662274708899251033166773)
                    ·
                      refine ⟨1562088253959304784359385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16662274708899251033166773 1562088253959304784359385)
                      ·
                        rfl

theorem cell23_3042156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3042156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042156 prefixEnd_3042156 := by exact prefixLift 3042156
  have htrace : WordTrace (prefixWord ++ tailWord_3042156) baseStart_3042156 baseEnd_3042156 := by
    simpa [prefixWord, tailWord_3042156, baseEnd_3042156] using wordTrace_append hprefix tailTrace_3042156
  have hstable : (prefixWord ++ tailWord_3042156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042156).length < 2 ^ (prefixWord ++ tailWord_3042156).sum := by decide
  have hdescent : baseEnd_3042156 < baseStart_3042156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042198 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3042198 : Nat := 118140960795 + 3042198 * 2 ^ 59
def prefixEnd_3042198 : Nat := 4983230072969 + 3 ^ 40 * 3042198 * 2
def baseEnd_3042198 : Nat := 1562109820146793620034193

theorem tailTrace_3042198 : CollatzResearch.WordTrace tailWord_3042198 prefixEnd_3042198 1562109820146793620034193 := by
  unfold tailWord_3042198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934879789540230431171453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73972051088429124599162165 6934879789540230431171453)
  ·
    refine ⟨2600579921077586411689295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6934879789540230431171453 2600579921077586411689295)
    ·
      refine ⟨3900869881616379617533943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600579921077586411689295 3900869881616379617533943)
      ·
        refine ⟨5851304822424569426300915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900869881616379617533943 5851304822424569426300915)
        ·
          refine ⟨8776957233636854139451373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851304822424569426300915 8776957233636854139451373)
          ·
            refine ⟨3291358962613820302294265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8776957233636854139451373 3291358962613820302294265)
            ·
              refine ⟨2468519221960365226720699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291358962613820302294265 2468519221960365226720699)
              ·
                refine ⟨3702778832940547840081049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468519221960365226720699 3702778832940547840081049)
                ·
                  refine ⟨2777084124705410880060787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702778832940547840081049 2777084124705410880060787)
                  ·
                    refine ⟨4165626187058116320091181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777084124705410880060787 4165626187058116320091181)
                    ·
                      refine ⟨1562109820146793620034193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165626187058116320091181 1562109820146793620034193)
                      ·
                        rfl

theorem cell23_3042198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3042198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042198 prefixEnd_3042198 := by exact prefixLift 3042198
  have htrace : WordTrace (prefixWord ++ tailWord_3042198) baseStart_3042198 baseEnd_3042198 := by
    simpa [prefixWord, tailWord_3042198, baseEnd_3042198] using wordTrace_append hprefix tailTrace_3042198
  have hstable : (prefixWord ++ tailWord_3042198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042198).length < 2 ^ (prefixWord ++ tailWord_3042198).sum := by decide
  have hdescent : baseEnd_3042198 < baseStart_3042198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042204 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3042204 : Nat := 118140960795 + 3042204 * 2 ^ 59
def prefixEnd_3042204 : Nat := 4983230072969 + 3 ^ 40 * 3042204 * 2
def baseEnd_3042204 : Nat := 1562112901030720596559165

theorem tailTrace_3042204 : CollatzResearch.WordTrace tailWord_3042204 prefixEnd_3042204 1562112901030720596559165 := by
  unfold tailWord_3042204
  simp only [CollatzResearch.WordTrace]
  refine ⟨55479147735310974961730833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73972196980414633282307777 55479147735310974961730833)
  ·
    refine ⟨41609360801483231221298125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55479147735310974961730833 41609360801483231221298125)
    ·
      refine ⟨15603510300556211707986797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41609360801483231221298125 15603510300556211707986797)
      ·
        refine ⟨5851316362708579390495049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15603510300556211707986797 5851316362708579390495049)
        ·
          refine ⟨4388487272031434542871287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5851316362708579390495049 4388487272031434542871287)
          ·
            refine ⟨6582730908047151814306931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388487272031434542871287 6582730908047151814306931)
            ·
              refine ⟨9874096362070727721460397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582730908047151814306931 9874096362070727721460397)
              ·
                refine ⟨3702786135776522895547649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9874096362070727721460397 3702786135776522895547649)
                ·
                  refine ⟨2777089601832392171660737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702786135776522895547649 2777089601832392171660737)
                  ·
                    refine ⟨2082817201374294128745553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2777089601832392171660737 2082817201374294128745553)
                    ·
                      refine ⟨1562112901030720596559165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082817201374294128745553 1562112901030720596559165)
                      ·
                        rfl

theorem cell23_3042204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3042204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042204 prefixEnd_3042204 := by exact prefixLift 3042204
  have htrace : WordTrace (prefixWord ++ tailWord_3042204) baseStart_3042204 baseEnd_3042204 := by
    simpa [prefixWord, tailWord_3042204, baseEnd_3042204] using wordTrace_append hprefix tailTrace_3042204
  have hstable : (prefixWord ++ tailWord_3042204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042204).length < 2 ^ (prefixWord ++ tailWord_3042204).sum := by decide
  have hdescent : baseEnd_3042204 < baseStart_3042204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042243 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 4, 4, 2]
def baseStart_3042243 : Nat := 118140960795 + 3042243 * 2 ^ 59
def prefixEnd_3042243 : Nat := 4983230072969 + 3 ^ 40 * 3042243 * 2
def baseEnd_3042243 : Nat := 1562132926776245943971485

theorem tailTrace_3042243 : CollatzResearch.WordTrace tailWord_3042243 prefixEnd_3042243 1562132926776245943971485 := by
  unfold tailWord_3042243
  simp only [CollatzResearch.WordTrace]
  refine ⟨110959717917480659584131383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73973145278320439722754255 110959717917480659584131383)
  ·
    refine ⟨166439576876220989376197075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110959717917480659584131383 166439576876220989376197075)
    ·
      refine ⟨249659365314331484064295613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166439576876220989376197075 249659365314331484064295613)
      ·
        refine ⟨93622261992874306524110855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249659365314331484064295613 93622261992874306524110855)
        ·
          refine ⟨140433392989311459786166283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93622261992874306524110855 140433392989311459786166283)
          ·
            refine ⟨210650089483967189679249425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140433392989311459786166283 210650089483967189679249425)
            ·
              refine ⟨157987567112975392259437069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210650089483967189679249425 157987567112975392259437069)
              ·
                refine ⟨59245337667365772097288901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157987567112975392259437069 59245337667365772097288901)
                ·
                  refine ⟨11108500812631082268241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59245337667365772097288901 11108500812631082268241669)
                  ·
                    refine ⟨2082843902368327925295313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11108500812631082268241669 2082843902368327925295313)
                    ·
                      refine ⟨1562132926776245943971485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082843902368327925295313 1562132926776245943971485)
                      ·
                        rfl

theorem cell23_3042243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_3042243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042243 prefixEnd_3042243 := by exact prefixLift 3042243
  have htrace : WordTrace (prefixWord ++ tailWord_3042243) baseStart_3042243 baseEnd_3042243 := by
    simpa [prefixWord, tailWord_3042243, baseEnd_3042243] using wordTrace_append hprefix tailTrace_3042243
  have hstable : (prefixWord ++ tailWord_3042243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042243).length < 2 ^ (prefixWord ++ tailWord_3042243).sum := by decide
  have hdescent : baseEnd_3042243 < baseStart_3042243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042256 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_3042256 : Nat := 118140960795 + 3042256 * 2 ^ 59
def prefixEnd_3042256 : Nat := 4983230072969 + 3 ^ 40 * 3042256 * 2
def baseEnd_3042256 : Nat := 1562139602024754393108925

theorem tailTrace_3042256 : CollatzResearch.WordTrace tailWord_3042256 prefixEnd_3042256 1562139602024754393108925 := by
  unfold tailWord_3042256
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480096033216781402177311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73973461377622375202903081 55480096033216781402177311)
  ·
    refine ⟨83220144049825172103265967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55480096033216781402177311 83220144049825172103265967)
    ·
      refine ⟨124830216074737758154898951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83220144049825172103265967 124830216074737758154898951)
      ·
        refine ⟨187245324112106637232348427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124830216074737758154898951 187245324112106637232348427)
        ·
          refine ⟨280867986168159955848522641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187245324112106637232348427 280867986168159955848522641)
          ·
            refine ⟨210650989626119966886391981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280867986168159955848522641 210650989626119966886391981)
            ·
              refine ⟨78994121109794987582396993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210650989626119966886391981 78994121109794987582396993)
              ·
                refine ⟨59245590832346240686797745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78994121109794987582396993 59245590832346240686797745)
                ·
                  refine ⟨44434193124259680515098309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59245590832346240686797745 44434193124259680515098309)
                  ·
                    refine ⟨8331411210798690096580933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44434193124259680515098309 8331411210798690096580933)
                    ·
                      refine ⟨1562139602024754393108925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8331411210798690096580933 1562139602024754393108925)
                      ·
                        rfl

theorem cell23_3042256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_3042256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042256 prefixEnd_3042256 := by exact prefixLift 3042256
  have htrace : WordTrace (prefixWord ++ tailWord_3042256) baseStart_3042256 baseEnd_3042256 := by
    simpa [prefixWord, tailWord_3042256, baseEnd_3042256] using wordTrace_append hprefix tailTrace_3042256
  have hstable : (prefixWord ++ tailWord_3042256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042256).length < 2 ^ (prefixWord ++ tailWord_3042256).sum := by decide
  have hdescent : baseEnd_3042256 < baseStart_3042256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042260 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3042260 : Nat := 118140960795 + 3042260 * 2 ^ 59
def prefixEnd_3042260 : Nat := 4983230072969 + 3 ^ 40 * 3042260 * 2
def baseEnd_3042260 : Nat := 1562141655947372377458907

theorem tailTrace_3042260 : CollatzResearch.WordTrace tailWord_3042260 prefixEnd_3042260 1562141655947372377458907 := by
  unfold tailWord_3042260
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480168979209535743750117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73973558638946047658333489 55480168979209535743750117)
  ·
    refine ⟨10402531683601787951953147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55480168979209535743750117 10402531683601787951953147)
    ·
      refine ⟨15603797525402681927929721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10402531683601787951953147 15603797525402681927929721)
      ·
        refine ⟨11702848144052011445947291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15603797525402681927929721 11702848144052011445947291)
        ·
          refine ⟨17554272216078017168920937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11702848144052011445947291 17554272216078017168920937)
          ·
            refine ⟨13165704162058512876690703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17554272216078017168920937 13165704162058512876690703)
            ·
              refine ⟨19748556243087769315036055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13165704162058512876690703 19748556243087769315036055)
              ·
                refine ⟨29622834364631653972554083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19748556243087769315036055 29622834364631653972554083)
                ·
                  refine ⟨44434251546947480958831125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29622834364631653972554083 44434251546947480958831125)
                  ·
                    refine ⟨2082855541263163169945209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44434251546947480958831125 2082855541263163169945209)
                    ·
                      refine ⟨1562141655947372377458907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2082855541263163169945209 1562141655947372377458907)
                      ·
                        rfl

theorem cell23_3042260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3042260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042260 prefixEnd_3042260 := by exact prefixLift 3042260
  have htrace : WordTrace (prefixWord ++ tailWord_3042260) baseStart_3042260 baseEnd_3042260 := by
    simpa [prefixWord, tailWord_3042260, baseEnd_3042260] using wordTrace_append hprefix tailTrace_3042260
  have hstable : (prefixWord ++ tailWord_3042260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042260).length < 2 ^ (prefixWord ++ tailWord_3042260).sum := by decide
  have hdescent : baseEnd_3042260 < baseStart_3042260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042280 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3042280 : Nat := 118140960795 + 3042280 * 2 ^ 59
def prefixEnd_3042280 : Nat := 4983230072969 + 3 ^ 40 * 3042280 * 2
def baseEnd_3042280 : Nat := 1562151925560462299208815

theorem tailTrace_3042280 : CollatzResearch.WordTrace tailWord_3042280 prefixEnd_3042280 1562151925560462299208815 := by
  unfold tailWord_3042280
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480533709173307451614147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73974044945564409935485529 55480533709173307451614147)
  ·
    refine ⟨83220800563759961177421221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55480533709173307451614147 83220800563759961177421221)
    ·
      refine ⟨15603900105704992720766479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83220800563759961177421221 15603900105704992720766479)
      ·
        refine ⟨23405850158557489081149719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15603900105704992720766479 23405850158557489081149719)
        ·
          refine ⟨35108775237836233621724579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23405850158557489081149719 35108775237836233621724579)
          ·
            refine ⟨52663162856754350432586869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35108775237836233621724579 52663162856754350432586869)
            ·
              refine ⟨4937171517820720353055019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52663162856754350432586869 4937171517820720353055019)
              ·
                refine ⟨7405757276731080529582529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937171517820720353055019 7405757276731080529582529)
                ·
                  refine ⟨5554317957548310397186897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7405757276731080529582529 5554317957548310397186897)
                  ·
                    refine ⟨4165738468161232797890173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5554317957548310397186897 4165738468161232797890173)
                    ·
                      refine ⟨1562151925560462299208815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165738468161232797890173 1562151925560462299208815)
                      ·
                        rfl

theorem cell23_3042280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3042280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042280 prefixEnd_3042280 := by exact prefixLift 3042280
  have htrace : WordTrace (prefixWord ++ tailWord_3042280) baseStart_3042280 baseEnd_3042280 := by
    simpa [prefixWord, tailWord_3042280, baseEnd_3042280] using wordTrace_append hprefix tailTrace_3042280
  have hstable : (prefixWord ++ tailWord_3042280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042280).length < 2 ^ (prefixWord ++ tailWord_3042280).sum := by decide
  have hdescent : baseEnd_3042280 < baseStart_3042280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042287 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 1, 4]
def baseStart_3042287 : Nat := 118140960795 + 3042287 * 2 ^ 59
def prefixEnd_3042287 : Nat := 4983230072969 + 3 ^ 40 * 3042287 * 2
def baseEnd_3042287 : Nat := 520718506641681257273761

theorem tailTrace_3042287 : CollatzResearch.WordTrace tailWord_3042287 prefixEnd_3042287 520718506641681257273761 := by
  unfold tailWord_3042287
  simp only [CollatzResearch.WordTrace]
  refine ⟨110961322729321255098733115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73974215152880836732488743 110961322729321255098733115)
  ·
    refine ⟨166441984093981882648099673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110961322729321255098733115 166441984093981882648099673)
    ·
      refine ⟨124831488070486411986074755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166441984093981882648099673 124831488070486411986074755)
      ·
        refine ⟨187247232105729617979112133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124831488070486411986074755 187247232105729617979112133)
        ·
          refine ⟨35108856019824303371083525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187247232105729617979112133 35108856019824303371083525)
          ·
            refine ⟨6582910503717056882078161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35108856019824303371083525 6582910503717056882078161)
            ·
              refine ⟨4937182877787792661558621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6582910503717056882078161 4937182877787792661558621)
              ·
                refine ⟨1851443579170422248084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4937182877787792661558621 1851443579170422248084483)
                ·
                  refine ⟨2777165368755633372126725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851443579170422248084483 2777165368755633372126725)
                  ·
                    refine ⟨520718506641681257273761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777165368755633372126725 520718506641681257273761)
                    ·
                      rfl

theorem cell23_3042287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 4].length) (baseStart_3042287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042287 prefixEnd_3042287 := by exact prefixLift 3042287
  have htrace : WordTrace (prefixWord ++ tailWord_3042287) baseStart_3042287 baseEnd_3042287 := by
    simpa [prefixWord, tailWord_3042287, baseEnd_3042287] using wordTrace_append hprefix tailTrace_3042287
  have hstable : (prefixWord ++ tailWord_3042287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042287).length < 2 ^ (prefixWord ++ tailWord_3042287).sum := by decide
  have hdescent : baseEnd_3042287 < baseStart_3042287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042300 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 6]
def baseStart_3042300 : Nat := 118140960795 + 3042300 * 2 ^ 59
def prefixEnd_3042300 : Nat := 4983230072969 + 3 ^ 40 * 3042300 * 2
def baseEnd_3042300 : Nat := 173573577241505802328747

theorem tailTrace_3042300 : CollatzResearch.WordTrace tailWord_3042300 prefixEnd_3042300 173573577241505802328747 := by
  unfold tailWord_3042300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480898439137079159478177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73974531252182772212637569 55480898439137079159478177)
  ·
    refine ⟨41610673829352809369608633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55480898439137079159478177 41610673829352809369608633)
    ·
      refine ⟨31208005372014607027206475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41610673829352809369608633 31208005372014607027206475)
      ·
        refine ⟨46812008058021910540809713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31208005372014607027206475 46812008058021910540809713)
        ·
          refine ⟨35109006043516432905607285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46812008058021910540809713 35109006043516432905607285)
          ·
            refine ⟨3291469316579665584900683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35109006043516432905607285 3291469316579665584900683)
            ·
              refine ⟨4937203974869498377351025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291469316579665584900683 4937203974869498377351025)
              ·
                refine ⟨3702902981152123783013269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937203974869498377351025 3702902981152123783013269)
                ·
                  refine ⟨173573577241505802328747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3702902981152123783013269 173573577241505802328747)
                  ·
                    rfl

theorem cell23_3042300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_3042300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042300 prefixEnd_3042300 := by exact prefixLift 3042300
  have htrace : WordTrace (prefixWord ++ tailWord_3042300) baseStart_3042300 baseEnd_3042300 := by
    simpa [prefixWord, tailWord_3042300, baseEnd_3042300] using wordTrace_append hprefix tailTrace_3042300
  have hstable : (prefixWord ++ tailWord_3042300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042300).length < 2 ^ (prefixWord ++ tailWord_3042300).sum := by decide
  have hdescent : baseEnd_3042300 < baseStart_3042300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042327 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3042327 : Nat := 118140960795 + 3042327 * 2 ^ 59
def prefixEnd_3042327 : Nat := 4983230072969 + 3 ^ 40 * 3042327 * 2
def baseEnd_3042327 : Nat := 1562176059151223615321099

theorem tailTrace_3042327 : CollatzResearch.WordTrace tailWord_3042327 prefixEnd_3042327 1562176059151223615321099 := by
  unfold tailWord_3042327
  simp only [CollatzResearch.WordTrace]
  refine ⟨110962781649176341930189235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73975187766117561286792823 110962781649176341930189235)
  ·
    refine ⟨166444172473764512895283853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110962781649176341930189235 166444172473764512895283853)
    ·
      refine ⟨62416564677661692335731445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166444172473764512895283853 62416564677661692335731445)
      ·
        refine ⟨5851552938530783656474823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62416564677661692335731445 5851552938530783656474823)
        ·
          refine ⟨8777329407796175484712235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851552938530783656474823 8777329407796175484712235)
          ·
            refine ⟨13165994111694263227068353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8777329407796175484712235 13165994111694263227068353)
            ·
              refine ⟨9874495583770697420301265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13165994111694263227068353 9874495583770697420301265)
              ·
                refine ⟨7405871687828023065225949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874495583770697420301265 7405871687828023065225949)
                ·
                  refine ⟨2777201882935508649459731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7405871687828023065225949 2777201882935508649459731)
                  ·
                    refine ⟨4165802824403262974189597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777201882935508649459731 4165802824403262974189597)
                    ·
                      refine ⟨1562176059151223615321099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165802824403262974189597 1562176059151223615321099)
                      ·
                        rfl

theorem cell23_3042327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3042327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042327 prefixEnd_3042327 := by exact prefixLift 3042327
  have htrace : WordTrace (prefixWord ++ tailWord_3042327) baseStart_3042327 baseEnd_3042327 := by
    simpa [prefixWord, tailWord_3042327, baseEnd_3042327] using wordTrace_append hprefix tailTrace_3042327
  have hstable : (prefixWord ++ tailWord_3042327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042327).length < 2 ^ (prefixWord ++ tailWord_3042327).sum := by decide
  have hdescent : baseEnd_3042327 < baseStart_3042327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042330 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_3042330 : Nat := 118140960795 + 3042330 * 2 ^ 59
def prefixEnd_3042330 : Nat := 4983230072969 + 3 ^ 40 * 3042330 * 2
def baseEnd_3042330 : Nat := 520725866531062367861195

theorem tailTrace_3042330 : CollatzResearch.WordTrace tailWord_3042330 prefixEnd_3042330 520725866531062367861195 := by
  unfold tailWord_3042330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27740722767041368360637111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73975260712110315628365629 27740722767041368360637111)
  ·
    refine ⟨41611084150562052540955667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27740722767041368360637111 41611084150562052540955667)
    ·
      refine ⟨62416626225843078811433501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41611084150562052540955667 62416626225843078811433501)
      ·
        refine ⟨23406234834691154554287563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62416626225843078811433501 23406234834691154554287563)
        ·
          refine ⟨35109352252036731831431345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23406234834691154554287563 35109352252036731831431345)
          ·
            refine ⟨26332014189027548873573509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35109352252036731831431345 26332014189027548873573509)
            ·
              refine ⟨4937252660442665413795033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26332014189027548873573509 4937252660442665413795033)
              ·
                refine ⟨3702939495331999060346275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937252660442665413795033 3702939495331999060346275)
                ·
                  refine ⟨5554409242997998590519413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702939495331999060346275 5554409242997998590519413)
                  ·
                    refine ⟨520725866531062367861195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5554409242997998590519413 520725866531062367861195)
                    ·
                      rfl

theorem cell23_3042330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_3042330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042330 prefixEnd_3042330 := by exact prefixLift 3042330
  have htrace : WordTrace (prefixWord ++ tailWord_3042330) baseStart_3042330 baseEnd_3042330 := by
    simpa [prefixWord, tailWord_3042330, baseEnd_3042330] using wordTrace_append hprefix tailTrace_3042330
  have hstable : (prefixWord ++ tailWord_3042330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042330).length < 2 ^ (prefixWord ++ tailWord_3042330).sum := by decide
  have hdescent : baseEnd_3042330 < baseStart_3042330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042360 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_3042360 : Nat := 118140960795 + 3042360 * 2 ^ 59
def prefixEnd_3042360 : Nat := 4983230072969 + 3 ^ 40 * 3042360 * 2
def baseEnd_3042360 : Nat := 520731001337607328736149

theorem tailTrace_3042360 : CollatzResearch.WordTrace tailWord_3042360 prefixEnd_3042360 520731001337607328736149 := by
  unfold tailWord_3042360
  simp only [CollatzResearch.WordTrace]
  refine ⟨55481992629028394283070267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73975990172037859044093689 55481992629028394283070267)
  ·
    refine ⟨83222988943542591424605401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55481992629028394283070267 83222988943542591424605401)
    ·
      refine ⟨62417241707656943568454051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83222988943542591424605401 62417241707656943568454051)
      ·
        refine ⟨93625862561485415352681077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62417241707656943568454051 93625862561485415352681077)
        ·
          refine ⟨8777424615139257689313851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93625862561485415352681077 8777424615139257689313851)
          ·
            refine ⟨13166136922708886533970777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8777424615139257689313851 13166136922708886533970777)
            ·
              refine ⟨9874602692031664900478083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13166136922708886533970777 9874602692031664900478083)
              ·
                refine ⟨14811904038047497350717125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9874602692031664900478083 14811904038047497350717125)
                ·
                  refine ⟨2777232007133905753259461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14811904038047497350717125 2777232007133905753259461)
                  ·
                    refine ⟨520731001337607328736149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777232007133905753259461 520731001337607328736149)
                    ·
                      rfl

theorem cell23_3042360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_3042360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042360 prefixEnd_3042360 := by exact prefixLift 3042360
  have htrace : WordTrace (prefixWord ++ tailWord_3042360) baseStart_3042360 baseEnd_3042360 := by
    simpa [prefixWord, tailWord_3042360, baseEnd_3042360] using wordTrace_append hprefix tailTrace_3042360
  have hstable : (prefixWord ++ tailWord_3042360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042360).length < 2 ^ (prefixWord ++ tailWord_3042360).sum := by decide
  have hdescent : baseEnd_3042360 < baseStart_3042360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042361 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3042361 : Nat := 118140960795 + 3042361 * 2 ^ 59
def prefixEnd_3042361 : Nat := 4983230072969 + 3 ^ 40 * 3042361 * 2
def baseEnd_3042361 : Nat := 1562193517493476482295943

theorem tailTrace_3042361 : CollatzResearch.WordTrace tailWord_3042361 prefixEnd_3042361 1562193517493476482295943 := by
  unfold tailWord_3042361
  simp only [CollatzResearch.WordTrace]
  refine ⟨110964021731053165736926937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73976014487368777157951291 110964021731053165736926937)
  ·
    refine ⟨83223016298289874302695203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110964021731053165736926937 83223016298289874302695203)
    ·
      refine ⟨124834524447434811454042805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83223016298289874302695203 124834524447434811454042805)
      ·
        refine ⟨11703236666947013573816513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124834524447434811454042805 11703236666947013573816513)
        ·
          refine ⟨8777427500210260180362385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11703236666947013573816513 8777427500210260180362385)
          ·
            refine ⟨6583070625157695135271789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8777427500210260180362385 6583070625157695135271789)
            ·
              refine ⟨2468651484434135675726921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6583070625157695135271789 2468651484434135675726921)
              ·
                refine ⟨1851488613325601756795191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468651484434135675726921 1851488613325601756795191)
                ·
                  refine ⟨2777232919988402635192787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851488613325601756795191 2777232919988402635192787)
                  ·
                    refine ⟨4165849379982603952789181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777232919988402635192787 4165849379982603952789181)
                    ·
                      refine ⟨1562193517493476482295943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165849379982603952789181 1562193517493476482295943)
                      ·
                        rfl

theorem cell23_3042361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3042361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042361 prefixEnd_3042361 := by exact prefixLift 3042361
  have htrace : WordTrace (prefixWord ++ tailWord_3042361) baseStart_3042361 baseEnd_3042361 := by
    simpa [prefixWord, tailWord_3042361, baseEnd_3042361] using wordTrace_append hprefix tailTrace_3042361
  have hstable : (prefixWord ++ tailWord_3042361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042361).length < 2 ^ (prefixWord ++ tailWord_3042361).sum := by decide
  have hdescent : baseEnd_3042361 < baseStart_3042361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042400 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3042400 : Nat := 118140960795 + 3042400 * 2 ^ 59
def prefixEnd_3042400 : Nat := 4983230072969 + 3 ^ 40 * 3042400 * 2
def baseEnd_3042400 : Nat := 1562213543239001829708263

theorem tailTrace_3042400 : CollatzResearch.WordTrace tailWord_3042400 prefixEnd_3042400 1562213543239001829708263 := by
  unfold tailWord_3042400
  simp only [CollatzResearch.WordTrace]
  refine ⟨55482722088955937698798327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73976962785274583598397769 55482722088955937698798327)
  ·
    refine ⟨83224083133433906548197491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55482722088955937698798327 83224083133433906548197491)
    ·
      refine ⟨124836124700150859822296237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83224083133433906548197491 124836124700150859822296237)
      ·
        refine ⟨46813546762556572433361089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124836124700150859822296237 46813546762556572433361089)
        ·
          refine ⟨35110160071917429325020817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46813546762556572433361089 35110160071917429325020817)
          ·
            refine ⟨26332620053938071993765613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35110160071917429325020817 26332620053938071993765613)
            ·
              refine ⟨9874732520226776997662105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26332620053938071993765613 9874732520226776997662105)
              ·
                refine ⟨7406049390170082748246579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874732520226776997662105 7406049390170082748246579)
                ·
                  refine ⟨11109074085255124122369869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406049390170082748246579 11109074085255124122369869)
                  ·
                    refine ⟨4165902781970671545888701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11109074085255124122369869 4165902781970671545888701)
                    ·
                      refine ⟨1562213543239001829708263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4165902781970671545888701 1562213543239001829708263)
                      ·
                        rfl

theorem cell23_3042400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3042400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042400 prefixEnd_3042400 := by exact prefixLift 3042400
  have htrace : WordTrace (prefixWord ++ tailWord_3042400) baseStart_3042400 baseEnd_3042400 := by
    simpa [prefixWord, tailWord_3042400, baseEnd_3042400] using wordTrace_append hprefix tailTrace_3042400
  have hstable : (prefixWord ++ tailWord_3042400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042400).length < 2 ^ (prefixWord ++ tailWord_3042400).sum := by decide
  have hdescent : baseEnd_3042400 < baseStart_3042400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042423 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3042423 : Nat := 118140960795 + 3042423 * 2 ^ 59
def prefixEnd_3042423 : Nat := 4983230072969 + 3 ^ 40 * 3042423 * 2
def baseEnd_3042423 : Nat := 1562225353294055239720657

theorem tailTrace_3042423 : CollatzResearch.WordTrace tailWord_3042423 prefixEnd_3042423 1562225353294055239720657 := by
  unfold tailWord_3042423
  simp only [CollatzResearch.WordTrace]
  refine ⟨110966283056828550325683923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73977522037885700217122615 110966283056828550325683923)
  ·
    refine ⟨166449424585242825488525885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110966283056828550325683923 166449424585242825488525885)
    ·
      refine ⟨62418534219466059558197207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166449424585242825488525885 62418534219466059558197207)
      ·
        refine ⟨93627801329199089337295811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62418534219466059558197207 93627801329199089337295811)
        ·
          refine ⟨140441701993798634005943717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93627801329199089337295811 140441701993798634005943717)
          ·
            refine ⟨26332819123837243876114447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140441701993798634005943717 26332819123837243876114447)
            ·
              refine ⟨39499228685755865814171671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26332819123837243876114447 39499228685755865814171671)
              ·
                refine ⟨59248843028633798721257507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39499228685755865814171671 59248843028633798721257507)
                ·
                  refine ⟨88873264542950698081886261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59248843028633798721257507 88873264542950698081886261)
                  ·
                    refine ⟨8331868550901627945176837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88873264542950698081886261 8331868550901627945176837)
                    ·
                      refine ⟨1562225353294055239720657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8331868550901627945176837 1562225353294055239720657)
                      ·
                        rfl

theorem cell23_3042423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3042423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042423 prefixEnd_3042423 := by exact prefixLift 3042423
  have htrace : WordTrace (prefixWord ++ tailWord_3042423) baseStart_3042423 baseEnd_3042423 := by
    simpa [prefixWord, tailWord_3042423, baseEnd_3042423] using wordTrace_append hprefix tailTrace_3042423
  have hstable : (prefixWord ++ tailWord_3042423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042423).length < 2 ^ (prefixWord ++ tailWord_3042423).sum := by decide
  have hdescent : baseEnd_3042423 < baseStart_3042423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_3042443 : Nat := 118140960795 + 3042443 * 2 ^ 59
def prefixEnd_3042443 : Nat := 4983230072969 + 3 ^ 40 * 3042443 * 2
def baseEnd_3042443 : Nat := 1562235622907145161470565

theorem tailTrace_3042443 : CollatzResearch.WordTrace tailWord_3042443 prefixEnd_3042443 1562235622907145161470565 := by
  unfold tailWord_3042443
  simp only [CollatzResearch.WordTrace]
  refine ⟨110967012516756093741411983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73978008344504062494274655 110967012516756093741411983)
  ·
    refine ⟨166450518775134140612117975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110967012516756093741411983 166450518775134140612117975)
    ·
      refine ⟨249675778162701210918176963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166450518775134140612117975 249675778162701210918176963)
      ·
        refine ⟨374513667244051816377265445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249675778162701210918176963 374513667244051816377265445)
        ·
          refine ⟨70221312608259715570737271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374513667244051816377265445 70221312608259715570737271)
          ·
            refine ⟨105331968912389573356105907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70221312608259715570737271 105331968912389573356105907)
            ·
              refine ⟨157997953368584360034158861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105331968912389573356105907 157997953368584360034158861)
              ·
                refine ⟨59249232513219135012809573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157997953368584360034158861 59249232513219135012809573)
                ·
                  refine ⟨11109231096228587814901795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59249232513219135012809573 11109231096228587814901795)
                  ·
                    refine ⟨16663846644342881722352693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11109231096228587814901795 16663846644342881722352693)
                    ·
                      refine ⟨1562235622907145161470565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16663846644342881722352693 1562235622907145161470565)
                      ·
                        rfl

theorem cell23_3042443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_3042443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042443 prefixEnd_3042443 := by exact prefixLift 3042443
  have htrace : WordTrace (prefixWord ++ tailWord_3042443) baseStart_3042443 baseEnd_3042443 := by
    simpa [prefixWord, tailWord_3042443, baseEnd_3042443] using wordTrace_append hprefix tailTrace_3042443
  have hstable : (prefixWord ++ tailWord_3042443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042443).length < 2 ^ (prefixWord ++ tailWord_3042443).sum := by decide
  have hdescent : baseEnd_3042443 < baseStart_3042443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042497 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 7]
def baseStart_3042497 : Nat := 118140960795 + 3042497 * 2 ^ 59
def prefixEnd_3042497 : Nat := 4983230072969 + 3 ^ 40 * 3042497 * 2
def baseEnd_3042497 : Nat := 173584816762498661132813

theorem tailTrace_3042497 : CollatzResearch.WordTrace tailWord_3042497 prefixEnd_3042497 173584816762498661132813 := by
  unfold tailWord_3042497
  simp only [CollatzResearch.WordTrace]
  refine ⟨110968982058560460963877745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73979321372373640642585163 110968982058560460963877745)
  ·
    refine ⟨83226736543920345722908309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110968982058560460963877745 83226736543920345722908309)
    ·
      refine ⟨3901253275496266205761327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83226736543920345722908309 3901253275496266205761327)
      ·
        refine ⟨5851879913244399308641991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901253275496266205761327 5851879913244399308641991)
        ·
          refine ⟨8777819869866598962962987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851879913244399308641991 8777819869866598962962987)
          ·
            refine ⟨13166729804799898444444481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8777819869866598962962987 13166729804799898444444481)
            ·
              refine ⟨9875047353599923833333361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13166729804799898444444481 9875047353599923833333361)
              ·
                refine ⟨7406285515199942875000021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9875047353599923833333361 7406285515199942875000021)
                ·
                  refine ⟨173584816762498661132813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7406285515199942875000021 173584816762498661132813)
                  ·
                    rfl

theorem cell23_3042497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_3042497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042497 prefixEnd_3042497 := by exact prefixLift 3042497
  have htrace : WordTrace (prefixWord ++ tailWord_3042497) baseStart_3042497 baseEnd_3042497 := by
    simpa [prefixWord, tailWord_3042497, baseEnd_3042497] using wordTrace_append hprefix tailTrace_3042497
  have hstable : (prefixWord ++ tailWord_3042497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042497).length < 2 ^ (prefixWord ++ tailWord_3042497).sum := by decide
  have hdescent : baseEnd_3042497 < baseStart_3042497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042523 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 8]
def baseStart_3042523 : Nat := 118140960795 + 3042523 * 2 ^ 59
def prefixEnd_3042523 : Nat := 4983230072969 + 3 ^ 40 * 3042523 * 2
def baseEnd_3042523 : Nat := 520758900453168282823399

theorem tailTrace_3042523 : CollatzResearch.WordTrace tailWord_3042523 prefixEnd_3042523 520758900453168282823399 := by
  unfold tailWord_3042523
  simp only [CollatzResearch.WordTrace]
  refine ⟨110969930356466267404324223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73979953570977511602882815 110969930356466267404324223)
  ·
    refine ⟨166454895534699401106486335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110969930356466267404324223 166454895534699401106486335)
    ·
      refine ⟨249682343302049101659729503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166454895534699401106486335 249682343302049101659729503)
      ·
        refine ⟨374523514953073652489594255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249682343302049101659729503 374523514953073652489594255)
        ·
          refine ⟨561785272429610478734391383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374523514953073652489594255 561785272429610478734391383)
          ·
            refine ⟨842677908644415718101587075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561785272429610478734391383 842677908644415718101587075)
            ·
              refine ⟨1264016862966623577152380613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842677908644415718101587075 1264016862966623577152380613)
              ·
                refine ⟨237003161806241920716071365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1264016862966623577152380613 237003161806241920716071365)
                ·
                  refine ⟨44438092838670360134263381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237003161806241920716071365 44438092838670360134263381)
                  ·
                    refine ⟨520758900453168282823399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44438092838670360134263381 520758900453168282823399)
                    ·
                      rfl

theorem cell23_3042523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_3042523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042523 prefixEnd_3042523 := by exact prefixLift 3042523
  have htrace : WordTrace (prefixWord ++ tailWord_3042523) baseStart_3042523 baseEnd_3042523 := by
    simpa [prefixWord, tailWord_3042523, baseEnd_3042523] using wordTrace_append hprefix tailTrace_3042523
  have hstable : (prefixWord ++ tailWord_3042523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042523).length < 2 ^ (prefixWord ++ tailWord_3042523).sum := by decide
  have hdescent : baseEnd_3042523 < baseStart_3042523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042564 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3042564 : Nat := 118140960795 + 3042564 * 2 ^ 59
def prefixEnd_3042564 : Nat := 4983230072969 + 3 ^ 40 * 3042564 * 2
def baseEnd_3042564 : Nat := 1562297754066339188057509

theorem tailTrace_3042564 : CollatzResearch.WordTrace tailWord_3042564 prefixEnd_3042564 1562297754066339188057509 := by
  unfold tailWord_3042564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55485712874658865703283373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73980950499545154271044497 55485712874658865703283373)
  ·
    refine ⟨20807142327997074638731265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55485712874658865703283373 20807142327997074638731265)
    ·
      refine ⟨15605356745997805979048449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20807142327997074638731265 15605356745997805979048449)
      ·
        refine ⟨11704017559498354484286337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15605356745997805979048449 11704017559498354484286337)
        ·
          refine ⟨8778013169623765863214753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11704017559498354484286337 8778013169623765863214753)
          ·
            refine ⟨6583509877217824397411065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8778013169623765863214753 6583509877217824397411065)
            ·
              refine ⟨4937632407913368298058299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583509877217824397411065 4937632407913368298058299)
              ·
                refine ⟨7406448611870052447087449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937632407913368298058299 7406448611870052447087449)
                ·
                  refine ⟨5554836458902539335315587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7406448611870052447087449 5554836458902539335315587)
                  ·
                    refine ⟨8332254688353809002973381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554836458902539335315587 8332254688353809002973381)
                    ·
                      refine ⟨1562297754066339188057509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8332254688353809002973381 1562297754066339188057509)
                      ·
                        rfl

theorem cell23_3042564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3042564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042564 prefixEnd_3042564 := by exact prefixLift 3042564
  have htrace : WordTrace (prefixWord ++ tailWord_3042564) baseStart_3042564 baseEnd_3042564 := by
    simpa [prefixWord, tailWord_3042564, baseEnd_3042564] using wordTrace_append hprefix tailTrace_3042564
  have hstable : (prefixWord ++ tailWord_3042564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042564).length < 2 ^ (prefixWord ++ tailWord_3042564).sum := by decide
  have hdescent : baseEnd_3042564 < baseStart_3042564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042591 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 1, 4]
def baseStart_3042591 : Nat := 118140960795 + 3042591 * 2 ^ 59
def prefixEnd_3042591 : Nat := 4983230072969 + 3 ^ 40 * 3042591 * 2
def baseEnd_3042591 : Nat := 520770539348003527473295

theorem tailTrace_3042591 : CollatzResearch.WordTrace tailWord_3042591 prefixEnd_3042591 520770539348003527473295 := by
  unfold tailWord_3042591
  simp only [CollatzResearch.WordTrace]
  refine ⟨110972410520219915017799627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73981607013479943345199751 110972410520219915017799627)
  ·
    refine ⟨166458615780329872526699441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110972410520219915017799627 166458615780329872526699441)
    ·
      refine ⟨124843961835247404395024581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166458615780329872526699441 124843961835247404395024581)
      ·
        refine ⟨23408242844108888324067109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124843961835247404395024581 23408242844108888324067109)
        ·
          refine ⟨4389045533270416560762583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23408242844108888324067109 4389045533270416560762583)
          ·
            refine ⟨6583568299905624841143875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389045533270416560762583 6583568299905624841143875)
            ·
              refine ⟨9875352449858437261715813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583568299905624841143875 9875352449858437261715813)
              ·
                refine ⟨1851628584348456986571715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9875352449858437261715813 1851628584348456986571715)
                ·
                  refine ⟨2777442876522685479857573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851628584348456986571715 2777442876522685479857573)
                  ·
                    refine ⟨520770539348003527473295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777442876522685479857573 520770539348003527473295)
                    ·
                      rfl

theorem cell23_3042591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 4].length) (baseStart_3042591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042591 prefixEnd_3042591 := by exact prefixLift 3042591
  have htrace : WordTrace (prefixWord ++ tailWord_3042591) baseStart_3042591 baseEnd_3042591 := by
    simpa [prefixWord, tailWord_3042591, baseEnd_3042591] using wordTrace_append hprefix tailTrace_3042591
  have hstable : (prefixWord ++ tailWord_3042591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042591).length < 2 ^ (prefixWord ++ tailWord_3042591).sum := by decide
  have hdescent : baseEnd_3042591 < baseStart_3042591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042607 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 5, 2]
def baseStart_3042607 : Nat := 118140960795 + 3042607 * 2 ^ 59
def prefixEnd_3042607 : Nat := 4983230072969 + 3 ^ 40 * 3042607 * 2
def baseEnd_3042607 : Nat := 1562319833734482519819811

theorem tailTrace_3042607 : CollatzResearch.WordTrace tailWord_3042607 prefixEnd_3042607 1562319833734482519819811 := by
  unfold tailWord_3042607
  simp only [CollatzResearch.WordTrace]
  refine ⟨110972994088161949750382075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73981996058774633166921383 110972994088161949750382075)
  ·
    refine ⟨166459491132242924625573113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110972994088161949750382075 166459491132242924625573113)
    ·
      refine ⟨124844618349182193469179835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166459491132242924625573113 124844618349182193469179835)
      ·
        refine ⟨187266927523773290203769753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124844618349182193469179835 187266927523773290203769753)
        ·
          refine ⟨140450195642829967652827315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187266927523773290203769753 140450195642829967652827315)
          ·
            refine ⟨210675293464244951479240973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140450195642829967652827315 210675293464244951479240973)
            ·
              refine ⟨79003235049091856804715365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210675293464244951479240973 79003235049091856804715365)
              ·
                refine ⟨14813106571704723150884131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79003235049091856804715365 14813106571704723150884131)
                ·
                  refine ⟨22219659857557084726326197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14813106571704723150884131 22219659857557084726326197)
                  ·
                    refine ⟨2083093111645976693093081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22219659857557084726326197 2083093111645976693093081)
                    ·
                      refine ⟨1562319833734482519819811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083093111645976693093081 1562319833734482519819811)
                      ·
                        rfl

theorem cell23_3042607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5, 2].length) (baseStart_3042607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042607 prefixEnd_3042607 := by exact prefixLift 3042607
  have htrace : WordTrace (prefixWord ++ tailWord_3042607) baseStart_3042607 baseEnd_3042607 := by
    simpa [prefixWord, tailWord_3042607, baseEnd_3042607] using wordTrace_append hprefix tailTrace_3042607
  have hstable : (prefixWord ++ tailWord_3042607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042607).length < 2 ^ (prefixWord ++ tailWord_3042607).sum := by decide
  have hdescent : baseEnd_3042607 < baseStart_3042607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042631 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_3042631 : Nat := 118140960795 + 3042631 * 2 ^ 59
def prefixEnd_3042631 : Nat := 4983230072969 + 3 ^ 40 * 3042631 * 2
def baseEnd_3042631 : Nat := 1562332157270190425919701

theorem tailTrace_3042631 : CollatzResearch.WordTrace tailWord_3042631 prefixEnd_3042631 1562332157270190425919701 := by
  unfold tailWord_3042631
  simp only [CollatzResearch.WordTrace]
  refine ⟨110973869440075001849255747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73982579626716667899503831 110973869440075001849255747)
  ·
    refine ⟨166460804160112502773883621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110973869440075001849255747 166460804160112502773883621)
    ·
      refine ⟨31211400780021094270103179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166460804160112502773883621 31211400780021094270103179)
      ·
        refine ⟨46817101170031641405154769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31211400780021094270103179 46817101170031641405154769)
        ·
          refine ⟨35112825877523731053866077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46817101170031641405154769 35112825877523731053866077)
          ·
            refine ⟨13167309704071399145199779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35112825877523731053866077 13167309704071399145199779)
            ·
              refine ⟨19750964556107098717799669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13167309704071399145199779 19750964556107098717799669)
              ·
                refine ⟨1851652927135040504793719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19750964556107098717799669 1851652927135040504793719)
                ·
                  refine ⟨2777479390702560757190579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851652927135040504793719 2777479390702560757190579)
                  ·
                    refine ⟨4166219086053841135785869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777479390702560757190579 4166219086053841135785869)
                    ·
                      refine ⟨1562332157270190425919701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4166219086053841135785869 1562332157270190425919701)
                      ·
                        rfl

theorem cell23_3042631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_3042631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042631 prefixEnd_3042631 := by exact prefixLift 3042631
  have htrace : WordTrace (prefixWord ++ tailWord_3042631) baseStart_3042631 baseEnd_3042631 := by
    simpa [prefixWord, tailWord_3042631, baseEnd_3042631] using wordTrace_append hprefix tailTrace_3042631
  have hstable : (prefixWord ++ tailWord_3042631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042631).length < 2 ^ (prefixWord ++ tailWord_3042631).sum := by decide
  have hdescent : baseEnd_3042631 < baseStart_3042631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042657 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_3042657 : Nat := 118140960795 + 3042657 * 2 ^ 59
def prefixEnd_3042657 : Nat := 4983230072969 + 3 ^ 40 * 3042657 * 2
def baseEnd_3042657 : Nat := 1562345507767207324194581

theorem tailTrace_3042657 : CollatzResearch.WordTrace tailWord_3042657 prefixEnd_3042657 1562345507767207324194581 := by
  unfold tailWord_3042657
  simp only [CollatzResearch.WordTrace]
  refine ⟨110974817737980808289702225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73983211825320538859801483 110974817737980808289702225)
  ·
    refine ⟨83231113303485606217276669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110974817737980808289702225 83231113303485606217276669)
    ·
      refine ⟨31211667488807102331478751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83231113303485606217276669 31211667488807102331478751)
      ·
        refine ⟨46817501233210653497218127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31211667488807102331478751 46817501233210653497218127)
        ·
          refine ⟨70226251849815980245827191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46817501233210653497218127 70226251849815980245827191)
          ·
            refine ⟨105339377774723970368740787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70226251849815980245827191 105339377774723970368740787)
            ·
              refine ⟨158009066662085955553111181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105339377774723970368740787 158009066662085955553111181)
              ·
                refine ⟨59253399998282233332416693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158009066662085955553111181 59253399998282233332416693)
                ·
                  refine ⟨5555006249838959374914065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59253399998282233332416693 5555006249838959374914065)
                  ·
                    refine ⟨4166254687379219531185549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5555006249838959374914065 4166254687379219531185549)
                    ·
                      refine ⟨1562345507767207324194581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4166254687379219531185549 1562345507767207324194581)
                      ·
                        rfl

theorem cell23_3042657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_3042657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042657 prefixEnd_3042657 := by exact prefixLift 3042657
  have htrace : WordTrace (prefixWord ++ tailWord_3042657) baseStart_3042657 baseEnd_3042657 := by
    simpa [prefixWord, tailWord_3042657, baseEnd_3042657] using wordTrace_append hprefix tailTrace_3042657
  have hstable : (prefixWord ++ tailWord_3042657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042657).length < 2 ^ (prefixWord ++ tailWord_3042657).sum := by decide
  have hdescent : baseEnd_3042657 < baseStart_3042657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042680 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3042680 : Nat := 118140960795 + 3042680 * 2 ^ 59
def prefixEnd_3042680 : Nat := 4983230072969 + 3 ^ 40 * 3042680 * 2
def baseEnd_3042680 : Nat := 1562357317822260734206975

theorem tailTrace_3042680 : CollatzResearch.WordTrace tailWord_3042680 prefixEnd_3042680 1562357317822260734206975 := by
  unfold tailWord_3042680
  simp only [CollatzResearch.WordTrace]
  refine ⟨55487828308448741608894747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73983771077931655478526329 55487828308448741608894747)
  ·
    refine ⟨83231742462673112413342121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55487828308448741608894747 83231742462673112413342121)
    ·
      refine ⟨62423806847004834310006591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83231742462673112413342121 62423806847004834310006591)
      ·
        refine ⟨93635710270507251465009887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62423806847004834310006591 93635710270507251465009887)
        ·
          refine ⟨140453565405760877197514831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93635710270507251465009887 140453565405760877197514831)
          ·
            refine ⟨210680348108641315796272247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140453565405760877197514831 210680348108641315796272247)
            ·
              refine ⟨316020522162961973694408371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210680348108641315796272247 316020522162961973694408371)
              ·
                refine ⟨474030783244442960541612557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316020522162961973694408371 474030783244442960541612557)
                ·
                  refine ⟨177761543716666110203104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474030783244442960541612557 177761543716666110203104709)
                  ·
                    refine ⟨33330289446874895663082133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177761543716666110203104709 33330289446874895663082133)
                    ·
                      refine ⟨1562357317822260734206975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33330289446874895663082133 1562357317822260734206975)
                      ·
                        rfl

theorem cell23_3042680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3042680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042680 prefixEnd_3042680 := by exact prefixLift 3042680
  have htrace : WordTrace (prefixWord ++ tailWord_3042680) baseStart_3042680 baseEnd_3042680 := by
    simpa [prefixWord, tailWord_3042680, baseEnd_3042680] using wordTrace_append hprefix tailTrace_3042680
  have hstable : (prefixWord ++ tailWord_3042680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042680).length < 2 ^ (prefixWord ++ tailWord_3042680).sum := by decide
  have hdescent : baseEnd_3042680 < baseStart_3042680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042744 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_3042744 : Nat := 118140960795 + 3042744 * 2 ^ 59
def prefixEnd_3042744 : Nat := 4983230072969 + 3 ^ 40 * 3042744 * 2
def baseEnd_3042744 : Nat := 1562390180584148483806681

theorem tailTrace_3042744 : CollatzResearch.WordTrace tailWord_3042744 prefixEnd_3042744 1562390180584148483806681 := by
  unfold tailWord_3042744
  simp only [CollatzResearch.WordTrace]
  refine ⟨55488995444332811074059643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73985327259110414765412857 55488995444332811074059643)
  ·
    refine ⟨83233493166499216611089465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55488995444332811074059643 83233493166499216611089465)
    ·
      refine ⟨62425119874874412458317099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83233493166499216611089465 62425119874874412458317099)
      ·
        refine ⟨93637679812311618687475649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62425119874874412458317099 93637679812311618687475649)
        ·
          refine ⟨70228259859233714015606737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93637679812311618687475649 70228259859233714015606737)
          ·
            refine ⟨52671194894425285511705053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70228259859233714015606737 52671194894425285511705053)
            ·
              refine ⟨19751698085409482066889395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52671194894425285511705053 19751698085409482066889395)
              ·
                refine ⟨29627547128114223100334093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19751698085409482066889395 29627547128114223100334093)
                ·
                  refine ⟨11110330173042833662625285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29627547128114223100334093 11110330173042833662625285)
                  ·
                    refine ⟨2083186907445531311742241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11110330173042833662625285 2083186907445531311742241)
                    ·
                      refine ⟨1562390180584148483806681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083186907445531311742241 1562390180584148483806681)
                      ·
                        rfl

theorem cell23_3042744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_3042744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042744 prefixEnd_3042744 := by exact prefixLift 3042744
  have htrace : WordTrace (prefixWord ++ tailWord_3042744) baseStart_3042744 baseEnd_3042744 := by
    simpa [prefixWord, tailWord_3042744, baseEnd_3042744] using wordTrace_append hprefix tailTrace_3042744
  have hstable : (prefixWord ++ tailWord_3042744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042744).length < 2 ^ (prefixWord ++ tailWord_3042744).sum := by decide
  have hdescent : baseEnd_3042744 < baseStart_3042744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042764 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3042764 : Nat := 118140960795 + 3042764 * 2 ^ 59
def prefixEnd_3042764 : Nat := 4983230072969 + 3 ^ 40 * 3042764 * 2
def baseEnd_3042764 : Nat := 1562400450197238405556589

theorem tailTrace_3042764 : CollatzResearch.WordTrace tailWord_3042764 prefixEnd_3042764 1562400450197238405556589 := by
  unfold tailWord_3042764
  simp only [CollatzResearch.WordTrace]
  refine ⟨55489360174296582781923673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73985813565728777042564897 55489360174296582781923673)
  ·
    refine ⟨41617020130722437086442755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55489360174296582781923673 41617020130722437086442755)
    ·
      refine ⟨62425530196083655629664133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41617020130722437086442755 62425530196083655629664133)
      ·
        refine ⟨11704786911765685430562025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62425530196083655629664133 11704786911765685430562025)
        ·
          refine ⟨8778590183824264072921519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11704786911765685430562025 8778590183824264072921519)
          ·
            refine ⟨13167885275736396109382279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778590183824264072921519 13167885275736396109382279)
            ·
              refine ⟨19751827913604594164073419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13167885275736396109382279 19751827913604594164073419)
              ·
                refine ⟨29627741870406891246110129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19751827913604594164073419 29627741870406891246110129)
                ·
                  refine ⟨22220806402805168434582597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29627741870406891246110129 22220806402805168434582597)
                  ·
                    refine ⟨4166401200525969081484237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22220806402805168434582597 4166401200525969081484237)
                    ·
                      refine ⟨1562400450197238405556589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4166401200525969081484237 1562400450197238405556589)
                      ·
                        rfl

theorem cell23_3042764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3042764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042764 prefixEnd_3042764 := by exact prefixLift 3042764
  have htrace : WordTrace (prefixWord ++ tailWord_3042764) baseStart_3042764 baseEnd_3042764 := by
    simpa [prefixWord, tailWord_3042764, baseEnd_3042764] using wordTrace_append hprefix tailTrace_3042764
  have hstable : (prefixWord ++ tailWord_3042764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042764).length < 2 ^ (prefixWord ++ tailWord_3042764).sum := by decide
  have hdescent : baseEnd_3042764 < baseStart_3042764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042778 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_3042778 : Nat := 118140960795 + 3042778 * 2 ^ 59
def prefixEnd_3042778 : Nat := 4983230072969 + 3 ^ 40 * 3042778 * 2
def baseEnd_3042778 : Nat := 1562407638926401350781525

theorem tailTrace_3042778 : CollatzResearch.WordTrace tailWord_3042778 prefixEnd_3042778 1562407638926401350781525 := by
  unfold tailWord_3042778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744807742635611488714247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73986153980361630636571325 27744807742635611488714247)
  ·
    refine ⟨41617211613953417233071371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27744807742635611488714247 41617211613953417233071371)
    ·
      refine ⟨62425817420930125849607057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41617211613953417233071371 62425817420930125849607057)
      ·
        refine ⟨46819363065697594387205293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62425817420930125849607057 46819363065697594387205293)
        ·
          refine ⟨17557261149636597895201985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46819363065697594387205293 17557261149636597895201985)
          ·
            refine ⟨13167945862227448421401489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17557261149636597895201985 13167945862227448421401489)
            ·
              refine ⟨9875959396670586316051117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13167945862227448421401489 9875959396670586316051117)
              ·
                refine ⟨3703484773751469868519169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9875959396670586316051117 3703484773751469868519169)
                ·
                  refine ⟨2777613580313602401389377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3703484773751469868519169 2777613580313602401389377)
                  ·
                    refine ⟨2083210185235201801042033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2777613580313602401389377 2083210185235201801042033)
                    ·
                      refine ⟨1562407638926401350781525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083210185235201801042033 1562407638926401350781525)
                      ·
                        rfl

theorem cell23_3042778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_3042778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042778 prefixEnd_3042778 := by exact prefixLift 3042778
  have htrace : WordTrace (prefixWord ++ tailWord_3042778) baseStart_3042778 baseEnd_3042778 := by
    simpa [prefixWord, tailWord_3042778, baseEnd_3042778] using wordTrace_append hprefix tailTrace_3042778
  have hstable : (prefixWord ++ tailWord_3042778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042778).length < 2 ^ (prefixWord ++ tailWord_3042778).sum := by decide
  have hdescent : baseEnd_3042778 < baseStart_3042778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042801 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 5]
def baseStart_3042801 : Nat := 118140960795 + 3042801 * 2 ^ 59
def prefixEnd_3042801 : Nat := 4983230072969 + 3 ^ 40 * 3042801 * 2
def baseEnd_3042801 : Nat := 173602160997939417865991

theorem tailTrace_3042801 : CollatzResearch.WordTrace tailWord_3042801 prefixEnd_3042801 173602160997939417865991 := by
  unfold tailWord_3042801
  simp only [CollatzResearch.WordTrace]
  refine ⟨110980069849459120882944257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73986713232972747255296171 110980069849459120882944257)
  ·
    refine ⟨83235052387094340662208193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110980069849459120882944257 83235052387094340662208193)
    ·
      refine ⟨62426289290320755496656145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83235052387094340662208193 62426289290320755496656145)
      ·
        refine ⟨46819716967740566622492109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62426289290320755496656145 46819716967740566622492109)
        ·
          refine ⟨17557393862902712483434541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46819716967740566622492109 17557393862902712483434541)
          ·
            refine ⟨6584022698588517181287953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17557393862902712483434541 6584022698588517181287953)
            ·
              refine ⟨4938017023941387885965965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6584022698588517181287953 4938017023941387885965965)
              ·
                refine ⟨1851756383978020457237237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4938017023941387885965965 1851756383978020457237237)
                ·
                  refine ⟨173602160997939417865991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851756383978020457237237 173602160997939417865991)
                  ·
                    rfl

theorem cell23_3042801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 5].length) (baseStart_3042801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042801 prefixEnd_3042801 := by exact prefixLift 3042801
  have htrace : WordTrace (prefixWord ++ tailWord_3042801) baseStart_3042801 baseEnd_3042801 := by
    simpa [prefixWord, tailWord_3042801, baseEnd_3042801] using wordTrace_append hprefix tailTrace_3042801
  have hstable : (prefixWord ++ tailWord_3042801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042801).length < 2 ^ (prefixWord ++ tailWord_3042801).sum := by decide
  have hdescent : baseEnd_3042801 < baseStart_3042801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042807 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3042807 : Nat := 118140960795 + 3042807 * 2 ^ 59
def prefixEnd_3042807 : Nat := 4983230072969 + 3 ^ 40 * 3042807 * 2
def baseEnd_3042807 : Nat := 1562422529865381737318891

theorem tailTrace_3042807 : CollatzResearch.WordTrace tailWord_3042807 prefixEnd_3042807 1562422529865381737318891 := by
  unfold tailWord_3042807
  simp only [CollatzResearch.WordTrace]
  refine ⟨110980288687437383907662675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73986859124958255938441783 110980288687437383907662675)
  ·
    refine ⟨166470433031156075861494013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110980288687437383907662675 166470433031156075861494013)
    ·
      refine ⟨62426412386683528448060255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166470433031156075861494013 62426412386683528448060255)
      ·
        refine ⟨93639618580025292672090383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62426412386683528448060255 93639618580025292672090383)
        ·
          refine ⟨140459427870037939008135575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93639618580025292672090383 140459427870037939008135575)
          ·
            refine ⟨210689141805056908512203363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140459427870037939008135575 210689141805056908512203363)
            ·
              refine ⟨316033712707585362768305045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210689141805056908512203363 316033712707585362768305045)
              ·
                refine ⟨14814080283168063879764299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316033712707585362768305045 14814080283168063879764299)
                ·
                  refine ⟨22221120424752095819646449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14814080283168063879764299 22221120424752095819646449)
                  ·
                    refine ⟨16665840318564071864734837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22221120424752095819646449 16665840318564071864734837)
                    ·
                      refine ⟨1562422529865381737318891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16665840318564071864734837 1562422529865381737318891)
                      ·
                        rfl

theorem cell23_3042807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3042807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042807 prefixEnd_3042807 := by exact prefixLift 3042807
  have htrace : WordTrace (prefixWord ++ tailWord_3042807) baseStart_3042807 baseEnd_3042807 := by
    simpa [prefixWord, tailWord_3042807, baseEnd_3042807] using wordTrace_append hprefix tailTrace_3042807
  have hstable : (prefixWord ++ tailWord_3042807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042807).length < 2 ^ (prefixWord ++ tailWord_3042807).sum := by decide
  have hdescent : baseEnd_3042807 < baseStart_3042807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042818 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3042818 : Nat := 118140960795 + 3042818 * 2 ^ 59
def prefixEnd_3042818 : Nat := 4983230072969 + 3 ^ 40 * 3042818 * 2
def baseEnd_3042818 : Nat := 173603130905842354920149

theorem tailTrace_3042818 : CollatzResearch.WordTrace tailWord_3042818 prefixEnd_3042818 173603130905842354920149 := by
  unfold tailWord_3042818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745172472599383196578277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73987126593598355190875405 27745172472599383196578277)
  ·
    refine ⟨5202219838612384349358427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27745172472599383196578277 5202219838612384349358427)
    ·
      refine ⟨7803329757918576524037641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5202219838612384349358427 7803329757918576524037641)
      ·
        refine ⟨5852497318438932393028231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7803329757918576524037641 5852497318438932393028231)
        ·
          refine ⟨8778745977658398589542347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852497318438932393028231 8778745977658398589542347)
          ·
            refine ⟨13168118966487597884313521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778745977658398589542347 13168118966487597884313521)
            ·
              refine ⟨9876089224865698413235141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13168118966487597884313521 9876089224865698413235141)
              ·
                refine ⟨1851766729662318452481589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9876089224865698413235141 1851766729662318452481589)
                ·
                  refine ⟨173603130905842354920149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851766729662318452481589 173603130905842354920149)
                  ·
                    rfl

theorem cell23_3042818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3042818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042818 prefixEnd_3042818 := by exact prefixLift 3042818
  have htrace : WordTrace (prefixWord ++ tailWord_3042818) baseStart_3042818 baseEnd_3042818 := by
    simpa [prefixWord, tailWord_3042818, baseEnd_3042818] using wordTrace_append hprefix tailTrace_3042818
  have hstable : (prefixWord ++ tailWord_3042818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042818).length < 2 ^ (prefixWord ++ tailWord_3042818).sum := by decide
  have hdescent : baseEnd_3042818 < baseStart_3042818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042829 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3042829 : Nat := 118140960795 + 3042829 * 2 ^ 59
def prefixEnd_3042829 : Nat := 4983230072969 + 3 ^ 40 * 3042829 * 2
def baseEnd_3042829 : Nat := 1562433826439780651243791

theorem tailTrace_3042829 : CollatzResearch.WordTrace tailWord_3042829 prefixEnd_3042829 1562433826439780651243791 := by
  unfold tailWord_3042829
  simp only [CollatzResearch.WordTrace]
  refine ⟨110981091093357681664963541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73987394062238454443309027 110981091093357681664963541)
  ·
    refine ⟨2601119322500570664022583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110981091093357681664963541 2601119322500570664022583)
    ·
      refine ⟨3901678983750855996033875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601119322500570664022583 3901678983750855996033875)
      ·
        refine ⟨5852518475626283994050813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901678983750855996033875 5852518475626283994050813)
        ·
          refine ⟨2194694428359856497769055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5852518475626283994050813 2194694428359856497769055)
          ·
            refine ⟨3292041642539784746653583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194694428359856497769055 3292041642539784746653583)
            ·
              refine ⟨4938062463809677119980375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292041642539784746653583 4938062463809677119980375)
              ·
                refine ⟨7407093695714515679970563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938062463809677119980375 7407093695714515679970563)
                ·
                  refine ⟨11110640543571773519955845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407093695714515679970563 11110640543571773519955845)
                  ·
                    refine ⟨2083245101919707534991721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11110640543571773519955845 2083245101919707534991721)
                    ·
                      refine ⟨1562433826439780651243791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083245101919707534991721 1562433826439780651243791)
                      ·
                        rfl

theorem cell23_3042829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3042829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042829 prefixEnd_3042829 := by exact prefixLift 3042829
  have htrace : WordTrace (prefixWord ++ tailWord_3042829) baseStart_3042829 baseEnd_3042829 := by
    simpa [prefixWord, tailWord_3042829, baseEnd_3042829] using wordTrace_append hprefix tailTrace_3042829
  have hstable : (prefixWord ++ tailWord_3042829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042829).length < 2 ^ (prefixWord ++ tailWord_3042829).sum := by decide
  have hdescent : baseEnd_3042829 < baseStart_3042829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042871 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_3042871 : Nat := 118140960795 + 3042871 * 2 ^ 59
def prefixEnd_3042871 : Nat := 4983230072969 + 3 ^ 40 * 3042871 * 2
def baseEnd_3042871 : Nat := 1562455392627269486918597

theorem tailTrace_3042871 : CollatzResearch.WordTrace tailWord_3042871 prefixEnd_3042871 1562455392627269486918597 := by
  unfold tailWord_3042871
  simp only [CollatzResearch.WordTrace]
  refine ⟨110982622959205522837992467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73988415306137015225328311 110982622959205522837992467)
  ·
    refine ⟨166473934438808284256988701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110982622959205522837992467 166473934438808284256988701)
    ·
      refine ⟨62427725414553106596370763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166473934438808284256988701 62427725414553106596370763)
      ·
        refine ⟨93641588121829659894556145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62427725414553106596370763 93641588121829659894556145)
        ·
          refine ⟨70231191091372244920917109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93641588121829659894556145 70231191091372244920917109)
          ·
            refine ⟨6584174164816147961335979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70231191091372244920917109 6584174164816147961335979)
            ·
              refine ⟨9876261247224221942003969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584174164816147961335979 9876261247224221942003969)
              ·
                refine ⟨7407195935418166456502977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9876261247224221942003969 7407195935418166456502977)
                ·
                  refine ⟨5555396951563624842377233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407195935418166456502977 5555396951563624842377233)
                  ·
                    refine ⟨4166547713672718631782925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5555396951563624842377233 4166547713672718631782925)
                    ·
                      refine ⟨1562455392627269486918597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4166547713672718631782925 1562455392627269486918597)
                      ·
                        rfl

theorem cell23_3042871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_3042871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042871 prefixEnd_3042871 := by exact prefixLift 3042871
  have htrace : WordTrace (prefixWord ++ tailWord_3042871) baseStart_3042871 baseEnd_3042871 := by
    simpa [prefixWord, tailWord_3042871, baseEnd_3042871] using wordTrace_append hprefix tailTrace_3042871
  have hstable : (prefixWord ++ tailWord_3042871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042871).length < 2 ^ (prefixWord ++ tailWord_3042871).sum := by decide
  have hdescent : baseEnd_3042871 < baseStart_3042871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042874 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_3042874 : Nat := 118140960795 + 3042874 * 2 ^ 59
def prefixEnd_3042874 : Nat := 4983230072969 + 3 ^ 40 * 3042874 * 2
def baseEnd_3042874 : Nat := 173606325896581441686787

theorem tailTrace_3042874 : CollatzResearch.WordTrace tailWord_3042874 prefixEnd_3042874 173606325896581441686787 := by
  unfold tailWord_3042874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745683094548663587587919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73988488252129769566901117 27745683094548663587587919)
  ·
    refine ⟨41618524641822995381381879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27745683094548663587587919 41618524641822995381381879)
    ·
      refine ⟨62427786962734493072072819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41618524641822995381381879 62427786962734493072072819)
      ·
        refine ⟨93641680444101739608109229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62427786962734493072072819 93641680444101739608109229)
        ·
          refine ⟨35115630166538152353040961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93641680444101739608109229 35115630166538152353040961)
          ·
            refine ⟨26336722624903614264780721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35115630166538152353040961 26336722624903614264780721)
            ·
              refine ⟨19752541968677710698585541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26336722624903614264780721 19752541968677710698585541)
              ·
                refine ⟨3703601619127070755984789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19752541968677710698585541 3703601619127070755984789)
                ·
                  refine ⟨173606325896581441686787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3703601619127070755984789 173606325896581441686787)
                  ·
                    rfl

theorem cell23_3042874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_3042874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042874 prefixEnd_3042874 := by exact prefixLift 3042874
  have htrace : WordTrace (prefixWord ++ tailWord_3042874) baseStart_3042874 baseEnd_3042874 := by
    simpa [prefixWord, tailWord_3042874, baseEnd_3042874] using wordTrace_append hprefix tailTrace_3042874
  have hstable : (prefixWord ++ tailWord_3042874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042874).length < 2 ^ (prefixWord ++ tailWord_3042874).sum := by decide
  have hdescent : baseEnd_3042874 < baseStart_3042874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042901 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3042901 : Nat := 118140960795 + 3042901 * 2 ^ 59
def prefixEnd_3042901 : Nat := 4983230072969 + 3 ^ 40 * 3042901 * 2
def baseEnd_3042901 : Nat := 1562470797046904369543459

theorem tailTrace_3042901 : CollatzResearch.WordTrace tailWord_3042901 prefixEnd_3042901 1562470797046904369543459 := by
  unfold tailWord_3042901
  simp only [CollatzResearch.WordTrace]
  refine ⟨110983717149096837961584557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73989144766064558641056371 110983717149096837961584557)
  ·
    refine ⟨41618893930911314235594209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110983717149096837961584557 41618893930911314235594209)
    ·
      refine ⟨31214170448183485676695657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41618893930911314235594209 31214170448183485676695657)
      ·
        refine ⟨23410627836137614257521743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31214170448183485676695657 23410627836137614257521743)
        ·
          refine ⟨35115941754206421386282615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23410627836137614257521743 35115941754206421386282615)
          ·
            refine ⟨52673912631309632079423923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35115941754206421386282615 52673912631309632079423923)
            ·
              refine ⟨79010868946964448119135885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52673912631309632079423923 79010868946964448119135885)
              ·
                refine ⟨29629075855111668044675957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79010868946964448119135885 29629075855111668044675957)
                ·
                  refine ⟨2777725861416718879188371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29629075855111668044675957 2777725861416718879188371)
                  ·
                    refine ⟨4166588792125078318782557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777725861416718879188371 4166588792125078318782557)
                    ·
                      refine ⟨1562470797046904369543459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4166588792125078318782557 1562470797046904369543459)
                      ·
                        rfl

theorem cell23_3042901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3042901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042901 prefixEnd_3042901 := by exact prefixLift 3042901
  have htrace : WordTrace (prefixWord ++ tailWord_3042901) baseStart_3042901 baseEnd_3042901 := by
    simpa [prefixWord, tailWord_3042901, baseEnd_3042901] using wordTrace_append hprefix tailTrace_3042901
  have hstable : (prefixWord ++ tailWord_3042901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042901).length < 2 ^ (prefixWord ++ tailWord_3042901).sum := by decide
  have hdescent : baseEnd_3042901 < baseStart_3042901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042902 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3042902 : Nat := 118140960795 + 3042902 * 2 ^ 59
def prefixEnd_3042902 : Nat := 4983230072969 + 3 ^ 40 * 3042902 * 2
def baseEnd_3042902 : Nat := 1562471310527558865630955

theorem tailTrace_3042902 : CollatzResearch.WordTrace tailWord_3042902 prefixEnd_3042902 1562471310527558865630955 := by
  unfold tailWord_3042902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936484601380825945773185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73989169081395476754913973 6936484601380825945773185)
  ·
    refine ⟨5202363451035619459329889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6936484601380825945773185 5202363451035619459329889)
    ·
      refine ⟨3901772588276714594497417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5202363451035619459329889 3901772588276714594497417)
      ·
        refine ⟨2926329441207535945873063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3901772588276714594497417 2926329441207535945873063)
        ·
          refine ⟨4389494161811303918809595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926329441207535945873063 4389494161811303918809595)
          ·
            refine ⟨6584241242716955878214393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389494161811303918809595 6584241242716955878214393)
            ·
              refine ⟨4938180932037716908660795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6584241242716955878214393 4938180932037716908660795)
              ·
                refine ⟨7407271398056575362991193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938180932037716908660795 7407271398056575362991193)
                ·
                  refine ⟨5555453548542431522243395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407271398056575362991193 5555453548542431522243395)
                  ·
                    refine ⟨8333180322813647283365093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5555453548542431522243395 8333180322813647283365093)
                    ·
                      refine ⟨1562471310527558865630955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8333180322813647283365093 1562471310527558865630955)
                      ·
                        rfl

theorem cell23_3042902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3042902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042902 prefixEnd_3042902 := by exact prefixLift 3042902
  have htrace : WordTrace (prefixWord ++ tailWord_3042902) baseStart_3042902 baseEnd_3042902 := by
    simpa [prefixWord, tailWord_3042902, baseEnd_3042902] using wordTrace_append hprefix tailTrace_3042902
  have hstable : (prefixWord ++ tailWord_3042902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042902).length < 2 ^ (prefixWord ++ tailWord_3042902).sum := by decide
  have hdescent : baseEnd_3042902 < baseStart_3042902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042928 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2]
def baseStart_3042928 : Nat := 118140960795 + 3042928 * 2 ^ 59
def prefixEnd_3042928 : Nat := 4983230072969 + 3 ^ 40 * 3042928 * 2
def baseEnd_3042928 : Nat := 1562484661024575763905835

theorem tailTrace_3042928 : CollatzResearch.WordTrace tailWord_3042928 prefixEnd_3042928 1562484661024575763905835 := by
  unfold tailWord_3042928
  simp only [CollatzResearch.WordTrace]
  refine ⟨55492350959999510786408719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73989801279999347715211625 55492350959999510786408719)
  ·
    refine ⟨83238526439999266179613079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55492350959999510786408719 83238526439999266179613079)
    ·
      refine ⟨124857789659998899269419619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83238526439999266179613079 124857789659998899269419619)
      ·
        refine ⟨187286684489998348904129429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124857789659998899269419619 187286684489998348904129429)
        ·
          refine ⟨8779063335468672604881067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187286684489998348904129429 8779063335468672604881067)
          ·
            refine ⟨13168595003203008907321601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779063335468672604881067 13168595003203008907321601)
            ·
              refine ⟨9876446252402256680491201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13168595003203008907321601 9876446252402256680491201)
              ·
                refine ⟨7407334689301692510368401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9876446252402256680491201 7407334689301692510368401)
                ·
                  refine ⟨5555501016976269382776301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407334689301692510368401 5555501016976269382776301)
                  ·
                    refine ⟨2083312881366101018541113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5555501016976269382776301 2083312881366101018541113)
                    ·
                      refine ⟨1562484661024575763905835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083312881366101018541113 1562484661024575763905835)
                      ·
                        rfl

theorem cell23_3042928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2].length) (baseStart_3042928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042928 prefixEnd_3042928 := by exact prefixLift 3042928
  have htrace : WordTrace (prefixWord ++ tailWord_3042928) baseStart_3042928 baseEnd_3042928 := by
    simpa [prefixWord, tailWord_3042928, baseEnd_3042928] using wordTrace_append hprefix tailTrace_3042928
  have hstable : (prefixWord ++ tailWord_3042928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042928).length < 2 ^ (prefixWord ++ tailWord_3042928).sum := by decide
  have hdescent : baseEnd_3042928 < baseStart_3042928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042941 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3042941 : Nat := 118140960795 + 3042941 * 2 ^ 59
def prefixEnd_3042941 : Nat := 4983230072969 + 3 ^ 40 * 3042941 * 2
def baseEnd_3042941 : Nat := 1562491336273084213043275

theorem tailTrace_3042941 : CollatzResearch.WordTrace tailWord_3042941 prefixEnd_3042941 1562491336273084213043275 := by
  unfold tailWord_3042941
  simp only [CollatzResearch.WordTrace]
  refine ⟨110985176068951924793040677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73990117379301283195360451 110985176068951924793040677)
  ·
    refine ⟨20809720512928485898695127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110985176068951924793040677 20809720512928485898695127)
    ·
      refine ⟨31214580769392728848042691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20809720512928485898695127 31214580769392728848042691)
      ·
        refine ⟨46821871154089093272064037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31214580769392728848042691 46821871154089093272064037)
        ·
          refine ⟨8779100841391704988512007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46821871154089093272064037 8779100841391704988512007)
          ·
            refine ⟨13168651262087557482768011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779100841391704988512007 13168651262087557482768011)
            ·
              refine ⟨19752976893131336224152017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13168651262087557482768011 19752976893131336224152017)
              ·
                refine ⟨14814732669848502168114013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19752976893131336224152017 14814732669848502168114013)
                ·
                  refine ⟨5555524751193188313042755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14814732669848502168114013 5555524751193188313042755)
                  ·
                    refine ⟨8333287126789782469564133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5555524751193188313042755 8333287126789782469564133)
                    ·
                      refine ⟨1562491336273084213043275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8333287126789782469564133 1562491336273084213043275)
                      ·
                        rfl

theorem cell23_3042941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3042941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042941 prefixEnd_3042941 := by exact prefixLift 3042941
  have htrace : WordTrace (prefixWord ++ tailWord_3042941) baseStart_3042941 baseEnd_3042941 := by
    simpa [prefixWord, tailWord_3042941, baseEnd_3042941] using wordTrace_append hprefix tailTrace_3042941
  have hstable : (prefixWord ++ tailWord_3042941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042941).length < 2 ^ (prefixWord ++ tailWord_3042941).sum := by decide
  have hdescent : baseEnd_3042941 < baseStart_3042941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042944 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3042944 : Nat := 118140960795 + 3042944 * 2 ^ 59
def prefixEnd_3042944 : Nat := 4983230072969 + 3 ^ 40 * 3042944 * 2
def baseEnd_3042944 : Nat := 1562492876715047701305761

theorem tailTrace_3042944 : CollatzResearch.WordTrace tailWord_3042944 prefixEnd_3042944 1562492876715047701305761 := by
  unfold tailWord_3042944
  simp only [CollatzResearch.WordTrace]
  refine ⟨55492642743970528152699943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73990190325294037536933257 55492642743970528152699943)
  ·
    refine ⟨83238964115955792229049915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55492642743970528152699943 83238964115955792229049915)
    ·
      refine ⟨124858446173933688343574873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83238964115955792229049915 124858446173933688343574873)
      ·
        refine ⟨93643834630450266257681155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124858446173933688343574873 93643834630450266257681155)
        ·
          refine ⟨140465751945675399386521733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93643834630450266257681155 140465751945675399386521733)
          ·
            refine ⟨26337328489814137384972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140465751945675399386521733 26337328489814137384972825)
            ·
              refine ⟨19752996367360603038729619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26337328489814137384972825 19752996367360603038729619)
              ·
                refine ⟨29629494551040904558094429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19752996367360603038729619 29629494551040904558094429)
                ·
                  refine ⟨11111060456640339209285411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29629494551040904558094429 11111060456640339209285411)
                  ·
                    refine ⟨16666590684960508813928117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11111060456640339209285411 16666590684960508813928117)
                    ·
                      refine ⟨1562492876715047701305761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16666590684960508813928117 1562492876715047701305761)
                      ·
                        rfl

theorem cell23_3042944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3042944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042944 prefixEnd_3042944 := by exact prefixLift 3042944
  have htrace : WordTrace (prefixWord ++ tailWord_3042944) baseStart_3042944 baseEnd_3042944 := by
    simpa [prefixWord, tailWord_3042944, baseEnd_3042944] using wordTrace_append hprefix tailTrace_3042944
  have hstable : (prefixWord ++ tailWord_3042944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042944).length < 2 ^ (prefixWord ++ tailWord_3042944).sum := by decide
  have hdescent : baseEnd_3042944 < baseStart_3042944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042951 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3042951 : Nat := 118140960795 + 3042951 * 2 ^ 59
def prefixEnd_3042951 : Nat := 4983230072969 + 3 ^ 40 * 3042951 * 2
def baseEnd_3042951 : Nat := 520832157026543057972743

theorem tailTrace_3042951 : CollatzResearch.WordTrace tailWord_3042951 prefixEnd_3042951 520832157026543057972743 := by
  unfold tailWord_3042951
  simp only [CollatzResearch.WordTrace]
  refine ⟨110985540798915696500904707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73990360532610464333936471 110985540798915696500904707)
  ·
    refine ⟨166478311198373544751357061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110985540798915696500904707 166478311198373544751357061)
    ·
      refine ⟨31214683349695039640879449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166478311198373544751357061 31214683349695039640879449)
      ·
        refine ⟨23411012512271279730659587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31214683349695039640879449 23411012512271279730659587)
        ·
          refine ⟨35116518768406919595989381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23411012512271279730659587 35116518768406919595989381)
          ·
            refine ⟨6584347269076297424248009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35116518768406919595989381 6584347269076297424248009)
            ·
              refine ⟨4938260451807223068186007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6584347269076297424248009 4938260451807223068186007)
              ·
                refine ⟨7407390677710834602279011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938260451807223068186007 7407390677710834602279011)
                ·
                  refine ⟨11111086016566251903418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407390677710834602279011 11111086016566251903418517)
                  ·
                    refine ⟨520832157026543057972743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11111086016566251903418517 520832157026543057972743)
                    ·
                      rfl

theorem cell23_3042951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3042951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042951 prefixEnd_3042951 := by exact prefixLift 3042951
  have htrace : WordTrace (prefixWord ++ tailWord_3042951) baseStart_3042951 baseEnd_3042951 := by
    simpa [prefixWord, tailWord_3042951, baseEnd_3042951] using wordTrace_append hprefix tailTrace_3042951
  have hstable : (prefixWord ++ tailWord_3042951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042951).length < 2 ^ (prefixWord ++ tailWord_3042951).sum := by decide
  have hdescent : baseEnd_3042951 < baseStart_3042951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042962 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3042962 : Nat := 118140960795 + 3042962 * 2 ^ 59
def prefixEnd_3042962 : Nat := 4983230072969 + 3 ^ 40 * 3042962 * 2
def baseEnd_3042962 : Nat := 1562502119366828630880679

theorem tailTrace_3042962 : CollatzResearch.WordTrace tailWord_3042962 prefixEnd_3042962 1562502119366828630880679 := by
  unfold tailWord_3042962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27746485500468961344888785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73990628001250563586370093 27746485500468961344888785)
  ·
    refine ⟨20809864125351721008666589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27746485500468961344888785 20809864125351721008666589)
    ·
      refine ⟨7803699047006895378249971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20809864125351721008666589 7803699047006895378249971)
      ·
        refine ⟨11705548570510343067374957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7803699047006895378249971 11705548570510343067374957)
        ·
          refine ⟨4389580713941378650265609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11705548570510343067374957 4389580713941378650265609)
          ·
            refine ⟨3292185535456033987699207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389580713941378650265609 3292185535456033987699207)
            ·
              refine ⟨4938278303184050981548811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292185535456033987699207 4938278303184050981548811)
              ·
                refine ⟨7407417454776076472323217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938278303184050981548811 7407417454776076472323217)
                ·
                  refine ⟨5555563091082057354242413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407417454776076472323217 5555563091082057354242413)
                  ·
                    refine ⟨2083336159155771507840905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5555563091082057354242413 2083336159155771507840905)
                    ·
                      refine ⟨1562502119366828630880679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083336159155771507840905 1562502119366828630880679)
                      ·
                        rfl

theorem cell23_3042962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3042962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042962 prefixEnd_3042962 := by exact prefixLift 3042962
  have htrace : WordTrace (prefixWord ++ tailWord_3042962) baseStart_3042962 baseEnd_3042962 := by
    simpa [prefixWord, tailWord_3042962, baseEnd_3042962] using wordTrace_append hprefix tailTrace_3042962
  have hstable : (prefixWord ++ tailWord_3042962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042962).length < 2 ^ (prefixWord ++ tailWord_3042962).sum := by decide
  have hdescent : baseEnd_3042962 < baseStart_3042962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042972 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_3042972 : Nat := 118140960795 + 3042972 * 2 ^ 59
def prefixEnd_3042972 : Nat := 4983230072969 + 3 ^ 40 * 3042972 * 2
def baseEnd_3042972 : Nat := 520835751391124530585211

theorem tailTrace_3042972 : CollatzResearch.WordTrace tailWord_3042972 prefixEnd_3042972 520835751391124530585211 := by
  unfold tailWord_3042972
  simp only [CollatzResearch.WordTrace]
  refine ⟨55493153365919808543709585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73990871154559744724946113 55493153365919808543709585)
  ·
    refine ⟨41619865024439856407782189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55493153365919808543709585 41619865024439856407782189)
    ·
      refine ⟨15607449384164946152918321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41619865024439856407782189 15607449384164946152918321)
      ·
        refine ⟨11705587038123709614688741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15607449384164946152918321 11705587038123709614688741)
        ·
          refine ⟨2194797569648195552754139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11705587038123709614688741 2194797569648195552754139)
          ·
            refine ⟨3292196354472293329131209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194797569648195552754139 3292196354472293329131209)
            ·
              refine ⟨2469147265854219996848407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292196354472293329131209 2469147265854219996848407)
              ·
                refine ⟨3703720898781329995272611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469147265854219996848407 3703720898781329995272611)
                ·
                  refine ⟨5555581348171994992908917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703720898781329995272611 5555581348171994992908917)
                  ·
                    refine ⟨520835751391124530585211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5555581348171994992908917 520835751391124530585211)
                    ·
                      rfl

theorem cell23_3042972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_3042972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042972 prefixEnd_3042972 := by exact prefixLift 3042972
  have htrace : WordTrace (prefixWord ++ tailWord_3042972) baseStart_3042972 baseEnd_3042972 := by
    simpa [prefixWord, tailWord_3042972, baseEnd_3042972] using wordTrace_append hprefix tailTrace_3042972
  have hstable : (prefixWord ++ tailWord_3042972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042972).length < 2 ^ (prefixWord ++ tailWord_3042972).sum := by decide
  have hdescent : baseEnd_3042972 < baseStart_3042972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042975 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3042975 : Nat := 118140960795 + 3042975 * 2 ^ 59
def prefixEnd_3042975 : Nat := 4983230072969 + 3 ^ 40 * 3042975 * 2
def baseEnd_3042975 : Nat := 1562508794615337080018119

theorem tailTrace_3042975 : CollatzResearch.WordTrace tailWord_3042975 prefixEnd_3042975 1562508794615337080018119 := by
  unfold tailWord_3042975
  simp only [CollatzResearch.WordTrace]
  refine ⟨110986416150828748599778379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73990944100552499066518919 110986416150828748599778379)
  ·
    refine ⟨166479624226243122899667569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110986416150828748599778379 166479624226243122899667569)
    ·
      refine ⟨124859718169682342174750677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166479624226243122899667569 124859718169682342174750677)
      ·
        refine ⟨2926399644601929894720719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 124859718169682342174750677 2926399644601929894720719)
        ·
          refine ⟨4389599466902894842081079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926399644601929894720719 4389599466902894842081079)
          ·
            refine ⟨6584399200354342263121619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389599466902894842081079 6584399200354342263121619)
            ·
              refine ⟨9876598800531513394682429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584399200354342263121619 9876598800531513394682429)
              ·
                refine ⟨3703724550199317523005911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9876598800531513394682429 3703724550199317523005911)
                ·
                  refine ⟨5555586825298976284508867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703724550199317523005911 5555586825298976284508867)
                  ·
                    refine ⟨8333380237948464426763301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5555586825298976284508867 8333380237948464426763301)
                    ·
                      refine ⟨1562508794615337080018119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8333380237948464426763301 1562508794615337080018119)
                      ·
                        rfl

theorem cell23_3042975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3042975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042975 prefixEnd_3042975 := by exact prefixLift 3042975
  have htrace : WordTrace (prefixWord ++ tailWord_3042975) baseStart_3042975 baseEnd_3042975 := by
    simpa [prefixWord, tailWord_3042975, baseEnd_3042975] using wordTrace_append hprefix tailTrace_3042975
  have hstable : (prefixWord ++ tailWord_3042975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042975).length < 2 ^ (prefixWord ++ tailWord_3042975).sum := by decide
  have hdescent : baseEnd_3042975 < baseStart_3042975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042994 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3042994 : Nat := 118140960795 + 3042994 * 2 ^ 59
def prefixEnd_3042994 : Nat := 4983230072969 + 3 ^ 40 * 3042994 * 2
def baseEnd_3042994 : Nat := 520839516915924168560177

theorem tailTrace_3042994 : CollatzResearch.WordTrace tailWord_3042994 prefixEnd_3042994 520839516915924168560177 := by
  unfold tailWord_3042994
  simp only [CollatzResearch.WordTrace]
  refine ⟨27746777284439978711180009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73991406091839943229813357 27746777284439978711180009)
  ·
    refine ⟨20810082963329984033385007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27746777284439978711180009 20810082963329984033385007)
    ·
      refine ⟨31215124444994976050077511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20810082963329984033385007 31215124444994976050077511)
      ·
        refine ⟨46822686667492464075116267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31215124444994976050077511 46822686667492464075116267)
        ·
          refine ⟨70234030001238696112674401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46822686667492464075116267 70234030001238696112674401)
          ·
            refine ⟨52675522500929022084505801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70234030001238696112674401 52675522500929022084505801)
            ·
              refine ⟨39506641875696766563379351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52675522500929022084505801 39506641875696766563379351)
              ·
                refine ⟨59259962813545149845069027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39506641875696766563379351 59259962813545149845069027)
                ·
                  refine ⟨88889944220317724767603541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59259962813545149845069027 88889944220317724767603541)
                  ·
                    refine ⟨520839516915924168560177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 88889944220317724767603541 520839516915924168560177)
                    ·
                      rfl

theorem cell23_3042994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3042994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3042994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3042994 prefixEnd_3042994 := by exact prefixLift 3042994
  have htrace : WordTrace (prefixWord ++ tailWord_3042994) baseStart_3042994 baseEnd_3042994 := by
    simpa [prefixWord, tailWord_3042994, baseEnd_3042994] using wordTrace_append hprefix tailTrace_3042994
  have hstable : (prefixWord ++ tailWord_3042994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042994).length < 2 ^ (prefixWord ++ tailWord_3042994).sum := by decide
  have hdescent : baseEnd_3042994 < baseStart_3042994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043024 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_3043024 : Nat := 118140960795 + 3043024 * 2 ^ 59
def prefixEnd_3043024 : Nat := 4983230072969 + 3 ^ 40 * 3043024 * 2
def baseEnd_3043024 : Nat := 520844651722469129435131

theorem tailTrace_3043024 : CollatzResearch.WordTrace tailWord_3043024 prefixEnd_3043024 520844651722469129435131 := by
  unfold tailWord_3043024
  simp only [CollatzResearch.WordTrace]
  refine ⟨55494101663825614984156063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73992135551767486645541417 55494101663825614984156063)
  ·
    refine ⟨83241152495738422476234095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55494101663825614984156063 83241152495738422476234095)
    ·
      refine ⟨124861728743607633714351143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83241152495738422476234095 124861728743607633714351143)
      ·
        refine ⟨187292593115411450571526715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124861728743607633714351143 187292593115411450571526715)
        ·
          refine ⟨280938889673117175857290073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187292593115411450571526715 280938889673117175857290073)
          ·
            refine ⟨210704167254837881892967555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280938889673117175857290073 210704167254837881892967555)
            ·
              refine ⟨316056250882256822839451333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210704167254837881892967555 316056250882256822839451333)
              ·
                refine ⟨59260547040423154282397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316056250882256822839451333 59260547040423154282397125)
                ·
                  refine ⟨11111352570079341427949461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59260547040423154282397125 11111352570079341427949461)
                  ·
                    refine ⟨520844651722469129435131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11111352570079341427949461 520844651722469129435131)
                    ·
                      rfl

theorem cell23_3043024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_3043024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043024 prefixEnd_3043024 := by exact prefixLift 3043024
  have htrace : WordTrace (prefixWord ++ tailWord_3043024) baseStart_3043024 baseEnd_3043024 := by
    simpa [prefixWord, tailWord_3043024, baseEnd_3043024] using wordTrace_append hprefix tailTrace_3043024
  have hstable : (prefixWord ++ tailWord_3043024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043024).length < 2 ^ (prefixWord ++ tailWord_3043024).sum := by decide
  have hdescent : baseEnd_3043024 < baseStart_3043024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043081 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_3043081 : Nat := 118140960795 + 3043081 * 2 ^ 59
def prefixEnd_3043081 : Nat := 4983230072969 + 3 ^ 40 * 3043081 * 2
def baseEnd_3043081 : Nat := 1562563223564713665292631

theorem tailTrace_3043081 : CollatzResearch.WordTrace tailWord_3043081 prefixEnd_3043081 1562563223564713665292631 := by
  unfold tailWord_3043081
  simp only [CollatzResearch.WordTrace]
  refine ⟨110990282288444728703137097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73993521525629819135424731 110990282288444728703137097)
  ·
    refine ⟨83242711716333546527352823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110990282288444728703137097 83242711716333546527352823)
    ·
      refine ⟨124864067574500319791029235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83242711716333546527352823 124864067574500319791029235)
      ·
        refine ⟨187296101361750479686543853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124864067574500319791029235 187296101361750479686543853)
        ·
          refine ⟨70236038010656429882453945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187296101361750479686543853 70236038010656429882453945)
          ·
            refine ⟨52677028507992322411840459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70236038010656429882453945 52677028507992322411840459)
            ·
              refine ⟨79015542761988483617760689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52677028507992322411840459 79015542761988483617760689)
              ·
                refine ⟨59261657071491362713320517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79015542761988483617760689 59261657071491362713320517)
                ·
                  refine ⟨11111560700904630508747597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59261657071491362713320517 11111560700904630508747597)
                  ·
                    refine ⟨4166835262839236440780349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11111560700904630508747597 4166835262839236440780349)
                    ·
                      refine ⟨1562563223564713665292631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4166835262839236440780349 1562563223564713665292631)
                      ·
                        rfl

theorem cell23_3043081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_3043081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043081 prefixEnd_3043081 := by exact prefixLift 3043081
  have htrace : WordTrace (prefixWord ++ tailWord_3043081) baseStart_3043081 baseEnd_3043081 := by
    simpa [prefixWord, tailWord_3043081, baseEnd_3043081] using wordTrace_append hprefix tailTrace_3043081
  have hstable : (prefixWord ++ tailWord_3043081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043081).length < 2 ^ (prefixWord ++ tailWord_3043081).sum := by decide
  have hdescent : baseEnd_3043081 < baseStart_3043081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043105 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 5]
def baseStart_3043105 : Nat := 118140960795 + 3043105 * 2 ^ 59
def prefixEnd_3043105 : Nat := 4983230072969 + 3 ^ 40 * 3043105 * 2
def baseEnd_3043105 : Nat := 173619505233380174599169

theorem tailTrace_3043105 : CollatzResearch.WordTrace tailWord_3043105 prefixEnd_3043105 173619505233380174599169 := by
  unfold tailWord_3043105
  simp only [CollatzResearch.WordTrace]
  refine ⟨110991157640357780802010769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73994105093571853868007179 110991157640357780802010769)
  ·
    refine ⟨83243368230268335601508077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110991157640357780802010769 83243368230268335601508077)
    ·
      refine ⟨31216263086350625850565529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83243368230268335601508077 31216263086350625850565529)
      ·
        refine ⟨23412197314762969387924147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31216263086350625850565529 23412197314762969387924147)
        ·
          refine ⟨35118295972144454081886221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23412197314762969387924147 35118295972144454081886221)
          ·
            refine ⟨13169360989554170280707333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35118295972144454081886221 13169360989554170280707333)
            ·
              refine ⟨2469255185541406927632625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13169360989554170280707333 2469255185541406927632625)
              ·
                refine ⟨1851941389156055195724469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469255185541406927632625 1851941389156055195724469)
                ·
                  refine ⟨173619505233380174599169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851941389156055195724469 173619505233380174599169)
                  ·
                    rfl

theorem cell23_3043105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 5].length) (baseStart_3043105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043105 prefixEnd_3043105 := by exact prefixLift 3043105
  have htrace : WordTrace (prefixWord ++ tailWord_3043105) baseStart_3043105 baseEnd_3043105 := by
    simpa [prefixWord, tailWord_3043105, baseEnd_3043105] using wordTrace_append hprefix tailTrace_3043105
  have hstable : (prefixWord ++ tailWord_3043105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043105).length < 2 ^ (prefixWord ++ tailWord_3043105).sum := by decide
  have hdescent : baseEnd_3043105 < baseStart_3043105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043135 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 2, 5]
def baseStart_3043135 : Nat := 118140960795 + 3043135 * 2 ^ 59
def prefixEnd_3043135 : Nat := 4983230072969 + 3 ^ 40 * 3043135 * 2
def baseEnd_3043135 : Nat := 520863650506685484672461

theorem tailTrace_3043135 : CollatzResearch.WordTrace tailWord_3043135 prefixEnd_3043135 520863650506685484672461 := by
  unfold tailWord_3043135
  simp only [CollatzResearch.WordTrace]
  refine ⟨110992251830249095925602859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73994834553499397283735239 110992251830249095925602859)
  ·
    refine ⟨166488377745373643888404289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110992251830249095925602859 166488377745373643888404289)
    ·
      refine ⟨124866283309030232916303217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166488377745373643888404289 124866283309030232916303217)
      ·
        refine ⟨93649712481772674687227413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124866283309030232916303217 93649712481772674687227413)
        ·
          refine ⟨4389830272583094125963785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93649712481772674687227413 4389830272583094125963785)
          ·
            refine ⟨3292372704437320594472839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389830272583094125963785 3292372704437320594472839)
            ·
              refine ⟨4938559056655980891709259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292372704437320594472839 4938559056655980891709259)
              ·
                refine ⟨7407838584983971337563889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938559056655980891709259 7407838584983971337563889)
                ·
                  refine ⟨5555878938737978503172917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407838584983971337563889 5555878938737978503172917)
                  ·
                    refine ⟨520863650506685484672461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5555878938737978503172917 520863650506685484672461)
                    ·
                      rfl

theorem cell23_3043135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_3043135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043135 prefixEnd_3043135 := by exact prefixLift 3043135
  have htrace : WordTrace (prefixWord ++ tailWord_3043135) baseStart_3043135 baseEnd_3043135 := by
    simpa [prefixWord, tailWord_3043135, baseEnd_3043135] using wordTrace_append hprefix tailTrace_3043135
  have hstable : (prefixWord ++ tailWord_3043135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043135).length < 2 ^ (prefixWord ++ tailWord_3043135).sum := by decide
  have hdescent : baseEnd_3043135 < baseStart_3043135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043161 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 8]
def baseStart_3043161 : Nat := 118140960795 + 3043161 * 2 ^ 59
def prefixEnd_3043161 : Nat := 4983230072969 + 3 ^ 40 * 3043161 * 2
def baseEnd_3043161 : Nat := 173622700224119261365807

theorem tailTrace_3043161 : CollatzResearch.WordTrace tailWord_3043161 prefixEnd_3043161 173622700224119261365807 := by
  unfold tailWord_3043161
  simp only [CollatzResearch.WordTrace]
  refine ⟨110993200128154902366049337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73995466752103268244032891 110993200128154902366049337)
  ·
    refine ⟨83244900096116176774537003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110993200128154902366049337 83244900096116176774537003)
    ·
      refine ⟨124867350144174265161805505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83244900096116176774537003 124867350144174265161805505)
      ·
        refine ⟨93650512608130698871354129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124867350144174265161805505 93650512608130698871354129)
        ·
          refine ⟨70237884456098024153515597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93650512608130698871354129 70237884456098024153515597)
          ·
            refine ⟨26339206671036759057568349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70237884456098024153515597 26339206671036759057568349)
            ·
              refine ⟨9877202501638784646588131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26339206671036759057568349 9877202501638784646588131)
              ·
                refine ⟨14815803752458176969882197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9877202501638784646588131 14815803752458176969882197)
                ·
                  refine ⟨173622700224119261365807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14815803752458176969882197 173622700224119261365807)
                  ·
                    rfl

theorem cell23_3043161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_3043161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043161 prefixEnd_3043161 := by exact prefixLift 3043161
  have htrace : WordTrace (prefixWord ++ tailWord_3043161) baseStart_3043161 baseEnd_3043161 := by
    simpa [prefixWord, tailWord_3043161, baseEnd_3043161] using wordTrace_append hprefix tailTrace_3043161
  have hstable : (prefixWord ++ tailWord_3043161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043161).length < 2 ^ (prefixWord ++ tailWord_3043161).sum := by decide
  have hdescent : baseEnd_3043161 < baseStart_3043161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043251 : List Nat := [1, 1, 1, 2, 3, 1, 3, 11]
def baseStart_3043251 : Nat := 118140960795 + 3043251 * 2 ^ 59
def prefixEnd_3043251 : Nat := 4983230072969 + 3 ^ 40 * 3043251 * 2
def baseEnd_3043251 : Nat := 57875945010221407413587

theorem tailTrace_3043251 : CollatzResearch.WordTrace tailWord_3043251 prefixEnd_3043251 57875945010221407413587 := by
  unfold tailWord_3043251
  simp only [CollatzResearch.WordTrace]
  refine ⟨110996482697828847736825607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73997655131885898491217071 110996482697828847736825607)
  ·
    refine ⟨166494724046743271605238411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110996482697828847736825607 166494724046743271605238411)
    ·
      refine ⟨249742086070114907407857617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166494724046743271605238411 249742086070114907407857617)
      ·
        refine ⟨187306564552586180555893213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249742086070114907407857617 187306564552586180555893213)
        ·
          refine ⟨70239961707219817708459955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187306564552586180555893213 70239961707219817708459955)
          ·
            refine ⟨105359942560829726562689933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70239961707219817708459955 105359942560829726562689933)
            ·
              refine ⟨39509978460311147461008725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105359942560829726562689933 39509978460311147461008725)
              ·
                refine ⟨57875945010221407413587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39509978460311147461008725 57875945010221407413587)
                ·
                  rfl

theorem cell23_3043251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 11].length) (baseStart_3043251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043251 prefixEnd_3043251 := by exact prefixLift 3043251
  have htrace : WordTrace (prefixWord ++ tailWord_3043251) baseStart_3043251 baseEnd_3043251 := by
    simpa [prefixWord, tailWord_3043251, baseEnd_3043251] using wordTrace_append hprefix tailTrace_3043251
  have hstable : (prefixWord ++ tailWord_3043251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043251).length < 2 ^ (prefixWord ++ tailWord_3043251).sum := by decide
  have hdescent : baseEnd_3043251 < baseStart_3043251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043272 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_3043272 : Nat := 118140960795 + 3043272 * 2 ^ 59
def prefixEnd_3043272 : Nat := 4983230072969 + 3 ^ 40 * 3043272 * 2
def baseEnd_3043272 : Nat := 520887099456574139334751

theorem tailTrace_3043272 : CollatzResearch.WordTrace tailWord_3043272 prefixEnd_3043272 520887099456574139334751 := by
  unfold tailWord_3043272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55498624315376384161670035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73998165753835178882226713 55498624315376384161670035)
  ·
    refine ⟨83247936473064576242505053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55498624315376384161670035 83247936473064576242505053)
    ·
      refine ⟨31217976177399216090939395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83247936473064576242505053 31217976177399216090939395)
      ·
        refine ⟨46826964266098824136409093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31217976177399216090939395 46826964266098824136409093)
        ·
          refine ⟨8780055799893529525576705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46826964266098824136409093 8780055799893529525576705)
          ·
            refine ⟨6585041849920147144182529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8780055799893529525576705 6585041849920147144182529)
            ·
              refine ⟨4938781387440110358136897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585041849920147144182529 4938781387440110358136897)
              ·
                refine ⟨3704086040580082768602673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4938781387440110358136897 3704086040580082768602673)
                ·
                  refine ⟨2778064530435062076452005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704086040580082768602673 2778064530435062076452005)
                  ·
                    refine ⟨520887099456574139334751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2778064530435062076452005 520887099456574139334751)
                    ·
                      rfl

theorem cell23_3043272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_3043272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043272 prefixEnd_3043272 := by exact prefixLift 3043272
  have htrace : WordTrace (prefixWord ++ tailWord_3043272) baseStart_3043272 baseEnd_3043272 := by
    simpa [prefixWord, tailWord_3043272, baseEnd_3043272] using wordTrace_append hprefix tailTrace_3043272
  have hstable : (prefixWord ++ tailWord_3043272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043272).length < 2 ^ (prefixWord ++ tailWord_3043272).sum := by decide
  have hdescent : baseEnd_3043272 < baseStart_3043272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043279 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 1, 2, 2]
def baseStart_3043279 : Nat := 118140960795 + 3043279 * 2 ^ 59
def prefixEnd_3043279 : Nat := 4983230072969 + 3 ^ 40 * 3043279 * 2
def baseEnd_3043279 : Nat := 1562664892734303890616721

theorem tailTrace_3043279 : CollatzResearch.WordTrace tailWord_3043279 prefixEnd_3043279 1562664892734303890616721 := by
  unfold tailWord_3043279
  simp only [CollatzResearch.WordTrace]
  refine ⟨110997503941727408518844891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73998335961151605679229927 110997503941727408518844891)
  ·
    refine ⟨166496255912591112778267337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110997503941727408518844891 166496255912591112778267337)
    ·
      refine ⟨124872191934443334583700503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166496255912591112778267337 124872191934443334583700503)
      ·
        refine ⟨187308287901665001875550755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124872191934443334583700503 187308287901665001875550755)
        ·
          refine ⟨280962431852497502813326133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187308287901665001875550755 280962431852497502813326133)
          ·
            refine ⟨26340227986171640888749325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280962431852497502813326133 26340227986171640888749325)
            ·
              refine ⟨9877585494814365333280997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26340227986171640888749325 9877585494814365333280997)
              ·
                refine ⟨1852047280277693499990187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9877585494814365333280997 1852047280277693499990187)
                ·
                  refine ⟨2778070920416540249985281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852047280277693499990187 2778070920416540249985281)
                  ·
                    refine ⟨2083553190312405187488961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2778070920416540249985281 2083553190312405187488961)
                    ·
                      refine ⟨1562664892734303890616721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083553190312405187488961 1562664892734303890616721)
                      ·
                        rfl

theorem cell23_3043279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 2, 2].length) (baseStart_3043279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043279 prefixEnd_3043279 := by exact prefixLift 3043279
  have htrace : WordTrace (prefixWord ++ tailWord_3043279) baseStart_3043279 baseEnd_3043279 := by
    simpa [prefixWord, tailWord_3043279, baseEnd_3043279] using wordTrace_append hprefix tailTrace_3043279
  have hstable : (prefixWord ++ tailWord_3043279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043279).length < 2 ^ (prefixWord ++ tailWord_3043279).sum := by decide
  have hdescent : baseEnd_3043279 < baseStart_3043279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043285 : List Nat := [1, 3, 2, 3, 2, 3, 1, 8]
def baseStart_3043285 : Nat := 118140960795 + 3043285 * 2 ^ 59
def prefixEnd_3043285 : Nat := 4983230072969 + 3 ^ 40 * 3043285 * 2
def baseEnd_3043285 : Nat := 57876591615490032116359

theorem tailTrace_3043285 : CollatzResearch.WordTrace tailWord_3043285 prefixEnd_3043285 57876591615490032116359 := by
  unfold tailWord_3043285
  simp only [CollatzResearch.WordTrace]
  refine ⟨110997722779705671543563309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73998481853137114362375539 110997722779705671543563309)
  ·
    refine ⟨41624146042389626828836241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110997722779705671543563309 41624146042389626828836241)
    ·
      refine ⟨31218109531792220121627181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41624146042389626828836241 31218109531792220121627181)
      ·
        refine ⟨11706791074422082545610193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31218109531792220121627181 11706791074422082545610193)
        ·
          refine ⟨8780093305816561909207645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11706791074422082545610193 8780093305816561909207645)
          ·
            refine ⟨3292534989681210715952867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8780093305816561909207645 3292534989681210715952867)
            ·
              refine ⟨4938802484521816073929301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292534989681210715952867 4938802484521816073929301)
              ·
                refine ⟨57876591615490032116359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4938802484521816073929301 57876591615490032116359)
                ·
                  rfl

theorem cell23_3043285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 8].length) (baseStart_3043285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043285 prefixEnd_3043285 := by exact prefixLift 3043285
  have htrace : WordTrace (prefixWord ++ tailWord_3043285) baseStart_3043285 baseEnd_3043285 := by
    simpa [prefixWord, tailWord_3043285, baseEnd_3043285] using wordTrace_append hprefix tailTrace_3043285
  have hstable : (prefixWord ++ tailWord_3043285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043285).length < 2 ^ (prefixWord ++ tailWord_3043285).sum := by decide
  have hdescent : baseEnd_3043285 < baseStart_3043285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043295 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3043295 : Nat := 118140960795 + 3043295 * 2 ^ 59
def prefixEnd_3043295 : Nat := 4983230072969 + 3 ^ 40 * 3043295 * 2
def baseEnd_3043295 : Nat := 1562673108424775828016647

theorem tailTrace_3043295 : CollatzResearch.WordTrace tailWord_3043295 prefixEnd_3043295 1562673108424775828016647 := by
  unfold tailWord_3043295
  simp only [CollatzResearch.WordTrace]
  refine ⟨110998087509669443251427339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73998725006446295500951559 110998087509669443251427339)
  ·
    refine ⟨166497131264504164877141009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110998087509669443251427339 166497131264504164877141009)
    ·
      refine ⟨124872848448378123657855757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166497131264504164877141009 124872848448378123657855757)
      ·
        refine ⟨46827318168141796371695909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124872848448378123657855757 46827318168141796371695909)
        ·
          refine ⟨8780122156526586819692983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46827318168141796371695909 8780122156526586819692983)
          ·
            refine ⟨13170183234789880229539475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8780122156526586819692983 13170183234789880229539475)
            ·
              refine ⟨19755274852184820344309213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13170183234789880229539475 19755274852184820344309213)
              ·
                refine ⟨7408228069569307629115955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19755274852184820344309213 7408228069569307629115955)
                ·
                  refine ⟨11112342104353961443673933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408228069569307629115955 11112342104353961443673933)
                  ·
                    refine ⟨4167128289132735541377725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11112342104353961443673933 4167128289132735541377725)
                    ·
                      refine ⟨1562673108424775828016647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4167128289132735541377725 1562673108424775828016647)
                      ·
                        rfl

theorem cell23_3043295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3043295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043295 prefixEnd_3043295 := by exact prefixLift 3043295
  have htrace : WordTrace (prefixWord ++ tailWord_3043295) baseStart_3043295 baseEnd_3043295 := by
    simpa [prefixWord, tailWord_3043295, baseEnd_3043295] using wordTrace_append hprefix tailTrace_3043295
  have hstable : (prefixWord ++ tailWord_3043295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043295).length < 2 ^ (prefixWord ++ tailWord_3043295).sum := by decide
  have hdescent : baseEnd_3043295 < baseStart_3043295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043375 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 5]
def baseStart_3043375 : Nat := 118140960795 + 3043375 * 2 ^ 59
def prefixEnd_3043375 : Nat := 4983230072969 + 3 ^ 40 * 3043375 * 2
def baseEnd_3043375 : Nat := 173634909653015057224031

theorem tailTrace_3043375 : CollatzResearch.WordTrace tailWord_3043375 prefixEnd_3043375 173634909653015057224031 := by
  unfold tailWord_3043375
  simp only [CollatzResearch.WordTrace]
  refine ⟨111001005349379616914339579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74000670232919744609559719 111001005349379616914339579)
  ·
    refine ⟨166501508024069425371509369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111001005349379616914339579 166501508024069425371509369)
    ·
      refine ⟨124876131018052069028632027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166501508024069425371509369 124876131018052069028632027)
      ·
        refine ⟨187314196527078103542948041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124876131018052069028632027 187314196527078103542948041)
        ·
          refine ⟨140485647395308577657211031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187314196527078103542948041 140485647395308577657211031)
          ·
            refine ⟨210728471092962866485816547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140485647395308577657211031 210728471092962866485816547)
            ·
              refine ⟨316092706639444299728724821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210728471092962866485816547 316092706639444299728724821)
              ·
                refine ⟨1852105702965493943722997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 316092706639444299728724821 1852105702965493943722997)
                ·
                  refine ⟨173634909653015057224031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852105702965493943722997 173634909653015057224031)
                  ·
                    rfl

theorem cell23_3043375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 5].length) (baseStart_3043375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043375 prefixEnd_3043375 := by exact prefixLift 3043375
  have htrace : WordTrace (prefixWord ++ tailWord_3043375) baseStart_3043375 baseEnd_3043375 := by
    simpa [prefixWord, tailWord_3043375, baseEnd_3043375] using wordTrace_append hprefix tailTrace_3043375
  have hstable : (prefixWord ++ tailWord_3043375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043375).length < 2 ^ (prefixWord ++ tailWord_3043375).sum := by decide
  have hdescent : baseEnd_3043375 < baseStart_3043375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043442 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3043442 : Nat := 118140960795 + 3043442 * 2 ^ 59
def prefixEnd_3043442 : Nat := 4983230072969 + 3 ^ 40 * 3043442 * 2
def baseEnd_3043442 : Nat := 1562748590080986752878471

theorem tailTrace_3043442 : CollatzResearch.WordTrace tailWord_3043442 prefixEnd_3043442 1562748590080986752878471 := by
  unfold tailWord_3043442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27750862260034221839257145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74002299360091258238019053 27750862260034221839257145)
  ·
    refine ⟨20813146695025666379442859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27750862260034221839257145 20813146695025666379442859)
    ·
      refine ⟨31219720042538499569164289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20813146695025666379442859 31219720042538499569164289)
      ·
        refine ⟨23414790031903874676873217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31219720042538499569164289 23414790031903874676873217)
        ·
          refine ⟨17561092523927906007654913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23414790031903874676873217 17561092523927906007654913)
          ·
            refine ⟨13170819392945929505741185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17561092523927906007654913 13170819392945929505741185)
            ·
              refine ⟨9878114544709447129305889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13170819392945929505741185 9878114544709447129305889)
              ·
                refine ⟨7408585908532085346979417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9878114544709447129305889 7408585908532085346979417)
                ·
                  refine ⟨5556439431399064010234563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7408585908532085346979417 5556439431399064010234563)
                  ·
                    refine ⟨8334659147098596015351845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5556439431399064010234563 8334659147098596015351845)
                    ·
                      refine ⟨1562748590080986752878471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8334659147098596015351845 1562748590080986752878471)
                      ·
                        rfl

theorem cell23_3043442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3043442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043442 prefixEnd_3043442 := by exact prefixLift 3043442
  have htrace : WordTrace (prefixWord ++ tailWord_3043442) baseStart_3043442 baseEnd_3043442 := by
    simpa [prefixWord, tailWord_3043442, baseEnd_3043442] using wordTrace_append hprefix tailTrace_3043442
  have hstable : (prefixWord ++ tailWord_3043442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043442).length < 2 ^ (prefixWord ++ tailWord_3043442).sum := by decide
  have hdescent : baseEnd_3043442 < baseStart_3043442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043465 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 6]
def baseStart_3043465 : Nat := 118140960795 + 3043465 * 2 ^ 59
def prefixEnd_3043465 : Nat := 4983230072969 + 3 ^ 40 * 3043465 * 2
def baseEnd_3043465 : Nat := 173640044459560018098985

theorem tailTrace_3043465 : CollatzResearch.WordTrace tailWord_3043465 prefixEnd_3043465 173640044459560018098985 := by
  unfold tailWord_3043465
  simp only [CollatzResearch.WordTrace]
  refine ⟨111004287919053562285115849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74002858612702374856743899 111004287919053562285115849)
  ·
    refine ⟨83253215939290171713836887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111004287919053562285115849 83253215939290171713836887)
    ·
      refine ⟨124879823908935257570755331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83253215939290171713836887 124879823908935257570755331)
      ·
        refine ⟨187319735863402886356132997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124879823908935257570755331 187319735863402886356132997)
        ·
          refine ⟨35122450474388041191774937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187319735863402886356132997 35122450474388041191774937)
          ·
            refine ⟨26341837855791030893831203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35122450474388041191774937 26341837855791030893831203)
            ·
              refine ⟨39512756783686546340746805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26341837855791030893831203 39512756783686546340746805)
              ·
                refine ⟨3704320948470613719445013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39512756783686546340746805 3704320948470613719445013)
                ·
                  refine ⟨173640044459560018098985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3704320948470613719445013 173640044459560018098985)
                  ·
                    rfl

theorem cell23_3043465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_3043465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043465 prefixEnd_3043465 := by exact prefixLift 3043465
  have htrace : WordTrace (prefixWord ++ tailWord_3043465) baseStart_3043465 baseEnd_3043465 := by
    simpa [prefixWord, tailWord_3043465, baseEnd_3043465] using wordTrace_append hprefix tailTrace_3043465
  have hstable : (prefixWord ++ tailWord_3043465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043465).length < 2 ^ (prefixWord ++ tailWord_3043465).sum := by decide
  have hdescent : baseEnd_3043465 < baseStart_3043465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043535 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_3043535 : Nat := 118140960795 + 3043535 * 2 ^ 59
def prefixEnd_3043535 : Nat := 4983230072969 + 3 ^ 40 * 3043535 * 2
def baseEnd_3043535 : Nat := 1562796343781854889015543

theorem tailTrace_3043535 : CollatzResearch.WordTrace tailWord_3043535 prefixEnd_3043535 1562796343781854889015543 := by
  unfold tailWord_3043535
  simp only [CollatzResearch.WordTrace]
  refine ⟨111006841028799964240164059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74004560685866642826776039 111006841028799964240164059)
  ·
    refine ⟨166510261543199946360246089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111006841028799964240164059 166510261543199946360246089)
    ·
      refine ⟨124882696157399959770184567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166510261543199946360246089 124882696157399959770184567)
      ·
        refine ⟨187324044236099939655276851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124882696157399959770184567 187324044236099939655276851)
        ·
          refine ⟨280986066354149909482915277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187324044236099939655276851 280986066354149909482915277)
          ·
            refine ⟨105369774882806216056093229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280986066354149909482915277 105369774882806216056093229)
            ·
              refine ⟨39513665581052331021034961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105369774882806216056093229 39513665581052331021034961)
              ·
                refine ⟨29635249185789248265776221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39513665581052331021034961 29635249185789248265776221)
                ·
                  refine ⟨11113218444670968099666083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29635249185789248265776221 11113218444670968099666083)
                  ·
                    refine ⟨16669827667006452149499125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11113218444670968099666083 16669827667006452149499125)
                    ·
                      refine ⟨1562796343781854889015543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16669827667006452149499125 1562796343781854889015543)
                      ·
                        rfl

theorem cell23_3043535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_3043535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043535 prefixEnd_3043535 := by exact prefixLift 3043535
  have htrace : WordTrace (prefixWord ++ tailWord_3043535) baseStart_3043535 baseEnd_3043535 := by
    simpa [prefixWord, tailWord_3043535, baseEnd_3043535] using wordTrace_append hprefix tailTrace_3043535
  have hstable : (prefixWord ++ tailWord_3043535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043535).length < 2 ^ (prefixWord ++ tailWord_3043535).sum := by decide
  have hdescent : baseEnd_3043535 < baseStart_3043535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043552 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3043552 : Nat := 118140960795 + 3043552 * 2 ^ 59
def prefixEnd_3043552 : Nat := 4983230072969 + 3 ^ 40 * 3043552 * 2
def baseEnd_3043552 : Nat := 1562805072952981322502965

theorem tailTrace_3043552 : CollatzResearch.WordTrace tailWord_3043552 prefixEnd_3043552 1562805072952981322502965 := by
  unfold tailWord_3043552
  simp only [CollatzResearch.WordTrace]
  refine ⟨55503730534869188071766455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74004974046492250762355273 55503730534869188071766455)
  ·
    refine ⟨83255595802303782107649683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55503730534869188071766455 83255595802303782107649683)
    ·
      refine ⟨124883393703455673161474525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83255595802303782107649683 124883393703455673161474525)
      ·
        refine ⟨46831272638795877435552947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124883393703455673161474525 46831272638795877435552947)
        ·
          refine ⟨70246908958193816153329421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46831272638795877435552947 70246908958193816153329421)
          ·
            refine ⟨26342590859322681057498533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70246908958193816153329421 26342590859322681057498533)
            ·
              refine ⟨4939235786123002698280975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26342590859322681057498533 4939235786123002698280975)
              ·
                refine ⟨7408853679184504047421463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939235786123002698280975 7408853679184504047421463)
                ·
                  refine ⟨11113280518776756071132195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408853679184504047421463 11113280518776756071132195)
                  ·
                    refine ⟨16669920778165134106698293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11113280518776756071132195 16669920778165134106698293)
                    ·
                      refine ⟨1562805072952981322502965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16669920778165134106698293 1562805072952981322502965)
                      ·
                        rfl

theorem cell23_3043552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3043552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043552 prefixEnd_3043552 := by exact prefixLift 3043552
  have htrace : WordTrace (prefixWord ++ tailWord_3043552) baseStart_3043552 baseEnd_3043552 := by
    simpa [prefixWord, tailWord_3043552, baseEnd_3043552] using wordTrace_append hprefix tailTrace_3043552
  have hstable : (prefixWord ++ tailWord_3043552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043552).length < 2 ^ (prefixWord ++ tailWord_3043552).sum := by decide
  have hdescent : baseEnd_3043552 < baseStart_3043552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043559 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3043559 : Nat := 118140960795 + 3043559 * 2 ^ 59
def prefixEnd_3043559 : Nat := 4983230072969 + 3 ^ 40 * 3043559 * 2
def baseEnd_3043559 : Nat := 520936222439187598371811

theorem tailTrace_3043559 : CollatzResearch.WordTrace tailWord_3043559 prefixEnd_3043559 520936222439187598371811 := by
  unfold tailWord_3043559
  simp only [CollatzResearch.WordTrace]
  refine ⟨111007716380713016339037731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74005144253808677559358487 111007716380713016339037731)
  ·
    refine ⟨166511574571069524508556597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111007716380713016339037731 166511574571069524508556597)
    ·
      refine ⟨15610460116037767922677181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166511574571069524508556597 15610460116037767922677181)
      ·
        refine ⟨5853922543514162971003943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15610460116037767922677181 5853922543514162971003943)
        ·
          refine ⟨8780883815271244456505915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853922543514162971003943 8780883815271244456505915)
          ·
            refine ⟨13171325722906866684758873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8780883815271244456505915 13171325722906866684758873)
            ·
              refine ⟨9878494292180150013569155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13171325722906866684758873 9878494292180150013569155)
              ·
                refine ⟨14817741438270225020353733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878494292180150013569155 14817741438270225020353733)
                ·
                  refine ⟨2778326519675667191316325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14817741438270225020353733 2778326519675667191316325)
                  ·
                    refine ⟨520936222439187598371811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2778326519675667191316325 520936222439187598371811)
                    ·
                      rfl

theorem cell23_3043559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3043559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043559 prefixEnd_3043559 := by exact prefixLift 3043559
  have htrace : WordTrace (prefixWord ++ tailWord_3043559) baseStart_3043559 baseEnd_3043559 := by
    simpa [prefixWord, tailWord_3043559, baseEnd_3043559] using wordTrace_append hprefix tailTrace_3043559
  have hstable : (prefixWord ++ tailWord_3043559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043559).length < 2 ^ (prefixWord ++ tailWord_3043559).sum := by decide
  have hdescent : baseEnd_3043559 < baseStart_3043559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043586 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3043586 : Nat := 118140960795 + 3043586 * 2 ^ 59
def prefixEnd_3043586 : Nat := 4983230072969 + 3 ^ 40 * 3043586 * 2
def baseEnd_3043586 : Nat := 1562822531295234189477809

theorem tailTrace_3043586 : CollatzResearch.WordTrace tailWord_3043586 prefixEnd_3043586 1562822531295234189477809 := by
  unfold tailWord_3043586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27752175287903799987567653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74005800767743466633513741 27752175287903799987567653)
  ·
    refine ⟨5203532866481962497668935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27752175287903799987567653 5203532866481962497668935)
    ·
      refine ⟨7805299299722943746503403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5203532866481962497668935 7805299299722943746503403)
      ·
        refine ⟨11707948949584415619755105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805299299722943746503403 11707948949584415619755105)
        ·
          refine ⟨8780961712188311714816329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11707948949584415619755105 8780961712188311714816329)
          ·
            refine ⟨6585721284141233786112247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8780961712188311714816329 6585721284141233786112247)
            ·
              refine ⟨9878581926211850679168371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585721284141233786112247 9878581926211850679168371)
              ·
                refine ⟨14817872889317776018752557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878581926211850679168371 14817872889317776018752557)
                ·
                  refine ⟨5556702333494166007032209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14817872889317776018752557 5556702333494166007032209)
                  ·
                    refine ⟨4167526750120624505274157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5556702333494166007032209 4167526750120624505274157)
                    ·
                      refine ⟨1562822531295234189477809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4167526750120624505274157 1562822531295234189477809)
                      ·
                        rfl

theorem cell23_3043586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3043586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043586 prefixEnd_3043586 := by exact prefixLift 3043586
  have htrace : WordTrace (prefixWord ++ tailWord_3043586) baseStart_3043586 baseEnd_3043586 := by
    simpa [prefixWord, tailWord_3043586, baseEnd_3043586] using wordTrace_append hprefix tailTrace_3043586
  have hstable : (prefixWord ++ tailWord_3043586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043586).length < 2 ^ (prefixWord ++ tailWord_3043586).sum := by decide
  have hdescent : baseEnd_3043586 < baseStart_3043586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043616 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3043616 : Nat := 118140960795 + 3043616 * 2 ^ 59
def prefixEnd_3043616 : Nat := 4983230072969 + 3 ^ 40 * 3043616 * 2
def baseEnd_3043616 : Nat := 1562837935714869072102671

theorem tailTrace_3043616 : CollatzResearch.WordTrace tailWord_3043616 prefixEnd_3043616 1562837935714869072102671 := by
  unfold tailWord_3043616
  simp only [CollatzResearch.WordTrace]
  refine ⟨55504897670753257536931351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74006530227671010049241801 55504897670753257536931351)
  ·
    refine ⟨83257346506129886305397027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55504897670753257536931351 83257346506129886305397027)
    ·
      refine ⟨124886019759194829458095541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83257346506129886305397027 124886019759194829458095541)
      ·
        refine ⟨11708064352424515261696457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124886019759194829458095541 11708064352424515261696457)
        ·
          refine ⟨8781048264318386446272343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11708064352424515261696457 8781048264318386446272343)
          ·
            refine ⟨13171572396477579669408515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8781048264318386446272343 13171572396477579669408515)
            ·
              refine ⟨19757358594716369504112773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13171572396477579669408515 19757358594716369504112773)
              ·
                refine ⟨3704504736509319282021145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19757358594716369504112773 3704504736509319282021145)
                ·
                  refine ⟨2778378552381989461515859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704504736509319282021145 2778378552381989461515859)
                  ·
                    refine ⟨4167567828572984192273789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2778378552381989461515859 4167567828572984192273789)
                    ·
                      refine ⟨1562837935714869072102671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4167567828572984192273789 1562837935714869072102671)
                      ·
                        rfl

theorem cell23_3043616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3043616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043616 prefixEnd_3043616 := by exact prefixLift 3043616
  have htrace : WordTrace (prefixWord ++ tailWord_3043616) baseStart_3043616 baseEnd_3043616 := by
    simpa [prefixWord, tailWord_3043616, baseEnd_3043616] using wordTrace_append hprefix tailTrace_3043616
  have hstable : (prefixWord ++ tailWord_3043616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043616).length < 2 ^ (prefixWord ++ tailWord_3043616).sum := by decide
  have hdescent : baseEnd_3043616 < baseStart_3043616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043623 : List Nat := [1, 1, 8, 1, 1, 2, 1, 8]
def baseStart_3043623 : Nat := 118140960795 + 3043623 * 2 ^ 59
def prefixEnd_3043623 : Nat := 4983230072969 + 3 ^ 40 * 3043623 * 2
def baseEnd_3043623 : Nat := 57883019632572242396857

theorem tailTrace_3043623 : CollatzResearch.WordTrace tailWord_3043623 prefixEnd_3043623 57883019632572242396857 := by
  unfold tailWord_3043623
  simp only [CollatzResearch.WordTrace]
  refine ⟨111010050652481155269367523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74006700434987436846245015 111010050652481155269367523)
  ·
    refine ⟨166515075978721732904051285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111010050652481155269367523 166515075978721732904051285)
    ·
      refine ⟨1951348546625645307469351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 166515075978721732904051285 1951348546625645307469351)
      ·
        refine ⟨2927022819938467961204027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951348546625645307469351 2927022819938467961204027)
        ·
          refine ⟨4390534229907701941806041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927022819938467961204027 4390534229907701941806041)
          ·
            refine ⟨3292900672430776456354531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4390534229907701941806041 3292900672430776456354531)
            ·
              refine ⟨4939351008646164684531797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292900672430776456354531 4939351008646164684531797)
              ·
                refine ⟨57883019632572242396857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4939351008646164684531797 57883019632572242396857)
                ·
                  rfl

theorem cell23_3043623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 8].length) (baseStart_3043623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043623 prefixEnd_3043623 := by exact prefixLift 3043623
  have htrace : WordTrace (prefixWord ++ tailWord_3043623) baseStart_3043623 baseEnd_3043623 := by
    simpa [prefixWord, tailWord_3043623, baseEnd_3043623] using wordTrace_append hprefix tailTrace_3043623
  have hstable : (prefixWord ++ tailWord_3043623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043623).length < 2 ^ (prefixWord ++ tailWord_3043623).sum := by decide
  have hdescent : baseEnd_3043623 < baseStart_3043623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043679 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 5]
def baseStart_3043679 : Nat := 118140960795 + 3043679 * 2 ^ 59
def prefixEnd_3043679 : Nat := 4983230072969 + 3 ^ 40 * 3043679 * 2
def baseEnd_3043679 : Nat := 173652253888455813957209

theorem tailTrace_3043679 : CollatzResearch.WordTrace tailWord_3043679 prefixEnd_3043679 173652253888455813957209 := by
  unfold tailWord_3043679
  simp only [CollatzResearch.WordTrace]
  refine ⟨111012093140278276833406091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74008062093518851222270727 111012093140278276833406091)
  ·
    refine ⟨166518139710417415250109137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111012093140278276833406091 166518139710417415250109137)
    ·
      refine ⟨124888604782813061437581853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166518139710417415250109137 124888604782813061437581853)
      ·
        refine ⟨46833226793554898039093195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124888604782813061437581853 46833226793554898039093195)
        ·
          refine ⟨70249840190332347058639793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46833226793554898039093195 70249840190332347058639793)
          ·
            refine ⟨52687380142749260293979845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70249840190332347058639793 52687380142749260293979845)
            ·
              refine ⟨9878883776765486305121221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52687380142749260293979845 9878883776765486305121221)
              ·
                refine ⟨1852290708143528682210229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9878883776765486305121221 1852290708143528682210229)
                ·
                  refine ⟨173652253888455813957209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852290708143528682210229 173652253888455813957209)
                  ·
                    rfl

theorem cell23_3043679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 5].length) (baseStart_3043679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043679 prefixEnd_3043679 := by exact prefixLift 3043679
  have htrace : WordTrace (prefixWord ++ tailWord_3043679) baseStart_3043679 baseEnd_3043679 := by
    simpa [prefixWord, tailWord_3043679, baseEnd_3043679] using wordTrace_append hprefix tailTrace_3043679
  have hstable : (prefixWord ++ tailWord_3043679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043679).length < 2 ^ (prefixWord ++ tailWord_3043679).sum := by decide
  have hdescent : baseEnd_3043679 < baseStart_3043679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043713 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 5]
def baseStart_3043713 : Nat := 118140960795 + 3043713 * 2 ^ 59
def prefixEnd_3043713 : Nat := 4983230072969 + 3 ^ 40 * 3043713 * 2
def baseEnd_3043713 : Nat := 173654193704261688065525

theorem tailTrace_3043713 : CollatzResearch.WordTrace tailWord_3043713 prefixEnd_3043713 173654193704261688065525 := by
  unfold tailWord_3043713
  simp only [CollatzResearch.WordTrace]
  refine ⟨111013333222155100640143793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74008888814770067093429195 111013333222155100640143793)
  ·
    refine ⟨83259999916616325480107845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111013333222155100640143793 83259999916616325480107845)
    ·
      refine ⟨15611249984365561027520221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83259999916616325480107845 15611249984365561027520221)
      ·
        refine ⟨5854218744137085385320083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15611249984365561027520221 5854218744137085385320083)
        ·
          refine ⟨8781328116205628077980125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854218744137085385320083 8781328116205628077980125)
          ·
            refine ⟨3292998043577110529242547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8781328116205628077980125 3292998043577110529242547)
            ·
              refine ⟨4939497065365665793863821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292998043577110529242547 4939497065365665793863821)
              ·
                refine ⟨1852311399512124672698933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4939497065365665793863821 1852311399512124672698933)
                ·
                  refine ⟨173654193704261688065525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852311399512124672698933 173654193704261688065525)
                  ·
                    rfl

theorem cell23_3043713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 5].length) (baseStart_3043713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043713 prefixEnd_3043713 := by exact prefixLift 3043713
  have htrace : WordTrace (prefixWord ++ tailWord_3043713) baseStart_3043713 baseEnd_3043713 := by
    simpa [prefixWord, tailWord_3043713, baseEnd_3043713] using wordTrace_append hprefix tailTrace_3043713
  have hstable : (prefixWord ++ tailWord_3043713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043713).length < 2 ^ (prefixWord ++ tailWord_3043713).sum := by decide
  have hdescent : baseEnd_3043713 < baseStart_3043713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043726 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3043726 : Nat := 118140960795 + 3043726 * 2 ^ 59
def prefixEnd_3043726 : Nat := 4983230072969 + 3 ^ 40 * 3043726 * 2
def baseEnd_3043726 : Nat := 520964806195621213909055

theorem tailTrace_3043726 : CollatzResearch.WordTrace tailWord_3043726 prefixEnd_3043726 520964806195621213909055 := by
  unfold tailWord_3043726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876725921388500482545879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74009204914072002573578021 13876725921388500482545879)
  ·
    refine ⟨20815088882082750723818819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876725921388500482545879 20815088882082750723818819)
    ·
      refine ⟨31222633323124126085728229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20815088882082750723818819 31222633323124126085728229)
      ·
        refine ⟨5854243748085773641074043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31222633323124126085728229 5854243748085773641074043)
        ·
          refine ⟨8781365622128660461611065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854243748085773641074043 8781365622128660461611065)
          ·
            refine ⟨6586024216596495346208299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8781365622128660461611065 6586024216596495346208299)
            ·
              refine ⟨9879036324894743019312449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586024216596495346208299 9879036324894743019312449)
              ·
                refine ⟨7409277243671057264484337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9879036324894743019312449 7409277243671057264484337)
                ·
                  refine ⟨5556957932753292948363253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7409277243671057264484337 5556957932753292948363253)
                  ·
                    refine ⟨520964806195621213909055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5556957932753292948363253 520964806195621213909055)
                    ·
                      rfl

theorem cell23_3043726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3043726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043726 prefixEnd_3043726 := by exact prefixLift 3043726
  have htrace : WordTrace (prefixWord ++ tailWord_3043726) baseStart_3043726 baseEnd_3043726 := by
    simpa [prefixWord, tailWord_3043726, baseEnd_3043726] using wordTrace_append hprefix tailTrace_3043726
  have hstable : (prefixWord ++ tailWord_3043726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043726).length < 2 ^ (prefixWord ++ tailWord_3043726).sum := by decide
  have hdescent : baseEnd_3043726 < baseStart_3043726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043746 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_3043746 : Nat := 118140960795 + 3043746 * 2 ^ 59
def prefixEnd_3043746 : Nat := 4983230072969 + 3 ^ 40 * 3043746 * 2
def baseEnd_3043746 : Nat := 1562904688199953563477073

theorem tailTrace_3043746 : CollatzResearch.WordTrace tailWord_3043746 prefixEnd_3043746 1562904688199953563477073 := by
  unfold tailWord_3043746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27753634207758886819023773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74009691220690364850730061 27753634207758886819023773)
  ·
    refine ⟨10407612827909582557133915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27753634207758886819023773 10407612827909582557133915)
    ·
      refine ⟨15611419241864373835700873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10407612827909582557133915 15611419241864373835700873)
      ·
        refine ⟨11708564431398280376775655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15611419241864373835700873 11708564431398280376775655)
        ·
          refine ⟨17562846647097420565163483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708564431398280376775655 17562846647097420565163483)
          ·
            refine ⟨26344269970646130847745225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17562846647097420565163483 26344269970646130847745225)
            ·
              refine ⟨19758202477984598135808919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26344269970646130847745225 19758202477984598135808919)
              ·
                refine ⟨29637303716976897203713379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19758202477984598135808919 29637303716976897203713379)
                ·
                  refine ⟨44455955575465345805570069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29637303716976897203713379 44455955575465345805570069)
                  ·
                    refine ⟨2083872917599938084636097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44455955575465345805570069 2083872917599938084636097)
                    ·
                      refine ⟨1562904688199953563477073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2083872917599938084636097 1562904688199953563477073)
                      ·
                        rfl

theorem cell23_3043746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_3043746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043746 prefixEnd_3043746 := by exact prefixLift 3043746
  have htrace : WordTrace (prefixWord ++ tailWord_3043746) baseStart_3043746 baseEnd_3043746 := by
    simpa [prefixWord, tailWord_3043746, baseEnd_3043746] using wordTrace_append hprefix tailTrace_3043746
  have hstable : (prefixWord ++ tailWord_3043746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043746).length < 2 ^ (prefixWord ++ tailWord_3043746).sum := by decide
  have hdescent : baseEnd_3043746 < baseStart_3043746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043749 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_3043749 : Nat := 118140960795 + 3043749 * 2 ^ 59
def prefixEnd_3043749 : Nat := 4983230072969 + 3 ^ 40 * 3043749 * 2
def baseEnd_3043749 : Nat := 1562906228641917051739559

theorem tailTrace_3043749 : CollatzResearch.WordTrace tailWord_3043749 prefixEnd_3043749 1562906228641917051739559 := by
  unfold tailWord_3043749
  simp only [CollatzResearch.WordTrace]
  refine ⟨111014646250024678788454301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74009764166683119192302867 111014646250024678788454301)
  ·
    refine ⟨41630492343759254545670363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111014646250024678788454301 41630492343759254545670363)
    ·
      refine ⟨62445738515638881818505545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41630492343759254545670363 62445738515638881818505545)
      ·
        refine ⟨46834303886729161363879159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62445738515638881818505545 46834303886729161363879159)
        ·
          refine ⟨70251455830093742045818739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46834303886729161363879159 70251455830093742045818739)
          ·
            refine ⟨105377183745140613068728109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70251455830093742045818739 105377183745140613068728109)
            ·
              refine ⟨39516443904427729900773041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105377183745140613068728109 39516443904427729900773041)
              ·
                refine ⟨29637332928320797425579781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39516443904427729900773041 29637332928320797425579781)
                ·
                  refine ⟨5556999924060149517296209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29637332928320797425579781 5556999924060149517296209)
                  ·
                    refine ⟨4167749943045112137972157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5556999924060149517296209 4167749943045112137972157)
                    ·
                      refine ⟨1562906228641917051739559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4167749943045112137972157 1562906228641917051739559)
                      ·
                        rfl

theorem cell23_3043749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_3043749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043749 prefixEnd_3043749 := by exact prefixLift 3043749
  have htrace : WordTrace (prefixWord ++ tailWord_3043749) baseStart_3043749 baseEnd_3043749 := by
    simpa [prefixWord, tailWord_3043749, baseEnd_3043749] using wordTrace_append hprefix tailTrace_3043749
  have hstable : (prefixWord ++ tailWord_3043749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043749).length < 2 ^ (prefixWord ++ tailWord_3043749).sum := by decide
  have hdescent : baseEnd_3043749 < baseStart_3043749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043792 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_3043792 : Nat := 118140960795 + 3043792 * 2 ^ 59
def prefixEnd_3043792 : Nat := 4983230072969 + 3 ^ 40 * 3043792 * 2
def baseEnd_3043792 : Nat := 1562928308310060383501861

theorem tailTrace_3043792 : CollatzResearch.WordTrace tailWord_3043792 prefixEnd_3043792 1562928308310060383501861 := by
  unfold tailWord_3043792
  simp only [CollatzResearch.WordTrace]
  refine ⟨55508107294434448566134815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74010809725912598088179753 55508107294434448566134815)
  ·
    refine ⟨83262160941651672849202223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55508107294434448566134815 83262160941651672849202223)
    ·
      refine ⟨124893241412477509273803335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83262160941651672849202223 124893241412477509273803335)
      ·
        refine ⟨187339862118716263910705003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124893241412477509273803335 187339862118716263910705003)
        ·
          refine ⟨281009793178074395866057505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187339862118716263910705003 281009793178074395866057505)
          ·
            refine ⟨210757344883555796899543129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281009793178074395866057505 210757344883555796899543129)
            ·
              refine ⟨158068008662666847674657347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210757344883555796899543129 158068008662666847674657347)
              ·
                refine ⟨237102012994000271511986021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158068008662666847674657347 237102012994000271511986021)
                ·
                  refine ⟨44456627436375050908497379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237102012994000271511986021 44456627436375050908497379)
                  ·
                    refine ⟨66684941154562576362746069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44456627436375050908497379 66684941154562576362746069)
                    ·
                      refine ⟨1562928308310060383501861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66684941154562576362746069 1562928308310060383501861)
                      ·
                        rfl

theorem cell23_3043792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_3043792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043792 prefixEnd_3043792 := by exact prefixLift 3043792
  have htrace : WordTrace (prefixWord ++ tailWord_3043792) baseStart_3043792 baseEnd_3043792 := by
    simpa [prefixWord, tailWord_3043792, baseEnd_3043792] using wordTrace_append hprefix tailTrace_3043792
  have hstable : (prefixWord ++ tailWord_3043792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043792).length < 2 ^ (prefixWord ++ tailWord_3043792).sum := by decide
  have hdescent : baseEnd_3043792 < baseStart_3043792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043819 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4]
def baseStart_3043819 : Nat := 118140960795 + 3043819 * 2 ^ 59
def prefixEnd_3043819 : Nat := 4983230072969 + 3 ^ 40 * 3043819 * 2
def baseEnd_3043819 : Nat := 1562942172287731777864237

theorem tailTrace_3043819 : CollatzResearch.WordTrace tailWord_3043819 prefixEnd_3043819 1562942172287731777864237 := by
  unfold tailWord_3043819
  simp only [CollatzResearch.WordTrace]
  refine ⟨111017199359771080743502511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74011466239847387162335007 111017199359771080743502511)
  ·
    refine ⟨166525799039656621115253767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111017199359771080743502511 166525799039656621115253767)
    ·
      refine ⟨249788698559484931672880651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166525799039656621115253767 249788698559484931672880651)
      ·
        refine ⟨374683047839227397509320977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249788698559484931672880651 374683047839227397509320977)
        ·
          refine ⟨281012285879420548131990733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374683047839227397509320977 281012285879420548131990733)
          ·
            refine ⟨105379607204782705549496525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281012285879420548131990733 105379607204782705549496525)
            ·
              refine ⟨39517352701793514581061197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105379607204782705549496525 39517352701793514581061197)
              ·
                refine ⟨14819007263172567967897949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39517352701793514581061197 14819007263172567967897949)
                ·
                  refine ⟨5557127723689712987961731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14819007263172567967897949 5557127723689712987961731)
                  ·
                    refine ⟨8335691585534569481942597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5557127723689712987961731 8335691585534569481942597)
                    ·
                      refine ⟨1562942172287731777864237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8335691585534569481942597 1562942172287731777864237)
                      ·
                        rfl

theorem cell23_3043819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 4].length) (baseStart_3043819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043819 prefixEnd_3043819 := by exact prefixLift 3043819
  have htrace : WordTrace (prefixWord ++ tailWord_3043819) baseStart_3043819 baseEnd_3043819 := by
    simpa [prefixWord, tailWord_3043819, baseEnd_3043819] using wordTrace_append hprefix tailTrace_3043819
  have hstable : (prefixWord ++ tailWord_3043819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043819).length < 2 ^ (prefixWord ++ tailWord_3043819).sum := by decide
  have hdescent : baseEnd_3043819 < baseStart_3043819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043839 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_3043839 : Nat := 118140960795 + 3043839 * 2 ^ 59
def prefixEnd_3043839 : Nat := 4983230072969 + 3 ^ 40 * 3043839 * 2
def baseEnd_3043839 : Nat := 1562952441900821699614145

theorem tailTrace_3043839 : CollatzResearch.WordTrace tailWord_3043839 prefixEnd_3043839 1562952441900821699614145 := by
  unfold tailWord_3043839
  simp only [CollatzResearch.WordTrace]
  refine ⟨111017928819698624159230571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74011952546465749439487047 111017928819698624159230571)
  ·
    refine ⟨166526893229547936238845857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111017928819698624159230571 166526893229547936238845857)
    ·
      refine ⟨124895169922160952179134393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166526893229547936238845857 124895169922160952179134393)
      ·
        refine ⟨93671377441620714134350795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124895169922160952179134393 93671377441620714134350795)
        ·
          refine ⟨140507066162431071201526193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93671377441620714134350795 140507066162431071201526193)
          ·
            refine ⟨105380299621823303401144645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140507066162431071201526193 105380299621823303401144645)
            ·
              refine ⟨19758806179091869387714621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105380299621823303401144645 19758806179091869387714621)
              ·
                refine ⟨7409552317159451020392983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19758806179091869387714621 7409552317159451020392983)
                ·
                  refine ⟨11114328475739176530589475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7409552317159451020392983 11114328475739176530589475)
                  ·
                    refine ⟨16671492713608764795884213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11114328475739176530589475 16671492713608764795884213)
                    ·
                      refine ⟨1562952441900821699614145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16671492713608764795884213 1562952441900821699614145)
                      ·
                        rfl

theorem cell23_3043839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_3043839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043839 prefixEnd_3043839 := by exact prefixLift 3043839
  have htrace : WordTrace (prefixWord ++ tailWord_3043839) baseStart_3043839 baseEnd_3043839 := by
    simpa [prefixWord, tailWord_3043839, baseEnd_3043839] using wordTrace_append hprefix tailTrace_3043839
  have hstable : (prefixWord ++ tailWord_3043839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043839).length < 2 ^ (prefixWord ++ tailWord_3043839).sum := by decide
  have hdescent : baseEnd_3043839 < baseStart_3043839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043866 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3043866 : Nat := 118140960795 + 3043866 * 2 ^ 59
def prefixEnd_3043866 : Nat := 4983230072969 + 3 ^ 40 * 3043866 * 2
def baseEnd_3043866 : Nat := 1562966305878493093976521

theorem tailTrace_3043866 : CollatzResearch.WordTrace tailWord_3043866 prefixEnd_3043866 1562966305878493093976521 := by
  unfold tailWord_3043866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27754728397650201942615863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74012609060400538513642301 27754728397650201942615863)
  ·
    refine ⟨41632092596475302913923795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27754728397650201942615863 41632092596475302913923795)
    ·
      refine ⟨62448138894712954370885693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41632092596475302913923795 62448138894712954370885693)
      ·
        refine ⟨23418052085517357889082135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62448138894712954370885693 23418052085517357889082135)
        ·
          refine ⟨35127078128276036833623203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23418052085517357889082135 35127078128276036833623203)
          ·
            refine ⟨52690617192414055250434805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35127078128276036833623203 52690617192414055250434805)
            ·
              refine ⟨4939745361788817679728263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52690617192414055250434805 4939745361788817679728263)
              ·
                refine ⟨7409618042683226519592395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939745361788817679728263 7409618042683226519592395)
                ·
                  refine ⟨11114427064024839779388593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7409618042683226519592395 11114427064024839779388593)
                  ·
                    refine ⟨8335820298018629834541445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11114427064024839779388593 8335820298018629834541445)
                    ·
                      refine ⟨1562966305878493093976521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8335820298018629834541445 1562966305878493093976521)
                      ·
                        rfl

theorem cell23_3043866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3043866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043866 prefixEnd_3043866 := by exact prefixLift 3043866
  have htrace : WordTrace (prefixWord ++ tailWord_3043866) baseStart_3043866 baseEnd_3043866 := by
    simpa [prefixWord, tailWord_3043866, baseEnd_3043866] using wordTrace_append hprefix tailTrace_3043866
  have hstable : (prefixWord ++ tailWord_3043866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043866).length < 2 ^ (prefixWord ++ tailWord_3043866).sum := by decide
  have hdescent : baseEnd_3043866 < baseStart_3043866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043873 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3043873 : Nat := 118140960795 + 3043873 * 2 ^ 59
def prefixEnd_3043873 : Nat := 4983230072969 + 3 ^ 40 * 3043873 * 2
def baseEnd_3043873 : Nat := 1562969900243074566588989

theorem tailTrace_3043873 : CollatzResearch.WordTrace tailWord_3043873 prefixEnd_3043873 1562969900243074566588989 := by
  unfold tailWord_3043873
  simp only [CollatzResearch.WordTrace]
  refine ⟨111019168901575447965968273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74012779267716965310645515 111019168901575447965968273)
  ·
    refine ⟨83264376676181585974476205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111019168901575447965968273 83264376676181585974476205)
    ·
      refine ⟨31224141253568094740428577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83264376676181585974476205 31224141253568094740428577)
      ·
        refine ⟨23418105940176071055321433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31224141253568094740428577 23418105940176071055321433)
        ·
          refine ⟨17563579455132053291491075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23418105940176071055321433 17563579455132053291491075)
          ·
            refine ⟨26345369182698079937236613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17563579455132053291491075 26345369182698079937236613)
            ·
              refine ⟨4939756721755889988231865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26345369182698079937236613 4939756721755889988231865)
              ·
                refine ⟨3704817541316917491173899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4939756721755889988231865 3704817541316917491173899)
                ·
                  refine ⟨5557226311975376236760849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3704817541316917491173899 5557226311975376236760849)
                  ·
                    refine ⟨4167919733981532177570637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557226311975376236760849 4167919733981532177570637)
                    ·
                      refine ⟨1562969900243074566588989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4167919733981532177570637 1562969900243074566588989)
                      ·
                        rfl

theorem cell23_3043873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3043873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043873 prefixEnd_3043873 := by exact prefixLift 3043873
  have htrace : WordTrace (prefixWord ++ tailWord_3043873) baseStart_3043873 baseEnd_3043873 := by
    simpa [prefixWord, tailWord_3043873, baseEnd_3043873] using wordTrace_append hprefix tailTrace_3043873
  have hstable : (prefixWord ++ tailWord_3043873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043873).length < 2 ^ (prefixWord ++ tailWord_3043873).sum := by decide
  have hdescent : baseEnd_3043873 < baseStart_3043873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043903 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 3]
def baseStart_3043903 : Nat := 118140960795 + 3043903 * 2 ^ 59
def prefixEnd_3043903 : Nat := 4983230072969 + 3 ^ 40 * 3043903 * 2
def baseEnd_3043903 : Nat := 1562985304662709449213851

theorem tailTrace_3043903 : CollatzResearch.WordTrace tailWord_3043903 prefixEnd_3043903 1562985304662709449213851 := by
  unfold tailWord_3043903
  simp only [CollatzResearch.WordTrace]
  refine ⟨111020263091466763089560363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74013508727644508726373575 111020263091466763089560363)
  ·
    refine ⟨166530394637200144634340545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111020263091466763089560363 166530394637200144634340545)
    ·
      refine ⟨124897795977900108475755409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166530394637200144634340545 124897795977900108475755409)
      ·
        refine ⟨93673346983425081356816557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124897795977900108475755409 93673346983425081356816557)
        ·
          refine ⟨35127505118784405508806209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93673346983425081356816557 35127505118784405508806209)
          ·
            refine ⟨26345628839088304131604657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35127505118784405508806209 26345628839088304131604657)
            ·
              refine ⟨19759221629316228098703493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26345628839088304131604657 19759221629316228098703493)
              ·
                refine ⟨3704854055496792768506905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19759221629316228098703493 3704854055496792768506905)
                ·
                  refine ⟨2778640541622594576380179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704854055496792768506905 2778640541622594576380179)
                  ·
                    refine ⟨4167960812433891864570269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2778640541622594576380179 4167960812433891864570269)
                    ·
                      refine ⟨1562985304662709449213851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4167960812433891864570269 1562985304662709449213851)
                      ·
                        rfl

theorem cell23_3043903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_3043903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043903 prefixEnd_3043903 := by exact prefixLift 3043903
  have htrace : WordTrace (prefixWord ++ tailWord_3043903) baseStart_3043903 baseEnd_3043903 := by
    simpa [prefixWord, tailWord_3043903, baseEnd_3043903] using wordTrace_append hprefix tailTrace_3043903
  have hstable : (prefixWord ++ tailWord_3043903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043903).length < 2 ^ (prefixWord ++ tailWord_3043903).sum := by decide
  have hdescent : baseEnd_3043903 < baseStart_3043903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043919 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 2, 6]
def baseStart_3043919 : Nat := 118140960795 + 3043919 * 2 ^ 59
def prefixEnd_3043919 : Nat := 4983230072969 + 3 ^ 40 * 3043919 * 2
def baseEnd_3043919 : Nat := 520997840117727128871259

theorem tailTrace_3043919 : CollatzResearch.WordTrace tailWord_3043919 prefixEnd_3043919 520997840117727128871259 := by
  unfold tailWord_3043919
  simp only [CollatzResearch.WordTrace]
  refine ⟨111020846659408797822142811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74013897772939198548095207 111020846659408797822142811)
  ·
    refine ⟨166531269989113196733214217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111020846659408797822142811 166531269989113196733214217)
    ·
      refine ⟨124898452491834897549910663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166531269989113196733214217 124898452491834897549910663)
      ·
        refine ⟨187347678737752346324865995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124898452491834897549910663 187347678737752346324865995)
        ·
          refine ⟨281021518106628519487298993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187347678737752346324865995 281021518106628519487298993)
          ·
            refine ⟨210766138579971389615474245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281021518106628519487298993 210766138579971389615474245)
            ·
              refine ⟨39518650983744635552901421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210766138579971389615474245 39518650983744635552901421)
              ·
                refine ⟨14819494118904238332338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39518650983744635552901421 14819494118904238332338033)
                ·
                  refine ⟨11114620589178178749253525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14819494118904238332338033 11114620589178178749253525)
                  ·
                    refine ⟨520997840117727128871259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11114620589178178749253525 520997840117727128871259)
                    ·
                      rfl

theorem cell23_3043919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_3043919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043919 prefixEnd_3043919 := by exact prefixLift 3043919
  have htrace : WordTrace (prefixWord ++ tailWord_3043919) baseStart_3043919 baseEnd_3043919 := by
    simpa [prefixWord, tailWord_3043919, baseEnd_3043919] using wordTrace_append hprefix tailTrace_3043919
  have hstable : (prefixWord ++ tailWord_3043919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043919).length < 2 ^ (prefixWord ++ tailWord_3043919).sum := by decide
  have hdescent : baseEnd_3043919 < baseStart_3043919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043946 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3043946 : Nat := 118140960795 + 3043946 * 2 ^ 59
def prefixEnd_3043946 : Nat := 4983230072969 + 3 ^ 40 * 3043946 * 2
def baseEnd_3043946 : Nat := 1563007384330852780976153

theorem tailTrace_3043946 : CollatzResearch.WordTrace tailWord_3043946 prefixEnd_3043946 1563007384330852780976153 := by
  unfold tailWord_3043946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27755457857577745358343923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74014554286873987622250461 27755457857577745358343923)
  ·
    refine ⟨41633186786366618037515885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27755457857577745358343923 41633186786366618037515885)
    ·
      refine ⟨15612445044887481764068457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41633186786366618037515885 15612445044887481764068457)
      ·
        refine ⟨11709333783665611323051343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15612445044887481764068457 11709333783665611323051343)
        ·
          refine ⟨17564000675498416984577015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11709333783665611323051343 17564000675498416984577015)
          ·
            refine ⟨26346001013247625476865523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17564000675498416984577015 26346001013247625476865523)
            ·
              refine ⟨39519001519871438215298285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26346001013247625476865523 39519001519871438215298285)
              ·
                refine ⟨14819625569951789330736857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39519001519871438215298285 14819625569951789330736857)
                ·
                  refine ⟨11114719177463841998052643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14819625569951789330736857 11114719177463841998052643)
                  ·
                    refine ⟨16672078766195762997078965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11114719177463841998052643 16672078766195762997078965)
                    ·
                      refine ⟨1563007384330852780976153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16672078766195762997078965 1563007384330852780976153)
                      ·
                        rfl

theorem cell23_3043946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3043946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043946 prefixEnd_3043946 := by exact prefixLift 3043946
  have htrace : WordTrace (prefixWord ++ tailWord_3043946) baseStart_3043946 baseEnd_3043946 := by
    simpa [prefixWord, tailWord_3043946, baseEnd_3043946] using wordTrace_append hprefix tailTrace_3043946
  have hstable : (prefixWord ++ tailWord_3043946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043946).length < 2 ^ (prefixWord ++ tailWord_3043946).sum := by decide
  have hdescent : baseEnd_3043946 < baseStart_3043946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043959 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3043959 : Nat := 118140960795 + 3043959 * 2 ^ 59
def prefixEnd_3043959 : Nat := 4983230072969 + 3 ^ 40 * 3043959 * 2
def baseEnd_3043959 : Nat := 1563014059579361230113593

theorem tailTrace_3043959 : CollatzResearch.WordTrace tailWord_3043959 prefixEnd_3043959 1563014059579361230113593 := by
  unfold tailWord_3043959
  simp only [CollatzResearch.WordTrace]
  refine ⟨111022305579263884653598931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74014870386175923102399287 111022305579263884653598931)
  ·
    refine ⟨166533458368895826980398397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111022305579263884653598931 166533458368895826980398397)
    ·
      refine ⟨62450046888335935117649399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166533458368895826980398397 62450046888335935117649399)
      ·
        refine ⟨93675070332503902676474099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62450046888335935117649399 93675070332503902676474099)
        ·
          refine ⟨140512605498755854014711149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93675070332503902676474099 140512605498755854014711149)
          ·
            refine ⟨52692227062033445255516681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140512605498755854014711149 52692227062033445255516681)
            ·
              refine ⟨39519170296525083941637511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52692227062033445255516681 39519170296525083941637511)
              ·
                refine ⟨59278755444787625912456267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39519170296525083941637511 59278755444787625912456267)
                ·
                  refine ⟨88918133167181438868684401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59278755444787625912456267 88918133167181438868684401)
                  ·
                    refine ⟨66688599875386079151513301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88918133167181438868684401 66688599875386079151513301)
                    ·
                      refine ⟨1563014059579361230113593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66688599875386079151513301 1563014059579361230113593)
                      ·
                        rfl

theorem cell23_3043959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3043959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3043959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3043959 prefixEnd_3043959 := by exact prefixLift 3043959
  have htrace : WordTrace (prefixWord ++ tailWord_3043959) baseStart_3043959 baseEnd_3043959 := by
    simpa [prefixWord, tailWord_3043959, baseEnd_3043959] using wordTrace_append hprefix tailTrace_3043959
  have hstable : (prefixWord ++ tailWord_3043959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043959).length < 2 ^ (prefixWord ++ tailWord_3043959).sum := by decide
  have hdescent : baseEnd_3043959 < baseStart_3043959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044000 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 5]
def baseStart_3044000 : Nat := 118140960795 + 3044000 * 2 ^ 59
def prefixEnd_3044000 : Nat := 4983230072969 + 3 ^ 40 * 3044000 * 2
def baseEnd_3044000 : Nat := 173670568031799507744545

theorem tailTrace_3044000 : CollatzResearch.WordTrace tailWord_3044000 prefixEnd_3044000 173670568031799507744545 := by
  unfold tailWord_3044000
  simp only [CollatzResearch.WordTrace]
  refine ⟨55511900486057674327920727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74015867314743565770560969 55511900486057674327920727)
  ·
    refine ⟨83267850729086511491881091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55511900486057674327920727 83267850729086511491881091)
    ·
      refine ⟨124901776093629767237821637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83267850729086511491881091 124901776093629767237821637)
      ·
        refine ⟨23419083017555581357091557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124901776093629767237821637 23419083017555581357091557)
        ·
          refine ⟨4391078065791671504454667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23419083017555581357091557 4391078065791671504454667)
          ·
            refine ⟨6586617098687507256682001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391078065791671504454667 6586617098687507256682001)
            ·
              refine ⟨4939962824015630442511501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6586617098687507256682001 4939962824015630442511501)
              ·
                refine ⟨1852486059005861415941813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4939962824015630442511501 1852486059005861415941813)
                ·
                  refine ⟨173670568031799507744545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852486059005861415941813 173670568031799507744545)
                  ·
                    rfl

theorem cell23_3044000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 5].length) (baseStart_3044000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044000 prefixEnd_3044000 := by exact prefixLift 3044000
  have htrace : WordTrace (prefixWord ++ tailWord_3044000) baseStart_3044000 baseEnd_3044000 := by
    simpa [prefixWord, tailWord_3044000, baseEnd_3044000] using wordTrace_append hprefix tailTrace_3044000
  have hstable : (prefixWord ++ tailWord_3044000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044000).length < 2 ^ (prefixWord ++ tailWord_3044000).sum := by decide
  have hdescent : baseEnd_3044000 < baseStart_3044000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044016 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_3044016 : Nat := 118140960795 + 3044016 * 2 ^ 59
def prefixEnd_3044016 : Nat := 4983230072969 + 3 ^ 40 * 3044016 * 2
def baseEnd_3044016 : Nat := 1563043327976667507100831

theorem tailTrace_3044016 : CollatzResearch.WordTrace tailWord_3044016 prefixEnd_3044016 1563043327976667507100831 := by
  unfold tailWord_3044016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55512192270028691694211951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74016256360038255592282601 55512192270028691694211951)
  ·
    refine ⟨83268288405043037541317927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55512192270028691694211951 83268288405043037541317927)
    ·
      refine ⟨124902432607564556311976891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83268288405043037541317927 124902432607564556311976891)
      ·
        refine ⟨187353648911346834467965337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124902432607564556311976891 187353648911346834467965337)
        ·
          refine ⟨140515236683510125850974003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187353648911346834467965337 140515236683510125850974003)
          ·
            refine ⟨210772855025265188776461005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140515236683510125850974003 210772855025265188776461005)
            ·
              refine ⟨79039820634474445791172877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210772855025265188776461005 79039820634474445791172877)
              ·
                refine ⟨29639932737927917171689829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79039820634474445791172877 29639932737927917171689829)
                ·
                  refine ⟨5557487388361484469691843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29639932737927917171689829 5557487388361484469691843)
                  ·
                    refine ⟨8336231082542226704537765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5557487388361484469691843 8336231082542226704537765)
                    ·
                      refine ⟨1563043327976667507100831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8336231082542226704537765 1563043327976667507100831)
                      ·
                        rfl

theorem cell23_3044016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_3044016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044016 prefixEnd_3044016 := by exact prefixLift 3044016
  have htrace : WordTrace (prefixWord ++ tailWord_3044016) baseStart_3044016 baseEnd_3044016 := by
    simpa [prefixWord, tailWord_3044016, baseEnd_3044016] using wordTrace_append hprefix tailTrace_3044016
  have hstable : (prefixWord ++ tailWord_3044016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044016).length < 2 ^ (prefixWord ++ tailWord_3044016).sum := by decide
  have hdescent : baseEnd_3044016 < baseStart_3044016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044056 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 8]
def baseStart_3044056 : Nat := 118140960795 + 3044056 * 2 ^ 59
def prefixEnd_3044056 : Nat := 4983230072969 + 3 ^ 40 * 3044056 * 2
def baseEnd_3044056 : Nat := 173673763022538594511183

theorem tailTrace_3044056 : CollatzResearch.WordTrace tailWord_3044056 prefixEnd_3044056 173673763022538594511183 := by
  unfold tailWord_3044056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55512921729956235109940011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74017228973274980146586681 55512921729956235109940011)
  ·
    refine ⟨83269382594934352664910017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55512921729956235109940011 83269382594934352664910017)
    ·
      refine ⟨62452036946200764498682513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83269382594934352664910017 62452036946200764498682513)
      ·
        refine ⟨46839027709650573374011885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62452036946200764498682513 46839027709650573374011885)
        ·
          refine ⟨17564635391118965015254457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46839027709650573374011885 17564635391118965015254457)
          ·
            refine ⟨13173476543339223761440843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17564635391118965015254457 13173476543339223761440843)
            ·
              refine ⟨19760214815008835642161265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13173476543339223761440843 19760214815008835642161265)
              ·
                refine ⟨14820161111256626731620949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19760214815008835642161265 14820161111256626731620949)
                ·
                  refine ⟨173673763022538594511183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14820161111256626731620949 173673763022538594511183)
                  ·
                    rfl

theorem cell23_3044056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_3044056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044056 prefixEnd_3044056 := by exact prefixLift 3044056
  have htrace : WordTrace (prefixWord ++ tailWord_3044056) baseStart_3044056 baseEnd_3044056 := by
    simpa [prefixWord, tailWord_3044056, baseEnd_3044056] using wordTrace_append hprefix tailTrace_3044056
  have hstable : (prefixWord ++ tailWord_3044056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044056).length < 2 ^ (prefixWord ++ tailWord_3044056).sum := by decide
  have hdescent : baseEnd_3044056 < baseStart_3044056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044100 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3044100 : Nat := 118140960795 + 3044100 * 2 ^ 59
def prefixEnd_3044100 : Nat := 4983230072969 + 3 ^ 40 * 3044100 * 2
def baseEnd_3044100 : Nat := 1563086460351645178450445

theorem tailTrace_3044100 : CollatzResearch.WordTrace tailWord_3044100 prefixEnd_3044100 1563086460351645178450445 := by
  unfold tailWord_3044100
  simp only [CollatzResearch.WordTrace]
  refine ⟨55513724135876532867240877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74018298847835377156321169 55513724135876532867240877)
  ·
    refine ⟨20817646550953699825215329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55513724135876532867240877 20817646550953699825215329)
    ·
      refine ⟨15613234913215274868911497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20817646550953699825215329 15613234913215274868911497)
      ·
        refine ⟨11709926184911456151683623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15613234913215274868911497 11709926184911456151683623)
        ·
          refine ⟨17564889277367184227525435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11709926184911456151683623 17564889277367184227525435)
          ·
            refine ⟨26347333916050776341288153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17564889277367184227525435 26347333916050776341288153)
            ·
              refine ⟨19760500437038082255966115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26347333916050776341288153 19760500437038082255966115)
              ·
                refine ⟨29640750655557123383949173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19760500437038082255966115 29640750655557123383949173)
                ·
                  refine ⟨2778820373958480317245235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29640750655557123383949173 2778820373958480317245235)
                  ·
                    refine ⟨4168230560937720475867853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2778820373958480317245235 4168230560937720475867853)
                    ·
                      refine ⟨1563086460351645178450445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168230560937720475867853 1563086460351645178450445)
                      ·
                        rfl

theorem cell23_3044100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3044100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044100 prefixEnd_3044100 := by exact prefixLift 3044100
  have htrace : WordTrace (prefixWord ++ tailWord_3044100) baseStart_3044100 baseEnd_3044100 := by
    simpa [prefixWord, tailWord_3044100, baseEnd_3044100] using wordTrace_append hprefix tailTrace_3044100
  have hstable : (prefixWord ++ tailWord_3044100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044100).length < 2 ^ (prefixWord ++ tailWord_3044100).sum := by decide
  have hdescent : baseEnd_3044100 < baseStart_3044100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044117 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_3044117 : Nat := 118140960795 + 3044117 * 2 ^ 59
def prefixEnd_3044117 : Nat := 4983230072969 + 3 ^ 40 * 3044117 * 2
def baseEnd_3044117 : Nat := 1563095189522771611937867

theorem tailTrace_3044117 : CollatzResearch.WordTrace tailWord_3044117 prefixEnd_3044117 1563095189522771611937867 := by
  unfold tailWord_3044117
  simp only [CollatzResearch.WordTrace]
  refine ⟨111028068312691477637850605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74018712208460985091900403 111028068312691477637850605)
  ·
    refine ⟨41635525617259304114193977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111028068312691477637850605 41635525617259304114193977)
    ·
      refine ⟨31226644212944478085645483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41635525617259304114193977 31226644212944478085645483)
      ·
        refine ⟨46839966319416717128468225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31226644212944478085645483 46839966319416717128468225)
        ·
          refine ⟨35129974739562537846351169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46839966319416717128468225 35129974739562537846351169)
          ·
            refine ⟨26347481054671903384763377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35129974739562537846351169 26347481054671903384763377)
            ·
              refine ⟨19760610791003927538572533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26347481054671903384763377 19760610791003927538572533)
              ·
                refine ⟨1852557261656618206741175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19760610791003927538572533 1852557261656618206741175)
                ·
                  refine ⟨2778835892484927310111763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852557261656618206741175 2778835892484927310111763)
                  ·
                    refine ⟨4168253838727390965167645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2778835892484927310111763 4168253838727390965167645)
                    ·
                      refine ⟨1563095189522771611937867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168253838727390965167645 1563095189522771611937867)
                      ·
                        rfl

theorem cell23_3044117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_3044117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044117 prefixEnd_3044117 := by exact prefixLift 3044117
  have htrace : WordTrace (prefixWord ++ tailWord_3044117) baseStart_3044117 baseEnd_3044117 := by
    simpa [prefixWord, tailWord_3044117, baseEnd_3044117] using wordTrace_append hprefix tailTrace_3044117
  have hstable : (prefixWord ++ tailWord_3044117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044117).length < 2 ^ (prefixWord ++ tailWord_3044117).sum := by decide
  have hdescent : baseEnd_3044117 < baseStart_3044117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044161 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3044161 : Nat := 118140960795 + 3044161 * 2 ^ 59
def prefixEnd_3044161 : Nat := 4983230072969 + 3 ^ 40 * 3044161 * 2
def baseEnd_3044161 : Nat := 1563117782671569439787665

theorem tailTrace_3044161 : CollatzResearch.WordTrace tailWord_3044161 prefixEnd_3044161 1563117782671569439787665 := by
  unfold tailWord_3044161
  simp only [CollatzResearch.WordTrace]
  refine ⟨111029673124532073152452337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74019782083021382101634891 111029673124532073152452337)
  ·
    refine ⟨83272254843399054864339253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111029673124532073152452337 83272254843399054864339253)
    ·
      refine ⟨7806773891568661393531805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83272254843399054864339253 7806773891568661393531805)
      ·
        refine ⟨2927540209338248022574427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7806773891568661393531805 2927540209338248022574427)
        ·
          refine ⟨4391310314007372033861641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927540209338248022574427 4391310314007372033861641)
          ·
            refine ⟨3293482735505529025396231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391310314007372033861641 3293482735505529025396231)
            ·
              refine ⟨4940224103258293538094347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293482735505529025396231 4940224103258293538094347)
              ·
                refine ⟨7410336154887440307141521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940224103258293538094347 7410336154887440307141521)
                ·
                  refine ⟨5557752116165580230356141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7410336154887440307141521 5557752116165580230356141)
                  ·
                    refine ⟨2084157043562092586383553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5557752116165580230356141 2084157043562092586383553)
                    ·
                      refine ⟨1563117782671569439787665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084157043562092586383553 1563117782671569439787665)
                      ·
                        rfl

theorem cell23_3044161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3044161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044161 prefixEnd_3044161 := by exact prefixLift 3044161
  have htrace : WordTrace (prefixWord ++ tailWord_3044161) baseStart_3044161 baseEnd_3044161 := by
    simpa [prefixWord, tailWord_3044161, baseEnd_3044161] using wordTrace_append hprefix tailTrace_3044161
  have hstable : (prefixWord ++ tailWord_3044161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044161).length < 2 ^ (prefixWord ++ tailWord_3044161).sum := by decide
  have hdescent : baseEnd_3044161 < baseStart_3044161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044163 : List Nat := [1, 1, 1, 3, 1, 4, 5, 7]
def baseStart_3044163 : Nat := 118140960795 + 3044163 * 2 ^ 59
def prefixEnd_3044163 : Nat := 4983230072969 + 3 ^ 40 * 3044163 * 2
def baseEnd_3044163 : Nat := 57893289245662164146765

theorem tailTrace_3044163 : CollatzResearch.WordTrace tailWord_3044163 prefixEnd_3044163 57893289245662164146765 := by
  unfold tailWord_3044163
  simp only [CollatzResearch.WordTrace]
  refine ⟨111029746070524827494025143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74019830713683218329350095 111029746070524827494025143)
  ·
    refine ⟨166544619105787241241037715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111029746070524827494025143 166544619105787241241037715)
    ·
      refine ⟨249816928658680861861556573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166544619105787241241037715 249816928658680861861556573)
      ·
        refine ⟨93681348247005323198083715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249816928658680861861556573 93681348247005323198083715)
        ·
          refine ⟨140522022370507984797125573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93681348247005323198083715 140522022370507984797125573)
          ·
            refine ⟨26347879194470247149461045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140522022370507984797125573 26347879194470247149461045)
            ·
              refine ⟨2470113674481585670261973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26347879194470247149461045 2470113674481585670261973)
              ·
                refine ⟨57893289245662164146765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2470113674481585670261973 57893289245662164146765)
                ·
                  rfl

theorem cell23_3044163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 7].length) (baseStart_3044163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044163 prefixEnd_3044163 := by exact prefixLift 3044163
  have htrace : WordTrace (prefixWord ++ tailWord_3044163) baseStart_3044163 baseEnd_3044163 := by
    simpa [prefixWord, tailWord_3044163, baseEnd_3044163] using wordTrace_append hprefix tailTrace_3044163
  have hstable : (prefixWord ++ tailWord_3044163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044163).length < 2 ^ (prefixWord ++ tailWord_3044163).sum := by decide
  have hdescent : baseEnd_3044163 < baseStart_3044163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044177 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_3044177 : Nat := 118140960795 + 3044177 * 2 ^ 59
def prefixEnd_3044177 : Nat := 4983230072969 + 3 ^ 40 * 3044177 * 2
def baseEnd_3044177 : Nat := 1563125998362041377187591

theorem tailTrace_3044177 : CollatzResearch.WordTrace tailWord_3044177 prefixEnd_3044177 1563125998362041377187591 := by
  unfold tailWord_3044177
  simp only [CollatzResearch.WordTrace]
  refine ⟨111030256692474107885034785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74020171128316071923356523 111030256692474107885034785)
  ·
    refine ⟨83272692519355580913776089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111030256692474107885034785 83272692519355580913776089)
    ·
      refine ⟨62454519389516685685332067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83272692519355580913776089 62454519389516685685332067)
      ·
        refine ⟨93681779084275028527998101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62454519389516685685332067 93681779084275028527998101)
        ·
          refine ⟨4391333394575391962249911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93681779084275028527998101 4391333394575391962249911)
          ·
            refine ⟨6587000091863087943374867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391333394575391962249911 6587000091863087943374867)
            ·
              refine ⟨9880500137794631915062301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587000091863087943374867 9880500137794631915062301)
              ·
                refine ⟨3705187551672986968148363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9880500137794631915062301 3705187551672986968148363)
                ·
                  refine ⟨5557781327509480452222545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705187551672986968148363 5557781327509480452222545)
                  ·
                    refine ⟨4168335995632110339166909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557781327509480452222545 4168335995632110339166909)
                    ·
                      refine ⟨1563125998362041377187591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168335995632110339166909 1563125998362041377187591)
                      ·
                        rfl

theorem cell23_3044177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_3044177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044177 prefixEnd_3044177 := by exact prefixLift 3044177
  have htrace : WordTrace (prefixWord ++ tailWord_3044177) baseStart_3044177 baseEnd_3044177 := by
    simpa [prefixWord, tailWord_3044177, baseEnd_3044177] using wordTrace_append hprefix tailTrace_3044177
  have hstable : (prefixWord ++ tailWord_3044177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044177).length < 2 ^ (prefixWord ++ tailWord_3044177).sum := by decide
  have hdescent : baseEnd_3044177 < baseStart_3044177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044217 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 1, 3, 2]
def baseStart_3044217 : Nat := 118140960795 + 3044217 * 2 ^ 59
def prefixEnd_3044217 : Nat := 4983230072969 + 3 ^ 40 * 3044217 * 2
def baseEnd_3044217 : Nat := 1563146537588221220687407

theorem tailTrace_3044217 : CollatzResearch.WordTrace tailWord_3044217 prefixEnd_3044217 1563146537588221220687407 := by
  unfold tailWord_3044217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111031715612329194716490905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74021143741552796477660603 111031715612329194716490905)
  ·
    refine ⟨83273786709246896037368179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111031715612329194716490905 83273786709246896037368179)
    ·
      refine ⟨124910680063870344056052269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83273786709246896037368179 124910680063870344056052269)
      ·
        refine ⟨46841505023951379021019601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124910680063870344056052269 46841505023951379021019601)
        ·
          refine ⟨35131128767963534265764701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46841505023951379021019601 35131128767963534265764701)
          ·
            refine ⟨13174173287986325349661763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35131128767963534265764701 13174173287986325349661763)
            ·
              refine ⟨19761259931979488024492645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174173287986325349661763 19761259931979488024492645)
              ·
                refine ⟨3705236237246154004592371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19761259931979488024492645 3705236237246154004592371)
                ·
                  refine ⟨5557854355869231006888557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705236237246154004592371 5557854355869231006888557)
                  ·
                    refine ⟨2084195383450961627583209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5557854355869231006888557 2084195383450961627583209)
                    ·
                      refine ⟨1563146537588221220687407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084195383450961627583209 1563146537588221220687407)
                      ·
                        rfl

theorem cell23_3044217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_3044217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044217 prefixEnd_3044217 := by exact prefixLift 3044217
  have htrace : WordTrace (prefixWord ++ tailWord_3044217) baseStart_3044217 baseEnd_3044217 := by
    simpa [prefixWord, tailWord_3044217, baseEnd_3044217] using wordTrace_append hprefix tailTrace_3044217
  have hstable : (prefixWord ++ tailWord_3044217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044217).length < 2 ^ (prefixWord ++ tailWord_3044217).sum := by decide
  have hdescent : baseEnd_3044217 < baseStart_3044217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044233 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_3044233 : Nat := 118140960795 + 3044233 * 2 ^ 59
def prefixEnd_3044233 : Nat := 4983230072969 + 3 ^ 40 * 3044233 * 2
def baseEnd_3044233 : Nat := 1563154753278693158087333

theorem tailTrace_3044233 : CollatzResearch.WordTrace tailWord_3044233 prefixEnd_3044233 1563154753278693158087333 := by
  unfold tailWord_3044233
  simp only [CollatzResearch.WordTrace]
  refine ⟨111032299180271229449073353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74021532786847486299382235 111032299180271229449073353)
  ·
    refine ⟨83274224385203422086805015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111032299180271229449073353 83274224385203422086805015)
    ·
      refine ⟨124911336577805133130207523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83274224385203422086805015 124911336577805133130207523)
      ·
        refine ⟨187367004866707699695311285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124911336577805133130207523 187367004866707699695311285)
        ·
          refine ⟨17565656706253846846435433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187367004866707699695311285 17565656706253846846435433)
          ·
            refine ⟨13174242529690385134826575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17565656706253846846435433 13174242529690385134826575)
            ·
              refine ⟨19761363794535577702239863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174242529690385134826575 19761363794535577702239863)
              ·
                refine ⟨29642045691803366553359795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19761363794535577702239863 29642045691803366553359795)
                ·
                  refine ⟨44463068537705049830039693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29642045691803366553359795 44463068537705049830039693)
                  ·
                    refine ⟨16673650701639393686264885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44463068537705049830039693 16673650701639393686264885)
                    ·
                      refine ⟨1563154753278693158087333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16673650701639393686264885 1563154753278693158087333)
                      ·
                        rfl

theorem cell23_3044233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_3044233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044233 prefixEnd_3044233 := by exact prefixLift 3044233
  have htrace : WordTrace (prefixWord ++ tailWord_3044233) baseStart_3044233 baseEnd_3044233 := by
    simpa [prefixWord, tailWord_3044233, baseEnd_3044233] using wordTrace_append hprefix tailTrace_3044233
  have hstable : (prefixWord ++ tailWord_3044233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044233).length < 2 ^ (prefixWord ++ tailWord_3044233).sum := by decide
  have hdescent : baseEnd_3044233 < baseStart_3044233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044234 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3044234 : Nat := 118140960795 + 3044234 * 2 ^ 59
def prefixEnd_3044234 : Nat := 4983230072969 + 3 ^ 40 * 3044234 * 2
def baseEnd_3044234 : Nat := 1563155266759347654174829

theorem tailTrace_3044234 : CollatzResearch.WordTrace tailWord_3044234 prefixEnd_3044234 1563155266759347654174829 := by
  unfold tailWord_3044234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27758083913316901654964939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74021557102178404413239837 27758083913316901654964939)
  ·
    refine ⟨41637125869975352482447409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27758083913316901654964939 41637125869975352482447409)
    ·
      refine ⟨31227844402481514361835557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41637125869975352482447409 31227844402481514361835557)
      ·
        refine ⟨5855220825465283942844167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31227844402481514361835557 5855220825465283942844167)
        ·
          refine ⟨8782831238197925914266251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855220825465283942844167 8782831238197925914266251)
          ·
            refine ⟨13174246857296888871399377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782831238197925914266251 13174246857296888871399377)
            ·
              refine ⟨9880685142972666653549533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13174246857296888871399377 9880685142972666653549533)
              ·
                refine ⟨3705256928614749995081075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9880685142972666653549533 3705256928614749995081075)
                ·
                  refine ⟨5557885392922124992621613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705256928614749995081075 5557885392922124992621613)
                  ·
                    refine ⟨2084207022345796872233105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5557885392922124992621613 2084207022345796872233105)
                    ·
                      refine ⟨1563155266759347654174829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084207022345796872233105 1563155266759347654174829)
                      ·
                        rfl

theorem cell23_3044234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3044234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044234 prefixEnd_3044234 := by exact prefixLift 3044234
  have htrace : WordTrace (prefixWord ++ tailWord_3044234) baseStart_3044234 baseEnd_3044234 := by
    simpa [prefixWord, tailWord_3044234, baseEnd_3044234] using wordTrace_append hprefix tailTrace_3044234
  have hstable : (prefixWord ++ tailWord_3044234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044234).length < 2 ^ (prefixWord ++ tailWord_3044234).sum := by decide
  have hdescent : baseEnd_3044234 < baseStart_3044234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044243 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_3044243 : Nat := 118140960795 + 3044243 * 2 ^ 59
def prefixEnd_3044243 : Nat := 4983230072969 + 3 ^ 40 * 3044243 * 2
def baseEnd_3044243 : Nat := 1563159888085238118962287

theorem tailTrace_3044243 : CollatzResearch.WordTrace tailWord_3044243 prefixEnd_3044243 1563159888085238118962287 := by
  unfold tailWord_3044243
  simp only [CollatzResearch.WordTrace]
  refine ⟨111032663910235001156937383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74021775940156667437958255 111032663910235001156937383)
  ·
    refine ⟨166548995865352501735406075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111032663910235001156937383 166548995865352501735406075)
    ·
      refine ⟨249823493798028752603109113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166548995865352501735406075 249823493798028752603109113)
      ·
        refine ⟨187367620348521564452331835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249823493798028752603109113 187367620348521564452331835)
        ·
          refine ⟨281051430522782346678497753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187367620348521564452331835 281051430522782346678497753)
          ·
            refine ⟨210788572892086760008873315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281051430522782346678497753 210788572892086760008873315)
            ·
              refine ⟨316182859338130140013309973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210788572892086760008873315 316182859338130140013309973)
              ·
                refine ⟨14821071531474850313123905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316182859338130140013309973 14821071531474850313123905)
                ·
                  refine ⟨11115803648606137734842929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14821071531474850313123905 11115803648606137734842929)
                  ·
                    refine ⟨8336852736454603301132197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11115803648606137734842929 8336852736454603301132197)
                    ·
                      refine ⟨1563159888085238118962287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8336852736454603301132197 1563159888085238118962287)
                      ·
                        rfl

theorem cell23_3044243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_3044243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044243 prefixEnd_3044243 := by exact prefixLift 3044243
  have htrace : WordTrace (prefixWord ++ tailWord_3044243) baseStart_3044243 baseEnd_3044243 := by
    simpa [prefixWord, tailWord_3044243, baseEnd_3044243] using wordTrace_append hprefix tailTrace_3044243
  have hstable : (prefixWord ++ tailWord_3044243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044243).length < 2 ^ (prefixWord ++ tailWord_3044243).sum := by decide
  have hdescent : baseEnd_3044243 < baseStart_3044243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044247 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_3044247 : Nat := 118140960795 + 3044247 * 2 ^ 59
def prefixEnd_3044247 : Nat := 4983230072969 + 3 ^ 40 * 3044247 * 2
def baseEnd_3044247 : Nat := 1563161942007856103312269

theorem tailTrace_3044247 : CollatzResearch.WordTrace tailWord_3044247 prefixEnd_3044247 1563161942007856103312269 := by
  unfold tailWord_3044247
  simp only [CollatzResearch.WordTrace]
  refine ⟨111032809802220509840082995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74021873201480339893388663 111032809802220509840082995)
  ·
    refine ⟨166549214703330764760124493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111032809802220509840082995 166549214703330764760124493)
    ·
      refine ⟨62455955513749036785046685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166549214703330764760124493 62455955513749036785046685)
      ·
        refine ⟨23420983317655888794392507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62455955513749036785046685 23420983317655888794392507)
        ·
          refine ⟨35131474976483833191588761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23420983317655888794392507 35131474976483833191588761)
          ·
            refine ⟨26348606232362874893691571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35131474976483833191588761 26348606232362874893691571)
            ·
              refine ⟨39522909348544312340537357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26348606232362874893691571 39522909348544312340537357)
              ·
                refine ⟨14821091005704117127701509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39522909348544312340537357 14821091005704117127701509)
                ·
                  refine ⟨2778954563569521961444033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14821091005704117127701509 2778954563569521961444033)
                  ·
                    refine ⟨2084215922677141471083025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2778954563569521961444033 2084215922677141471083025)
                    ·
                      refine ⟨1563161942007856103312269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084215922677141471083025 1563161942007856103312269)
                      ·
                        rfl

theorem cell23_3044247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_3044247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044247 prefixEnd_3044247 := by exact prefixLift 3044247
  have htrace : WordTrace (prefixWord ++ tailWord_3044247) baseStart_3044247 baseEnd_3044247 := by
    simpa [prefixWord, tailWord_3044247, baseEnd_3044247] using wordTrace_append hprefix tailTrace_3044247
  have hstable : (prefixWord ++ tailWord_3044247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044247).length < 2 ^ (prefixWord ++ tailWord_3044247).sum := by decide
  have hdescent : baseEnd_3044247 < baseStart_3044247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044300 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_3044300 : Nat := 118140960795 + 3044300 * 2 ^ 59
def prefixEnd_3044300 : Nat := 4983230072969 + 3 ^ 40 * 3044300 * 2
def baseEnd_3044300 : Nat := 521063052160848131983175

theorem tailTrace_3044300 : CollatzResearch.WordTrace tailWord_3044300 prefixEnd_3044300 521063052160848131983175 := by
  unfold tailWord_3044300
  simp only [CollatzResearch.WordTrace]
  refine ⟨55517371435514249945881177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74023161914018999927841569 55517371435514249945881177)
  ·
    refine ⟨41638028576635687459410883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55517371435514249945881177 41638028576635687459410883)
    ·
      refine ⟨62457042864953531189116325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41638028576635687459410883 62457042864953531189116325)
      ·
        refine ⟨11710695537178787097959311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62457042864953531189116325 11710695537178787097959311)
        ·
          refine ⟨17566043305768180646938967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710695537178787097959311 17566043305768180646938967)
          ·
            refine ⟨26349064958652270970408451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17566043305768180646938967 26349064958652270970408451)
            ·
              refine ⟨39523597437978406455612677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26349064958652270970408451 39523597437978406455612677)
              ·
                refine ⟨7410674519620951210427377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39523597437978406455612677 7410674519620951210427377)
                ·
                  refine ⟨5558005889715713407820533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7410674519620951210427377 5558005889715713407820533)
                  ·
                    refine ⟨521063052160848131983175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5558005889715713407820533 521063052160848131983175)
                    ·
                      rfl

theorem cell23_3044300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_3044300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044300 prefixEnd_3044300 := by exact prefixLift 3044300
  have htrace : WordTrace (prefixWord ++ tailWord_3044300) baseStart_3044300 baseEnd_3044300 := by
    simpa [prefixWord, tailWord_3044300, baseEnd_3044300] using wordTrace_append hprefix tailTrace_3044300
  have hstable : (prefixWord ++ tailWord_3044300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044300).length < 2 ^ (prefixWord ++ tailWord_3044300).sum := by decide
  have hdescent : baseEnd_3044300 < baseStart_3044300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044334 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3044334 : Nat := 118140960795 + 3044334 * 2 ^ 59
def prefixEnd_3044334 : Nat := 4983230072969 + 3 ^ 40 * 3044334 * 2
def baseEnd_3044334 : Nat := 521068871608265754308123

theorem tailTrace_3044334 : CollatzResearch.WordTrace tailWord_3044334 prefixEnd_3044334 521068871608265754308123 := by
  unfold tailWord_3044334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13879497869113165462312507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74023988635270215799000037 13879497869113165462312507)
  ·
    refine ⟨20819246803669748193468761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13879497869113165462312507 20819246803669748193468761)
    ·
      refine ⟨15614435102752311145101571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20819246803669748193468761 15614435102752311145101571)
      ·
        refine ⟨23421652654128466717652357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15614435102752311145101571 23421652654128466717652357)
        ·
          refine ⟨4391559872649087509559817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23421652654128466717652357 4391559872649087509559817)
          ·
            refine ⟨3293669904486815632169863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391559872649087509559817 3293669904486815632169863)
            ·
              refine ⟨4940504856730223448254795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293669904486815632169863 4940504856730223448254795)
              ·
                refine ⟨7410757285095335172382193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940504856730223448254795 7410757285095335172382193)
                ·
                  refine ⟨5558067963821501379286645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7410757285095335172382193 5558067963821501379286645)
                  ·
                    refine ⟨521068871608265754308123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5558067963821501379286645 521068871608265754308123)
                    ·
                      rfl

theorem cell23_3044334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3044334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044334 prefixEnd_3044334 := by exact prefixLift 3044334
  have htrace : WordTrace (prefixWord ++ tailWord_3044334) baseStart_3044334 baseEnd_3044334 := by
    simpa [prefixWord, tailWord_3044334, baseEnd_3044334] using wordTrace_append hprefix tailTrace_3044334
  have hstable : (prefixWord ++ tailWord_3044334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044334).length < 2 ^ (prefixWord ++ tailWord_3044334).sum := by decide
  have hdescent : baseEnd_3044334 < baseStart_3044334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044337 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_3044337 : Nat := 118140960795 + 3044337 * 2 ^ 59
def prefixEnd_3044337 : Nat := 4983230072969 + 3 ^ 40 * 3044337 * 2
def baseEnd_3044337 : Nat := 1563208155266760751186855

theorem tailTrace_3044337 : CollatzResearch.WordTrace tailWord_3044337 prefixEnd_3044337 1563208155266760751186855 := by
  unfold tailWord_3044337
  simp only [CollatzResearch.WordTrace]
  refine ⟨111036092371894455210859265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74024061581262970140572843 111036092371894455210859265)
  ·
    refine ⟨83277069278920841408144449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111036092371894455210859265 83277069278920841408144449)
    ·
      refine ⟨62457801959190631056108337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83277069278920841408144449 62457801959190631056108337)
      ·
        refine ⟨46843351469392973292081253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62457801959190631056108337 46843351469392973292081253)
        ·
          refine ⟨8783128400511182492265235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46843351469392973292081253 8783128400511182492265235)
          ·
            refine ⟨13174692600766773738397853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8783128400511182492265235 13174692600766773738397853)
            ·
              refine ⟨4940509725287540151899195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13174692600766773738397853 4940509725287540151899195)
              ·
                refine ⟨7410764587931310227848793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940509725287540151899195 7410764587931310227848793)
                ·
                  refine ⟨5558073440948482670886595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7410764587931310227848793 5558073440948482670886595)
                  ·
                    refine ⟨8337110161422724006329893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558073440948482670886595 8337110161422724006329893)
                    ·
                      refine ⟨1563208155266760751186855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8337110161422724006329893 1563208155266760751186855)
                      ·
                        rfl

theorem cell23_3044337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_3044337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044337 prefixEnd_3044337 := by exact prefixLift 3044337
  have htrace : WordTrace (prefixWord ++ tailWord_3044337) baseStart_3044337 baseEnd_3044337 := by
    simpa [prefixWord, tailWord_3044337, baseEnd_3044337] using wordTrace_append hprefix tailTrace_3044337
  have hstable : (prefixWord ++ tailWord_3044337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044337).length < 2 ^ (prefixWord ++ tailWord_3044337).sum := by decide
  have hdescent : baseEnd_3044337 < baseStart_3044337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044360 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 8]
def baseStart_3044360 : Nat := 118140960795 + 3044360 * 2 ^ 59
def prefixEnd_3044360 : Nat := 4983230072969 + 3 ^ 40 * 3044360 * 2
def baseEnd_3044360 : Nat := 173691107257979351244361

theorem tailTrace_3044360 : CollatzResearch.WordTrace tailWord_3044360 prefixEnd_3044360 173691107257979351244361 := by
  unfold tailWord_3044360
  simp only [CollatzResearch.WordTrace]
  refine ⟨55518465625405565069473267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74024620833874086759297689 55518465625405565069473267)
  ·
    refine ⟨83277698438108347604209901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55518465625405565069473267 83277698438108347604209901)
    ·
      refine ⟨31229136914290630351578713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83277698438108347604209901 31229136914290630351578713)
      ·
        refine ⟨23421852685717972763684035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31229136914290630351578713 23421852685717972763684035)
        ·
          refine ⟨35132779028576959145526053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23421852685717972763684035 35132779028576959145526053)
          ·
            refine ⟨6587396067858179839786135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35132779028576959145526053 6587396067858179839786135)
            ·
              refine ⟨9881094101787269759679203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587396067858179839786135 9881094101787269759679203)
              ·
                refine ⟨14821641152680904639518805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881094101787269759679203 14821641152680904639518805)
                ·
                  refine ⟨173691107257979351244361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14821641152680904639518805 173691107257979351244361)
                  ·
                    rfl

theorem cell23_3044360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_3044360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044360 prefixEnd_3044360 := by exact prefixLift 3044360
  have htrace : WordTrace (prefixWord ++ tailWord_3044360) baseStart_3044360 baseEnd_3044360 := by
    simpa [prefixWord, tailWord_3044360, baseEnd_3044360] using wordTrace_append hprefix tailTrace_3044360
  have hstable : (prefixWord ++ tailWord_3044360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044360).length < 2 ^ (prefixWord ++ tailWord_3044360).sum := by decide
  have hdescent : baseEnd_3044360 < baseStart_3044360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044364 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_3044364 : Nat := 118140960795 + 3044364 * 2 ^ 59
def prefixEnd_3044364 : Nat := 4983230072969 + 3 ^ 40 * 3044364 * 2
def baseEnd_3044364 : Nat := 521074006414810715183077

theorem tailTrace_3044364 : CollatzResearch.WordTrace tailWord_3044364 prefixEnd_3044364 521074006414810715183077 := by
  unfold tailWord_3044364
  simp only [CollatzResearch.WordTrace]
  refine ⟨55518538571398319411046073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74024718095197759214728097 55518538571398319411046073)
  ·
    refine ⟨41638903928548739558284555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55518538571398319411046073 41638903928548739558284555)
    ·
      refine ⟨62458355892823109337426833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41638903928548739558284555 62458355892823109337426833)
      ·
        refine ⟨46843766919617332003070125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62458355892823109337426833 46843766919617332003070125)
        ·
          refine ⟨17566412594856499501151297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46843766919617332003070125 17566412594856499501151297)
          ·
            refine ⟨13174809446142374625863473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566412594856499501151297 13174809446142374625863473)
            ·
              refine ⟨9881107084606780969397605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13174809446142374625863473 9881107084606780969397605)
              ·
                refine ⟨1852707578363771431762051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9881107084606780969397605 1852707578363771431762051)
                ·
                  refine ⟨2779061367545657147643077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852707578363771431762051 2779061367545657147643077)
                  ·
                    refine ⟨521074006414810715183077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2779061367545657147643077 521074006414810715183077)
                    ·
                      rfl

theorem cell23_3044364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_3044364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044364 prefixEnd_3044364 := by exact prefixLift 3044364
  have htrace : WordTrace (prefixWord ++ tailWord_3044364) baseStart_3044364 baseEnd_3044364 := by
    simpa [prefixWord, tailWord_3044364, baseEnd_3044364] using wordTrace_append hprefix tailTrace_3044364
  have hstable : (prefixWord ++ tailWord_3044364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044364).length < 2 ^ (prefixWord ++ tailWord_3044364).sum := by decide
  have hdescent : baseEnd_3044364 < baseStart_3044364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044440 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3044440 : Nat := 118140960795 + 3044440 * 2 ^ 59
def prefixEnd_3044440 : Nat := 4983230072969 + 3 ^ 40 * 3044440 * 2
def baseEnd_3044440 : Nat := 1563261043774173848198881

theorem tailTrace_3044440 : CollatzResearch.WordTrace tailWord_3044440 prefixEnd_3044440 1563261043774173848198881 := by
  unfold tailWord_3044440
  simp only [CollatzResearch.WordTrace]
  refine ⟨55519924545260651900929387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74026566060347535867905849 55519924545260651900929387)
  ·
    refine ⟨83279886817890977851394081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55519924545260651900929387 83279886817890977851394081)
    ·
      refine ⟨62459915113418233388545561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83279886817890977851394081 62459915113418233388545561)
      ·
        refine ⟨46844936335063675041409171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62459915113418233388545561 46844936335063675041409171)
        ·
          refine ⟨70267404502595512562113757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46844936335063675041409171 70267404502595512562113757)
          ·
            refine ⟨26350276688473317210792659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70267404502595512562113757 26350276688473317210792659)
            ·
              refine ⟨39525415032709975816188989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26350276688473317210792659 39525415032709975816188989)
              ·
                refine ⟨14822030637266240931070871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39525415032709975816188989 14822030637266240931070871)
                ·
                  refine ⟨22233045955899361396606307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14822030637266240931070871 22233045955899361396606307)
                  ·
                    refine ⟨33349568933849042094909461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22233045955899361396606307 33349568933849042094909461)
                    ·
                      refine ⟨1563261043774173848198881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33349568933849042094909461 1563261043774173848198881)
                      ·
                        rfl

theorem cell23_3044440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3044440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044440 prefixEnd_3044440 := by exact prefixLift 3044440
  have htrace : WordTrace (prefixWord ++ tailWord_3044440) baseStart_3044440 baseEnd_3044440 := by
    simpa [prefixWord, tailWord_3044440, baseEnd_3044440] using wordTrace_append hprefix tailTrace_3044440
  have hstable : (prefixWord ++ tailWord_3044440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044440).length < 2 ^ (prefixWord ++ tailWord_3044440).sum := by decide
  have hdescent : baseEnd_3044440 < baseStart_3044440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044447 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3044447 : Nat := 118140960795 + 3044447 * 2 ^ 59
def prefixEnd_3044447 : Nat := 4983230072969 + 3 ^ 40 * 3044447 * 2
def baseEnd_3044447 : Nat := 1563264638138755320811349

theorem tailTrace_3044447 : CollatzResearch.WordTrace tailWord_3044447 prefixEnd_3044447 1563264638138755320811349 := by
  unfold tailWord_3044447
  simp only [CollatzResearch.WordTrace]
  refine ⟨111040104401495943997363595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74026736267663962664909063 111040104401495943997363595)
  ·
    refine ⟨166560156602243915996045393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111040104401495943997363595 166560156602243915996045393)
    ·
      refine ⟨124920117451682936997034045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166560156602243915996045393 124920117451682936997034045)
      ·
        refine ⟨46845044044381101373887767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124920117451682936997034045 46845044044381101373887767)
        ·
          refine ⟨70267566066571652060831651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46845044044381101373887767 70267566066571652060831651)
          ·
            refine ⟨105401349099857478091247477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70267566066571652060831651 105401349099857478091247477)
            ·
              refine ⟨9881376478111638571054451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105401349099857478091247477 9881376478111638571054451)
              ·
                refine ⟨14822064717167457856581677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881376478111638571054451 14822064717167457856581677)
                ·
                  refine ⟨5558274268937796696218129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14822064717167457856581677 5558274268937796696218129)
                  ·
                    refine ⟨4168705701703347522163597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5558274268937796696218129 4168705701703347522163597)
                    ·
                      refine ⟨1563264638138755320811349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168705701703347522163597 1563264638138755320811349)
                      ·
                        rfl

theorem cell23_3044447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3044447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044447 prefixEnd_3044447 := by exact prefixLift 3044447
  have htrace : WordTrace (prefixWord ++ tailWord_3044447) baseStart_3044447 baseEnd_3044447 := by
    simpa [prefixWord, tailWord_3044447, baseEnd_3044447] using wordTrace_append hprefix tailTrace_3044447
  have hstable : (prefixWord ++ tailWord_3044447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044447).length < 2 ^ (prefixWord ++ tailWord_3044447).sum := by decide
  have hdescent : baseEnd_3044447 < baseStart_3044447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044457 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_3044457 : Nat := 118140960795 + 3044457 * 2 ^ 59
def prefixEnd_3044457 : Nat := 4983230072969 + 3 ^ 40 * 3044457 * 2
def baseEnd_3044457 : Nat := 1563269772945300281686303

theorem tailTrace_3044457 : CollatzResearch.WordTrace tailWord_3044457 prefixEnd_3044457 1563269772945300281686303 := by
  unfold tailWord_3044457
  simp only [CollatzResearch.WordTrace]
  refine ⟨111040469131459715705227625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74026979420973143803485083 111040469131459715705227625)
  ·
    refine ⟨83280351848594786778920719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111040469131459715705227625 83280351848594786778920719)
    ·
      refine ⟨124920527772892180168381079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83280351848594786778920719 124920527772892180168381079)
      ·
        refine ⟨187380791659338270252571619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124920527772892180168381079 187380791659338270252571619)
        ·
          refine ⟨281071187489007405378857429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187380791659338270252571619 281071187489007405378857429)
          ·
            refine ⟨6587605956773611063566971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 281071187489007405378857429 6587605956773611063566971)
            ·
              refine ⟨9881408935160416595350457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587605956773611063566971 9881408935160416595350457)
              ·
                refine ⟨7411056701370312446512843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9881408935160416595350457 7411056701370312446512843)
                ·
                  refine ⟨11116585052055468669769265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7411056701370312446512843 11116585052055468669769265)
                  ·
                    refine ⟨8337438789041601502326949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11116585052055468669769265 8337438789041601502326949)
                    ·
                      refine ⟨1563269772945300281686303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8337438789041601502326949 1563269772945300281686303)
                      ·
                        rfl

theorem cell23_3044457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_3044457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044457 prefixEnd_3044457 := by exact prefixLift 3044457
  have htrace : WordTrace (prefixWord ++ tailWord_3044457) baseStart_3044457 baseEnd_3044457 := by
    simpa [prefixWord, tailWord_3044457, baseEnd_3044457] using wordTrace_append hprefix tailTrace_3044457
  have hstable : (prefixWord ++ tailWord_3044457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044457).length < 2 ^ (prefixWord ++ tailWord_3044457).sum := by decide
  have hdescent : baseEnd_3044457 < baseStart_3044457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044461 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3044461 : Nat := 118140960795 + 3044461 * 2 ^ 59
def prefixEnd_3044461 : Nat := 4983230072969 + 3 ^ 40 * 3044461 * 2
def baseEnd_3044461 : Nat := 1563271826867918266036285

theorem tailTrace_3044461 : CollatzResearch.WordTrace tailWord_3044461 prefixEnd_3044461 1563271826867918266036285 := by
  unfold tailWord_3044461
  simp only [CollatzResearch.WordTrace]
  refine ⟨111040615023445224388373237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74027076682296816258915491 111040615023445224388373237)
  ·
    refine ⟨10410057658447989786409991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111040615023445224388373237 10410057658447989786409991)
    ·
      refine ⟨15615086487671984679614987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10410057658447989786409991 15615086487671984679614987)
      ·
        refine ⟨23422629731507977019422481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15615086487671984679614987 23422629731507977019422481)
        ·
          refine ⟨17566972298630982764566861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23422629731507977019422481 17566972298630982764566861)
          ·
            refine ⟨6587614611986618536712573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17566972298630982764566861 6587614611986618536712573)
            ·
              refine ⟨2470355479494981951267215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6587614611986618536712573 2470355479494981951267215)
              ·
                refine ⟨3705533219242472926900823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470355479494981951267215 3705533219242472926900823)
                ·
                  refine ⟨5558299828863709390351235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705533219242472926900823 5558299828863709390351235)
                  ·
                    refine ⟨8337449743295564085526853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558299828863709390351235 8337449743295564085526853)
                    ·
                      refine ⟨1563271826867918266036285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8337449743295564085526853 1563271826867918266036285)
                      ·
                        rfl

theorem cell23_3044461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3044461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044461 prefixEnd_3044461 := by exact prefixLift 3044461
  have htrace : WordTrace (prefixWord ++ tailWord_3044461) baseStart_3044461 baseEnd_3044461 := by
    simpa [prefixWord, tailWord_3044461, baseEnd_3044461] using wordTrace_append hprefix tailTrace_3044461
  have hstable : (prefixWord ++ tailWord_3044461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044461).length < 2 ^ (prefixWord ++ tailWord_3044461).sum := by decide
  have hdescent : baseEnd_3044461 < baseStart_3044461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044477 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_3044477 : Nat := 118140960795 + 3044477 * 2 ^ 59
def prefixEnd_3044477 : Nat := 4983230072969 + 3 ^ 40 * 3044477 * 2
def baseEnd_3044477 : Nat := 1563280042558390203436211

theorem tailTrace_3044477 : CollatzResearch.WordTrace tailWord_3044477 prefixEnd_3044477 1563280042558390203436211 := by
  unfold tailWord_3044477
  simp only [CollatzResearch.WordTrace]
  refine ⟨111041198591387259120955685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74027465727591506080637123 111041198591387259120955685)
  ·
    refine ⟨20820224735885111085179191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111041198591387259120955685 20820224735885111085179191)
    ·
      refine ⟨31230337103827666627768787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20820224735885111085179191 31230337103827666627768787)
      ·
        refine ⟨46845505655741499941653181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31230337103827666627768787 46845505655741499941653181)
        ·
          refine ⟨17567064620903062478119943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46845505655741499941653181 17567064620903062478119943)
          ·
            refine ⟨26350596931354593717179915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17567064620903062478119943 26350596931354593717179915)
            ·
              refine ⟨39525895397031890575769873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26350596931354593717179915 39525895397031890575769873)
              ·
                refine ⟨29644421547773917931827405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39525895397031890575769873 29644421547773917931827405)
                ·
                  refine ⟨11116658080415219224435277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29644421547773917931827405 11116658080415219224435277)
                  ·
                    refine ⟨4168746780155707209163229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11116658080415219224435277 4168746780155707209163229)
                    ·
                      refine ⟨1563280042558390203436211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168746780155707209163229 1563280042558390203436211)
                      ·
                        rfl

theorem cell23_3044477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_3044477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044477 prefixEnd_3044477 := by exact prefixLift 3044477
  have htrace : WordTrace (prefixWord ++ tailWord_3044477) baseStart_3044477 baseEnd_3044477 := by
    simpa [prefixWord, tailWord_3044477, baseEnd_3044477] using wordTrace_append hprefix tailTrace_3044477
  have hstable : (prefixWord ++ tailWord_3044477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044477).length < 2 ^ (prefixWord ++ tailWord_3044477).sum := by decide
  have hdescent : baseEnd_3044477 < baseStart_3044477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044480 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_3044480 : Nat := 118140960795 + 3044480 * 2 ^ 59
def prefixEnd_3044480 : Nat := 4983230072969 + 3 ^ 40 * 3044480 * 2
def baseEnd_3044480 : Nat := 521093861000117897232899

theorem tailTrace_3044480 : CollatzResearch.WordTrace tailWord_3044480 prefixEnd_3044480 521093861000117897232899 := by
  unfold tailWord_3044480
  simp only [CollatzResearch.WordTrace]
  refine ⟨55520654005188195316657447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74027538673584260422209929 55520654005188195316657447)
  ·
    refine ⟨83280981007782292974986171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55520654005188195316657447 83280981007782292974986171)
    ·
      refine ⟨124921471511673439462479257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83280981007782292974986171 124921471511673439462479257)
      ·
        refine ⟨93691103633755079596859443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124921471511673439462479257 93691103633755079596859443)
        ·
          refine ⟨140536655450632619395289165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93691103633755079596859443 140536655450632619395289165)
          ·
            refine ⟨52701245793987232273233437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140536655450632619395289165 52701245793987232273233437)
            ·
              refine ⟨19762967172745212102462539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52701245793987232273233437 19762967172745212102462539)
              ·
                refine ⟨29644450759117818153693809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19762967172745212102462539 29644450759117818153693809)
                ·
                  refine ⟨22233338069338363615270357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29644450759117818153693809 22233338069338363615270357)
                  ·
                    refine ⟨521093861000117897232899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22233338069338363615270357 521093861000117897232899)
                    ·
                      rfl

theorem cell23_3044480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_3044480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044480 prefixEnd_3044480 := by exact prefixLift 3044480
  have htrace : WordTrace (prefixWord ++ tailWord_3044480) baseStart_3044480 baseEnd_3044480 := by
    simpa [prefixWord, tailWord_3044480, baseEnd_3044480] using wordTrace_append hprefix tailTrace_3044480
  have hstable : (prefixWord ++ tailWord_3044480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044480).length < 2 ^ (prefixWord ++ tailWord_3044480).sum := by decide
  have hdescent : baseEnd_3044480 < baseStart_3044480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044494 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3044494 : Nat := 118140960795 + 3044494 * 2 ^ 59
def prefixEnd_3044494 : Nat := 4983230072969 + 3 ^ 40 * 3044494 * 2
def baseEnd_3044494 : Nat := 1563288771729516636923633

theorem tailTrace_3044494 : CollatzResearch.WordTrace tailWord_3044494 prefixEnd_3044494 1563288771729516636923633 := by
  unfold tailWord_3044494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880227329040708878040567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74027879088217114016216357 13880227329040708878040567)
  ·
    refine ⟨20820340993561063317060851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880227329040708878040567 20820340993561063317060851)
    ·
      refine ⟨31230511490341594975591277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20820340993561063317060851 31230511490341594975591277)
      ·
        refine ⟨11711441808878098115846729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31230511490341594975591277 11711441808878098115846729)
        ·
          refine ⟨8783581356658573586885047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11711441808878098115846729 8783581356658573586885047)
          ·
            refine ⟨13175372034987860380327571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8783581356658573586885047 13175372034987860380327571)
            ·
              refine ⟨19763058052481790570491357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175372034987860380327571 19763058052481790570491357)
              ·
                refine ⟨7411146769680671463934259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19763058052481790570491357 7411146769680671463934259)
                ·
                  refine ⟨11116720154521007195901389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7411146769680671463934259 11116720154521007195901389)
                  ·
                    refine ⟨4168770057945377698463021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11116720154521007195901389 4168770057945377698463021)
                    ·
                      refine ⟨1563288771729516636923633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168770057945377698463021 1563288771729516636923633)
                      ·
                        rfl

theorem cell23_3044494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3044494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044494 prefixEnd_3044494 := by exact prefixLift 3044494
  have htrace : WordTrace (prefixWord ++ tailWord_3044494) baseStart_3044494 baseEnd_3044494 := by
    simpa [prefixWord, tailWord_3044494, baseEnd_3044494] using wordTrace_append hprefix tailTrace_3044494
  have hstable : (prefixWord ++ tailWord_3044494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044494).length < 2 ^ (prefixWord ++ tailWord_3044494).sum := by decide
  have hdescent : baseEnd_3044494 < baseStart_3044494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044545 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3044545 : Nat := 118140960795 + 3044545 * 2 ^ 59
def prefixEnd_3044545 : Nat := 4983230072969 + 3 ^ 40 * 3044545 * 2
def baseEnd_3044545 : Nat := 1563314959242895937385899

theorem tailTrace_3044545 : CollatzResearch.WordTrace tailWord_3044545 prefixEnd_3044545 1563314959242895937385899 := by
  unfold tailWord_3044545
  simp only [CollatzResearch.WordTrace]
  refine ⟨111043678755140906734431089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74029119170093937822954059 111043678755140906734431089)
  ·
    refine ⟨83282759066355680050823317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111043678755140906734431089 83282759066355680050823317)
    ·
      refine ⟨3903879331235422502382343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83282759066355680050823317 3903879331235422502382343)
      ·
        refine ⟨5855818996853133753573515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903879331235422502382343 5855818996853133753573515)
        ·
          refine ⟨8783728495279700630360273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855818996853133753573515 8783728495279700630360273)
          ·
            refine ⟨6587796371459775472770205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8783728495279700630360273 6587796371459775472770205)
            ·
              refine ⟨2470423639297415802288827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6587796371459775472770205 2470423639297415802288827)
              ·
                refine ⟨3705635458946123703433241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470423639297415802288827 3705635458946123703433241)
                ·
                  refine ⟨2779226594209592777574931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705635458946123703433241 2779226594209592777574931)
                  ·
                    refine ⟨4168839891314389166362397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779226594209592777574931 4168839891314389166362397)
                    ·
                      refine ⟨1563314959242895937385899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168839891314389166362397 1563314959242895937385899)
                      ·
                        rfl

theorem cell23_3044545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3044545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044545 prefixEnd_3044545 := by exact prefixLift 3044545
  have htrace : WordTrace (prefixWord ++ tailWord_3044545) baseStart_3044545 baseEnd_3044545 := by
    simpa [prefixWord, tailWord_3044545, baseEnd_3044545] using wordTrace_append hprefix tailTrace_3044545
  have hstable : (prefixWord ++ tailWord_3044545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044545).length < 2 ^ (prefixWord ++ tailWord_3044545).sum := by decide
  have hdescent : baseEnd_3044545 < baseStart_3044545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044551 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_3044551 : Nat := 118140960795 + 3044551 * 2 ^ 59
def prefixEnd_3044551 : Nat := 4983230072969 + 3 ^ 40 * 3044551 * 2
def baseEnd_3044551 : Nat := 1563318040126822913910871

theorem tailTrace_3044551 : CollatzResearch.WordTrace tailWord_3044551 prefixEnd_3044551 1563318040126822913910871 := by
  unfold tailWord_3044551
  simp only [CollatzResearch.WordTrace]
  refine ⟨111043897593119169759149507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74029265062079446506099671 111043897593119169759149507)
  ·
    refine ⟨166565846389678754638724261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111043897593119169759149507 166565846389678754638724261)
    ·
      refine ⟨31231096198064766494760799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166565846389678754638724261 31231096198064766494760799)
      ·
        refine ⟨46846644297097149742141199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31231096198064766494760799 46846644297097149742141199)
        ·
          refine ⟨70269966445645724613211799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46846644297097149742141199 70269966445645724613211799)
          ·
            refine ⟨105404949668468586919817699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70269966445645724613211799 105404949668468586919817699)
            ·
              refine ⟨158107424502702880379726549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105404949668468586919817699 158107424502702880379726549)
              ·
                refine ⟨3705642761782098758899841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158107424502702880379726549 3705642761782098758899841)
                ·
                  refine ⟨2779232071336574069174881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705642761782098758899841 2779232071336574069174881)
                  ·
                    refine ⟨2084424053502430551881161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2779232071336574069174881 2084424053502430551881161)
                    ·
                      refine ⟨1563318040126822913910871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084424053502430551881161 1563318040126822913910871)
                      ·
                        rfl

theorem cell23_3044551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_3044551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044551 prefixEnd_3044551 := by exact prefixLift 3044551
  have htrace : WordTrace (prefixWord ++ tailWord_3044551) baseStart_3044551 baseEnd_3044551 := by
    simpa [prefixWord, tailWord_3044551, baseEnd_3044551] using wordTrace_append hprefix tailTrace_3044551
  have hstable : (prefixWord ++ tailWord_3044551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044551).length < 2 ^ (prefixWord ++ tailWord_3044551).sum := by decide
  have hdescent : baseEnd_3044551 < baseStart_3044551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044567 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_3044567 : Nat := 118140960795 + 3044567 * 2 ^ 59
def prefixEnd_3044567 : Nat := 4983230072969 + 3 ^ 40 * 3044567 * 2
def baseEnd_3044567 : Nat := 1563326255817294851310797

theorem tailTrace_3044567 : CollatzResearch.WordTrace tailWord_3044567 prefixEnd_3044567 1563326255817294851310797 := by
  unfold tailWord_3044567
  simp only [CollatzResearch.WordTrace]
  refine ⟨111044481161061204491731955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74029654107374136327821303 111044481161061204491731955)
  ·
    refine ⟨166566721741591806737597933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111044481161061204491731955 166566721741591806737597933)
    ·
      refine ⟨62462520653096927526599225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166566721741591806737597933 62462520653096927526599225)
      ·
        refine ⟨46846890489822695644949419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62462520653096927526599225 46846890489822695644949419)
        ·
          refine ⟨70270335734734043467424129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46846890489822695644949419 70270335734734043467424129)
          ·
            refine ⟨52702751801050532600568097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70270335734734043467424129 52702751801050532600568097)
            ·
              refine ⟨39527063850787899450426073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52702751801050532600568097 39527063850787899450426073)
              ·
                refine ⟨29645297888090924587819555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39527063850787899450426073 29645297888090924587819555)
                ·
                  refine ⟨44467946832136386881729333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29645297888090924587819555 44467946832136386881729333)
                  ·
                    refine ⟨4168870015512786270162125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44467946832136386881729333 4168870015512786270162125)
                    ·
                      refine ⟨1563326255817294851310797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168870015512786270162125 1563326255817294851310797)
                      ·
                        rfl

theorem cell23_3044567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_3044567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044567 prefixEnd_3044567 := by exact prefixLift 3044567
  have htrace : WordTrace (prefixWord ++ tailWord_3044567) baseStart_3044567 baseEnd_3044567 := by
    simpa [prefixWord, tailWord_3044567, baseEnd_3044567] using wordTrace_append hprefix tailTrace_3044567
  have hstable : (prefixWord ++ tailWord_3044567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044567).length < 2 ^ (prefixWord ++ tailWord_3044567).sum := by decide
  have hdescent : baseEnd_3044567 < baseStart_3044567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044587 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 4, 5]
def baseStart_3044587 : Nat := 118140960795 + 3044587 * 2 ^ 59
def prefixEnd_3044587 : Nat := 4983230072969 + 3 ^ 40 * 3044587 * 2
def baseEnd_3044587 : Nat := 521112175143461591020235

theorem tailTrace_3044587 : CollatzResearch.WordTrace tailWord_3044587 prefixEnd_3044587 521112175143461591020235 := by
  unfold tailWord_3044587
  simp only [CollatzResearch.WordTrace]
  refine ⟨111045210620988747907460015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74030140413992498604973343 111045210620988747907460015)
  ·
    refine ⟨166567815931483121861190023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111045210620988747907460015 166567815931483121861190023)
    ·
      refine ⟨249851723897224682791785035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166567815931483121861190023 249851723897224682791785035)
      ·
        refine ⟨374777585845837024187677553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249851723897224682791785035 374777585845837024187677553)
        ·
          refine ⟨281083189384377768140758165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374777585845837024187677553 281083189384377768140758165)
          ·
            refine ⟨13175774502392707881598039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 281083189384377768140758165 13175774502392707881598039)
            ·
              refine ⟨19763661753589061822397059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175774502392707881598039 19763661753589061822397059)
              ·
                refine ⟨29645492630383592733595589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19763661753589061822397059 29645492630383592733595589)
                ·
                  refine ⟨5558529868196923637549173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29645492630383592733595589 5558529868196923637549173)
                  ·
                    refine ⟨521112175143461591020235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5558529868196923637549173 521112175143461591020235)
                    ·
                      rfl

theorem cell23_3044587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 5].length) (baseStart_3044587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044587 prefixEnd_3044587 := by exact prefixLift 3044587
  have htrace : WordTrace (prefixWord ++ tailWord_3044587) baseStart_3044587 baseEnd_3044587 := by
    simpa [prefixWord, tailWord_3044587, baseEnd_3044587] using wordTrace_append hprefix tailTrace_3044587
  have hstable : (prefixWord ++ tailWord_3044587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044587).length < 2 ^ (prefixWord ++ tailWord_3044587).sum := by decide
  have hdescent : baseEnd_3044587 < baseStart_3044587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044591 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 7]
def baseStart_3044591 : Nat := 118140960795 + 3044591 * 2 ^ 59
def prefixEnd_3044591 : Nat := 4983230072969 + 3 ^ 40 * 3044591 * 2
def baseEnd_3044591 : Nat := 173704286594778084156743

theorem tailTrace_3044591 : CollatzResearch.WordTrace tailWord_3044591 prefixEnd_3044591 173704286594778084156743 := by
  unfold tailWord_3044591
  simp only [CollatzResearch.WordTrace]
  refine ⟨111045356512974256590605627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74030237675316171060403751 111045356512974256590605627)
  ·
    refine ⟨166568034769461384885908441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111045356512974256590605627 166568034769461384885908441)
    ·
      refine ⟨124926026077096038664431331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166568034769461384885908441 124926026077096038664431331)
      ·
        refine ⟨187389039115644057996646997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124926026077096038664431331 187389039115644057996646997)
        ·
          refine ⟨2195965302136453804648207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 187389039115644057996646997 2195965302136453804648207)
          ·
            refine ⟨3293947953204680706972311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195965302136453804648207 3293947953204680706972311)
            ·
              refine ⟨4940921929807021060458467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293947953204680706972311 4940921929807021060458467)
              ·
                refine ⟨7411382894710531590687701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940921929807021060458467 7411382894710531590687701)
                ·
                  refine ⟨173704286594778084156743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7411382894710531590687701 173704286594778084156743)
                  ·
                    rfl

theorem cell23_3044591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 7].length) (baseStart_3044591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044591 prefixEnd_3044591 := by exact prefixLift 3044591
  have htrace : WordTrace (prefixWord ++ tailWord_3044591) baseStart_3044591 baseEnd_3044591 := by
    simpa [prefixWord, tailWord_3044591, baseEnd_3044591] using wordTrace_append hprefix tailTrace_3044591
  have hstable : (prefixWord ++ tailWord_3044591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044591).length < 2 ^ (prefixWord ++ tailWord_3044591).sum := by decide
  have hdescent : baseEnd_3044591 < baseStart_3044591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044596 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3044596 : Nat := 118140960795 + 3044596 * 2 ^ 59
def prefixEnd_3044596 : Nat := 4983230072969 + 3 ^ 40 * 3044596 * 2
def baseEnd_3044596 : Nat := 1563341146756275237848165

theorem tailTrace_3044596 : CollatzResearch.WordTrace tailWord_3044596 prefixEnd_3044596 1563341146756275237848165 := by
  unfold tailWord_3044596
  simp only [CollatzResearch.WordTrace]
  refine ⟨55522769438978071222268821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74030359251970761629691761 55522769438978071222268821)
  ·
    refine ⟨2602629817452097088543851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55522769438978071222268821 2602629817452097088543851)
    ·
      refine ⟨3903944726178145632815777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602629817452097088543851 3903944726178145632815777)
      ·
        refine ⟨2927958544633609224611833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3903944726178145632815777 2927958544633609224611833)
        ·
          refine ⟨2195968908475206918458875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927958544633609224611833 2195968908475206918458875)
          ·
            refine ⟨3293953362712810377688313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195968908475206918458875 3293953362712810377688313)
            ·
              refine ⟨2470465022034607783266235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3293953362712810377688313 2470465022034607783266235)
              ·
                refine ⟨3705697533051911674899353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470465022034607783266235 3705697533051911674899353)
                ·
                  refine ⟨2779273149788933756174515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705697533051911674899353 2779273149788933756174515)
                  ·
                    refine ⟨4168909724683400634261773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779273149788933756174515 4168909724683400634261773)
                    ·
                      refine ⟨1563341146756275237848165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168909724683400634261773 1563341146756275237848165)
                      ·
                        rfl

theorem cell23_3044596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3044596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044596 prefixEnd_3044596 := by exact prefixLift 3044596
  have htrace : WordTrace (prefixWord ++ tailWord_3044596) baseStart_3044596 baseEnd_3044596 := by
    simpa [prefixWord, tailWord_3044596, baseEnd_3044596] using wordTrace_append hprefix tailTrace_3044596
  have hstable : (prefixWord ++ tailWord_3044596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044596).length < 2 ^ (prefixWord ++ tailWord_3044596).sum := by decide
  have hdescent : baseEnd_3044596 < baseStart_3044596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044708 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_3044708 : Nat := 118140960795 + 3044708 * 2 ^ 59
def prefixEnd_3044708 : Nat := 4983230072969 + 3 ^ 40 * 3044708 * 2
def baseEnd_3044708 : Nat := 1563398656589578799647649

theorem tailTrace_3044708 : CollatzResearch.WordTrace tailWord_3044708 prefixEnd_3044708 1563398656589578799647649 := by
  unfold tailWord_3044708
  simp only [CollatzResearch.WordTrace]
  refine ⟨55524811926775192786307389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74033082569033590381743185 55524811926775192786307389)
  ·
    refine ⟨20821804472540697294865271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55524811926775192786307389 20821804472540697294865271)
    ·
      refine ⟨31232706708811045942297907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20821804472540697294865271 31232706708811045942297907)
      ·
        refine ⟨46849060063216568913446861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31232706708811045942297907 46849060063216568913446861)
        ·
          refine ⟨17568397523706213342542573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46849060063216568913446861 17568397523706213342542573)
          ·
            refine ⟨6588149071389830003453465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17568397523706213342542573 6588149071389830003453465)
            ·
              refine ⟨4941111803542372502590099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6588149071389830003453465 4941111803542372502590099)
              ·
                refine ⟨7411667705313558753885149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941111803542372502590099 7411667705313558753885149)
                ·
                  refine ⟨2779375389492584532706931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7411667705313558753885149 2779375389492584532706931)
                  ·
                    refine ⟨4169063084238876799060397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779375389492584532706931 4169063084238876799060397)
                    ·
                      refine ⟨1563398656589578799647649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169063084238876799060397 1563398656589578799647649)
                      ·
                        rfl

theorem cell23_3044708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_3044708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044708 prefixEnd_3044708 := by exact prefixLift 3044708
  have htrace : WordTrace (prefixWord ++ tailWord_3044708) baseStart_3044708 baseEnd_3044708 := by
    simpa [prefixWord, tailWord_3044708, baseEnd_3044708] using wordTrace_append hprefix tailTrace_3044708
  have hstable : (prefixWord ++ tailWord_3044708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044708).length < 2 ^ (prefixWord ++ tailWord_3044708).sum := by decide
  have hdescent : baseEnd_3044708 < baseStart_3044708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044731 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 4]
def baseStart_3044731 : Nat := 118140960795 + 3044731 * 2 ^ 59
def prefixEnd_3044731 : Nat := 4983230072969 + 3 ^ 40 * 3044731 * 2
def baseEnd_3044731 : Nat := 1563410466644632209660043

theorem tailTrace_3044731 : CollatzResearch.WordTrace tailWord_3044731 prefixEnd_3044731 1563410466644632209660043 := by
  unfold tailWord_3044731
  simp only [CollatzResearch.WordTrace]
  refine ⟨111050462732467060500702047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74033641821644707000468031 111050462732467060500702047)
  ·
    refine ⟨166575694098700590751053071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111050462732467060500702047 166575694098700590751053071)
    ·
      refine ⟨249863541148050886126579607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166575694098700590751053071 249863541148050886126579607)
      ·
        refine ⟨374795311722076329189869411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249863541148050886126579607 374795311722076329189869411)
        ·
          refine ⟨562192967583114493784804117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374795311722076329189869411 562192967583114493784804117)
          ·
            refine ⟨26352795355458491896162693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 562192967583114493784804117 26352795355458491896162693)
            ·
              refine ⟨4941149129148467230530505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26352795355458491896162693 4941149129148467230530505)
              ·
                refine ⟨3705861846861350422897879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941149129148467230530505 3705861846861350422897879)
                ·
                  refine ⟨5558792770292025634346819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705861846861350422897879 5558792770292025634346819)
                  ·
                    refine ⟨8338189155438038451520229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558792770292025634346819 8338189155438038451520229)
                    ·
                      refine ⟨1563410466644632209660043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8338189155438038451520229 1563410466644632209660043)
                      ·
                        rfl

theorem cell23_3044731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 4].length) (baseStart_3044731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044731 prefixEnd_3044731 := by exact prefixLift 3044731
  have htrace : WordTrace (prefixWord ++ tailWord_3044731) baseStart_3044731 baseEnd_3044731 := by
    simpa [prefixWord, tailWord_3044731, baseEnd_3044731] using wordTrace_append hprefix tailTrace_3044731
  have hstable : (prefixWord ++ tailWord_3044731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044731).length < 2 ^ (prefixWord ++ tailWord_3044731).sum := by decide
  have hdescent : baseEnd_3044731 < baseStart_3044731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044765 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_3044765 : Nat := 118140960795 + 3044765 * 2 ^ 59
def prefixEnd_3044765 : Nat := 4983230072969 + 3 ^ 40 * 3044765 * 2
def baseEnd_3044765 : Nat := 1563427924986885076634887

theorem tailTrace_3044765 : CollatzResearch.WordTrace tailWord_3044765 prefixEnd_3044765 1563427924986885076634887 := by
  unfold tailWord_3044765
  simp only [CollatzResearch.WordTrace]
  refine ⟨111051702814343884307439749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74034468542895922871626499 111051702814343884307439749)
  ·
    refine ⟨20822194277689478307644953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111051702814343884307439749 20822194277689478307644953)
    ·
      refine ⟨15616645708267108730733715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20822194277689478307644953 15616645708267108730733715)
      ·
        refine ⟨23424968562400663096100573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15616645708267108730733715 23424968562400663096100573)
        ·
          refine ⟨8784363210900248661037715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23424968562400663096100573 8784363210900248661037715)
          ·
            refine ⟨13176544816350372991556573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8784363210900248661037715 13176544816350372991556573)
            ·
              refine ⟨4941204306131389871833715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13176544816350372991556573 4941204306131389871833715)
              ·
                refine ⟨7411806459197084807750573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941204306131389871833715 7411806459197084807750573)
                ·
                  refine ⟨2779427422198906802906465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7411806459197084807750573 2779427422198906802906465)
                  ·
                    refine ⟨2084570566649180102179849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2779427422198906802906465 2084570566649180102179849)
                    ·
                      refine ⟨1563427924986885076634887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084570566649180102179849 1563427924986885076634887)
                      ·
                        rfl

theorem cell23_3044765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_3044765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044765 prefixEnd_3044765 := by exact prefixLift 3044765
  have htrace : WordTrace (prefixWord ++ tailWord_3044765) baseStart_3044765 baseEnd_3044765 := by
    simpa [prefixWord, tailWord_3044765, baseEnd_3044765] using wordTrace_append hprefix tailTrace_3044765
  have hstable : (prefixWord ++ tailWord_3044765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044765).length < 2 ^ (prefixWord ++ tailWord_3044765).sum := by decide
  have hdescent : baseEnd_3044765 < baseStart_3044765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044824 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3044824 : Nat := 118140960795 + 3044824 * 2 ^ 59
def prefixEnd_3044824 : Nat := 4983230072969 + 3 ^ 40 * 3044824 * 2
def baseEnd_3044824 : Nat := 1563458220345500345797115

theorem tailTrace_3044824 : CollatzResearch.WordTrace tailWord_3044824 prefixEnd_3044824 1563458220345500345797115 := by
  unfold tailWord_3044824
  simp only [CollatzResearch.WordTrace]
  refine ⟨55526927360565068691918763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74035903147420091589225017 55526927360565068691918763)
  ·
    refine ⟨83290391040847603037878145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55526927360565068691918763 83290391040847603037878145)
    ·
      refine ⟨62467793280635702278408609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83290391040847603037878145 62467793280635702278408609)
      ·
        refine ⟨46850844960476776708806457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62467793280635702278408609 46850844960476776708806457)
        ·
          refine ⟨35138133720357582531604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46850844960476776708806457 35138133720357582531604843)
          ·
            refine ⟨52707200580536373797407265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35138133720357582531604843 52707200580536373797407265)
            ·
              refine ⟨39530400435402280348055449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52707200580536373797407265 39530400435402280348055449)
              ·
                refine ⟨29647800326551710261041587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39530400435402280348055449 29647800326551710261041587)
                ·
                  refine ⟨44471700489827565391562381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29647800326551710261041587 44471700489827565391562381)
                  ·
                    refine ⟨16676887683685337021835893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44471700489827565391562381 16676887683685337021835893)
                    ·
                      refine ⟨1563458220345500345797115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16676887683685337021835893 1563458220345500345797115)
                      ·
                        rfl

theorem cell23_3044824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3044824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044824 prefixEnd_3044824 := by exact prefixLift 3044824
  have htrace : WordTrace (prefixWord ++ tailWord_3044824) baseStart_3044824 baseEnd_3044824 := by
    simpa [prefixWord, tailWord_3044824, baseEnd_3044824] using wordTrace_append hprefix tailTrace_3044824
  have hstable : (prefixWord ++ tailWord_3044824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044824).length < 2 ^ (prefixWord ++ tailWord_3044824).sum := by decide
  have hdescent : baseEnd_3044824 < baseStart_3044824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044878 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_3044878 : Nat := 118140960795 + 3044878 * 2 ^ 59
def prefixEnd_3044878 : Nat := 4983230072969 + 3 ^ 40 * 3044878 * 2
def baseEnd_3044878 : Nat := 173720660922315903835763

theorem tailTrace_3044878 : CollatzResearch.WordTrace tailWord_3044878 prefixEnd_3044878 173720660922315903835763 := by
  unfold tailWord_3044878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881978032866813075787911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74037216175289669737535525 13881978032866813075787911)
  ·
    refine ⟨20822967049300219613681867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13881978032866813075787911 20822967049300219613681867)
    ·
      refine ⟨31234450573950329420522801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20822967049300219613681867 31234450573950329420522801)
      ·
        refine ⟨23425837930462747065392101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31234450573950329420522801 23425837930462747065392101)
        ·
          refine ⟨4392344611961765074761019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23425837930462747065392101 4392344611961765074761019)
          ·
            refine ⟨6588516917942647612141529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392344611961765074761019 6588516917942647612141529)
            ·
              refine ⟨4941387688456985709106147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6588516917942647612141529 4941387688456985709106147)
              ·
                refine ⟨7412081532685478563659221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941387688456985709106147 7412081532685478563659221)
                ·
                  refine ⟨173720660922315903835763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7412081532685478563659221 173720660922315903835763)
                  ·
                    rfl

theorem cell23_3044878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_3044878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044878 prefixEnd_3044878 := by exact prefixLift 3044878
  have htrace : WordTrace (prefixWord ++ tailWord_3044878) baseStart_3044878 baseEnd_3044878 := by
    simpa [prefixWord, tailWord_3044878, baseEnd_3044878] using wordTrace_append hprefix tailTrace_3044878
  have hstable : (prefixWord ++ tailWord_3044878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044878).length < 2 ^ (prefixWord ++ tailWord_3044878).sum := by decide
  have hdescent : baseEnd_3044878 < baseStart_3044878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044898 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_3044898 : Nat := 118140960795 + 3044898 * 2 ^ 59
def prefixEnd_3044898 : Nat := 4983230072969 + 3 ^ 40 * 3044898 * 2
def baseEnd_3044898 : Nat := 1563496217913933056271775

theorem tailTrace_3044898 : CollatzResearch.WordTrace tailWord_3044898 prefixEnd_3044898 1563496217913933056271775 := by
  unfold tailWord_3044898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764138430715512005507837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74037702481908032014687565 27764138430715512005507837)
  ·
    refine ⟨10411551911518317002065439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27764138430715512005507837 10411551911518317002065439)
    ·
      refine ⟨15617327867277475503098159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411551911518317002065439 15617327867277475503098159)
      ·
        refine ⟨23425991800916213254647239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15617327867277475503098159 23425991800916213254647239)
        ·
          refine ⟨35138987701374319881970859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23425991800916213254647239 35138987701374319881970859)
          ·
            refine ⟨52708481552061479822956289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35138987701374319881970859 52708481552061479822956289)
            ·
              refine ⟨39531361164046109867217217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52708481552061479822956289 39531361164046109867217217)
              ·
                refine ⟨29648520873034582400412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39531361164046109867217217 29648520873034582400412913)
                ·
                  refine ⟨22236390654775936800309685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29648520873034582400412913 22236390654775936800309685)
                  ·
                    refine ⟨2084661623885244075029033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22236390654775936800309685 2084661623885244075029033)
                    ·
                      refine ⟨1563496217913933056271775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084661623885244075029033 1563496217913933056271775)
                      ·
                        rfl

theorem cell23_3044898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_3044898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044898 prefixEnd_3044898 := by exact prefixLift 3044898
  have htrace : WordTrace (prefixWord ++ tailWord_3044898) baseStart_3044898 baseEnd_3044898 := by
    simpa [prefixWord, tailWord_3044898, baseEnd_3044898] using wordTrace_append hprefix tailTrace_3044898
  have hstable : (prefixWord ++ tailWord_3044898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044898).length < 2 ^ (prefixWord ++ tailWord_3044898).sum := by decide
  have hdescent : baseEnd_3044898 < baseStart_3044898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044948 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3044948 : Nat := 118140960795 + 3044948 * 2 ^ 59
def prefixEnd_3044948 : Nat := 4983230072969 + 3 ^ 40 * 3044948 * 2
def baseEnd_3044948 : Nat := 1563521891946657860646545

theorem tailTrace_3044948 : CollatzResearch.WordTrace tailWord_3044948 prefixEnd_3044948 1563521891946657860646545 := by
  unfold tailWord_3044948
  simp only [CollatzResearch.WordTrace]
  refine ⟨55529188686340453280675749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74038918248453937707567665 55529188686340453280675749)
  ·
    refine ⟨10411722878688834990126703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55529188686340453280675749 10411722878688834990126703)
    ·
      refine ⟨15617584318033252485190055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411722878688834990126703 15617584318033252485190055)
      ·
        refine ⟨23426376477049878727785083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15617584318033252485190055 23426376477049878727785083)
        ·
          refine ⟨35139564715574818091677625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23426376477049878727785083 35139564715574818091677625)
          ·
            refine ⟨26354673536681113568758219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35139564715574818091677625 26354673536681113568758219)
            ·
              refine ⟨39532010305021670353137329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26354673536681113568758219 39532010305021670353137329)
              ·
                refine ⟨29649007728766252764852997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39532010305021670353137329 29649007728766252764852997)
                ·
                  refine ⟨5559188949143672393409937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29649007728766252764852997 5559188949143672393409937)
                  ·
                    refine ⟨4169391711857754295057453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559188949143672393409937 4169391711857754295057453)
                    ·
                      refine ⟨1563521891946657860646545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169391711857754295057453 1563521891946657860646545)
                      ·
                        rfl

theorem cell23_3044948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3044948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044948 prefixEnd_3044948 := by exact prefixLift 3044948
  have htrace : WordTrace (prefixWord ++ tailWord_3044948) baseStart_3044948 baseEnd_3044948 := by
    simpa [prefixWord, tailWord_3044948, baseEnd_3044948] using wordTrace_append hprefix tailTrace_3044948
  have hstable : (prefixWord ++ tailWord_3044948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044948).length < 2 ^ (prefixWord ++ tailWord_3044948).sum := by decide
  have hdescent : baseEnd_3044948 < baseStart_3044948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044965 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3044965 : Nat := 118140960795 + 3044965 * 2 ^ 59
def prefixEnd_3044965 : Nat := 4983230072969 + 3 ^ 40 * 3044965 * 2
def baseEnd_3044965 : Nat := 1563530621117784294133967

theorem tailTrace_3044965 : CollatzResearch.WordTrace tailWord_3044965 prefixEnd_3044965 1563530621117784294133967 := by
  unfold tailWord_3044965
  simp only [CollatzResearch.WordTrace]
  refine ⟨111058997413619318464720349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74039331609079545643146899 111058997413619318464720349)
  ·
    refine ⟨41647124030107244424270131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111058997413619318464720349 41647124030107244424270131)
    ·
      refine ⟨62470686045160866636405197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41647124030107244424270131 62470686045160866636405197)
      ·
        refine ⟨23426507266935324988651949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62470686045160866636405197 23426507266935324988651949)
        ·
          refine ⟨8784940225100746870744481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23426507266935324988651949 8784940225100746870744481)
          ·
            refine ⟨6588705168825560153058361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8784940225100746870744481 6588705168825560153058361)
            ·
              refine ⟨4941528876619170114793771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6588705168825560153058361 4941528876619170114793771)
              ·
                refine ⟨7412293314928755172190657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941528876619170114793771 7412293314928755172190657)
                ·
                  refine ⟨5559219986196566379142993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412293314928755172190657 5559219986196566379142993)
                  ·
                    refine ⟨4169414989647424784357245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559219986196566379142993 4169414989647424784357245)
                    ·
                      refine ⟨1563530621117784294133967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169414989647424784357245 1563530621117784294133967)
                      ·
                        rfl

theorem cell23_3044965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3044965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044965 prefixEnd_3044965 := by exact prefixLift 3044965
  have htrace : WordTrace (prefixWord ++ tailWord_3044965) baseStart_3044965 baseEnd_3044965 := by
    simpa [prefixWord, tailWord_3044965, baseEnd_3044965] using wordTrace_append hprefix tailTrace_3044965
  have hstable : (prefixWord ++ tailWord_3044965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044965).length < 2 ^ (prefixWord ++ tailWord_3044965).sum := by decide
  have hdescent : baseEnd_3044965 < baseStart_3044965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044988 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_3044988 : Nat := 118140960795 + 3044988 * 2 ^ 59
def prefixEnd_3044988 : Nat := 4983230072969 + 3 ^ 40 * 3044988 * 2
def baseEnd_3044988 : Nat := 1563542431172837704146361

theorem tailTrace_3044988 : CollatzResearch.WordTrace tailWord_3044988 prefixEnd_3044988 1563542431172837704146361 := by
  unfold tailWord_3044988
  simp only [CollatzResearch.WordTrace]
  refine ⟨55529918146267996696403809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74039890861690662261871745 55529918146267996696403809)
  ·
    refine ⟨41647438609700997522302857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55529918146267996696403809 41647438609700997522302857)
    ·
      refine ⟨31235578957275748141727143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41647438609700997522302857 31235578957275748141727143)
      ·
        refine ⟨46853368435913622212590715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31235578957275748141727143 46853368435913622212590715)
        ·
          refine ⟨70280052653870433318886073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46853368435913622212590715 70280052653870433318886073)
          ·
            refine ⟨52710039490402824989164555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70280052653870433318886073 52710039490402824989164555)
            ·
              refine ⟨79065059235604237483746833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52710039490402824989164555 79065059235604237483746833)
              ·
                refine ⟨59298794426703178112810125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79065059235604237483746833 59298794426703178112810125)
                ·
                  refine ⟨22237047910013691792303797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59298794426703178112810125 22237047910013691792303797)
                  ·
                    refine ⟨2084723241563783605528481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22237047910013691792303797 2084723241563783605528481)
                    ·
                      refine ⟨1563542431172837704146361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084723241563783605528481 1563542431172837704146361)
                      ·
                        rfl

theorem cell23_3044988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_3044988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044988 prefixEnd_3044988 := by exact prefixLift 3044988
  have htrace : WordTrace (prefixWord ++ tailWord_3044988) baseStart_3044988 baseEnd_3044988 := by
    simpa [prefixWord, tailWord_3044988, baseEnd_3044988] using wordTrace_append hprefix tailTrace_3044988
  have hstable : (prefixWord ++ tailWord_3044988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044988).length < 2 ^ (prefixWord ++ tailWord_3044988).sum := by decide
  have hdescent : baseEnd_3044988 < baseStart_3044988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044989 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_3044989 : Nat := 118140960795 + 3044989 * 2 ^ 59
def prefixEnd_3044989 : Nat := 4983230072969 + 3 ^ 40 * 3044989 * 2
def baseEnd_3044989 : Nat := 521180981551164066744619

theorem tailTrace_3044989 : CollatzResearch.WordTrace tailWord_3044989 prefixEnd_3044989 521180981551164066744619 := by
  unfold tailWord_3044989
  simp only [CollatzResearch.WordTrace]
  refine ⟨111059872765532370563594021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74039915177021580375729347 111059872765532370563594021)
  ·
    refine ⟨20823726143537319480673879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111059872765532370563594021 20823726143537319480673879)
    ·
      refine ⟨31235589215305979221010819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20823726143537319480673879 31235589215305979221010819)
      ·
        refine ⟨46853383822958968831516229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31235589215305979221010819 46853383822958968831516229)
        ·
          refine ⟨8785009466804806655909293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46853383822958968831516229 8785009466804806655909293)
          ·
            refine ⟨3294378550051802495965985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8785009466804806655909293 3294378550051802495965985)
            ·
              refine ⟨2470783912538851871974489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294378550051802495965985 2470783912538851871974489)
              ·
                refine ⟨1853087934404138903980867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2470783912538851871974489 1853087934404138903980867)
                ·
                  refine ⟨2779631901606208355971301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853087934404138903980867 2779631901606208355971301)
                  ·
                    refine ⟨521180981551164066744619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2779631901606208355971301 521180981551164066744619)
                    ·
                      rfl

theorem cell23_3044989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_3044989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044989 prefixEnd_3044989 := by exact prefixLift 3044989
  have htrace : WordTrace (prefixWord ++ tailWord_3044989) baseStart_3044989 baseEnd_3044989 := by
    simpa [prefixWord, tailWord_3044989, baseEnd_3044989] using wordTrace_append hprefix tailTrace_3044989
  have hstable : (prefixWord ++ tailWord_3044989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044989).length < 2 ^ (prefixWord ++ tailWord_3044989).sum := by decide
  have hdescent : baseEnd_3044989 < baseStart_3044989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045022 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_3045022 : Nat := 118140960795 + 3045022 * 2 ^ 59
def prefixEnd_3045022 : Nat := 4983230072969 + 3 ^ 40 * 3045022 * 2
def baseEnd_3045022 : Nat := 1563559889515090571121205

theorem tailTrace_3045022 : CollatzResearch.WordTrace tailWord_3045022 prefixEnd_3045022 1563559889515090571121205 := by
  unfold tailWord_3045022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882634546801602149943165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74040717582941878133030213 13882634546801602149943165)
  ·
    refine ⟨5205987955050600806228687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13882634546801602149943165 5205987955050600806228687)
    ·
      refine ⟨7808981932575901209343031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205987955050600806228687 7808981932575901209343031)
      ·
        refine ⟨11713472898863851814014547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7808981932575901209343031 11713472898863851814014547)
        ·
          refine ⟨17570209348295777721021821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713472898863851814014547 17570209348295777721021821)
          ·
            refine ⟨6588828505610916645383183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17570209348295777721021821 6588828505610916645383183)
            ·
              refine ⟨9883242758416374968074775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588828505610916645383183 9883242758416374968074775)
              ·
                refine ⟨14824864137624562452112163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9883242758416374968074775 14824864137624562452112163)
                ·
                  refine ⟨22237296206436843678168245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14824864137624562452112163 22237296206436843678168245)
                  ·
                    refine ⟨2084746519353454094828273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22237296206436843678168245 2084746519353454094828273)
                    ·
                      refine ⟨1563559889515090571121205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084746519353454094828273 1563559889515090571121205)
                      ·
                        rfl

theorem cell23_3045022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_3045022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045022 prefixEnd_3045022 := by exact prefixLift 3045022
  have htrace : WordTrace (prefixWord ++ tailWord_3045022) baseStart_3045022 baseEnd_3045022 := by
    simpa [prefixWord, tailWord_3045022, baseEnd_3045022] using wordTrace_append hprefix tailTrace_3045022
  have hstable : (prefixWord ++ tailWord_3045022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045022).length < 2 ^ (prefixWord ++ tailWord_3045022).sum := by decide
  have hdescent : baseEnd_3045022 < baseStart_3045022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045028 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_3045028 : Nat := 118140960795 + 3045028 * 2 ^ 59
def prefixEnd_3045028 : Nat := 4983230072969 + 3 ^ 40 * 3045028 * 2
def baseEnd_3045028 : Nat := 521187656799672515882059

theorem tailTrace_3045028 : CollatzResearch.WordTrace tailWord_3045028 prefixEnd_3045028 521187656799672515882059 := by
  unfold tailWord_3045028
  simp only [CollatzResearch.WordTrace]
  refine ⟨55530647606195540112131869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74040863474927386816175825 55530647606195540112131869)
  ·
    refine ⟨20823992852323327542049451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55530647606195540112131869 20823992852323327542049451)
    ·
      refine ⟨31235989278484991313074177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20823992852323327542049451 31235989278484991313074177)
      ·
        refine ⟨23426991958863743484805633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31235989278484991313074177 23426991958863743484805633)
        ·
          refine ⟨17570243969147807613604225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23426991958863743484805633 17570243969147807613604225)
          ·
            refine ⟨13177682976860855710203169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17570243969147807613604225 13177682976860855710203169)
            ·
              refine ⟨9883262232645641782652377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13177682976860855710203169 9883262232645641782652377)
              ·
                refine ⟨7412446674484231336989283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9883262232645641782652377 7412446674484231336989283)
                ·
                  refine ⟨11118670011726347005483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7412446674484231336989283 11118670011726347005483925)
                  ·
                    refine ⟨521187656799672515882059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11118670011726347005483925 521187656799672515882059)
                    ·
                      rfl

theorem cell23_3045028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_3045028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045028 prefixEnd_3045028 := by exact prefixLift 3045028
  have htrace : WordTrace (prefixWord ++ tailWord_3045028) baseStart_3045028 baseEnd_3045028 := by
    simpa [prefixWord, tailWord_3045028, baseEnd_3045028] using wordTrace_append hprefix tailTrace_3045028
  have hstable : (prefixWord ++ tailWord_3045028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045028).length < 2 ^ (prefixWord ++ tailWord_3045028).sum := by decide
  have hdescent : baseEnd_3045028 < baseStart_3045028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045046 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3045046 : Nat := 118140960795 + 3045046 * 2 ^ 59
def prefixEnd_3045046 : Nat := 4983230072969 + 3 ^ 40 * 3045046 * 2
def baseEnd_3045046 : Nat := 1563572213050798477221095

theorem tailTrace_3045046 : CollatzResearch.WordTrace tailWord_3045046 prefixEnd_3045046 1563572213050798477221095 := by
  unfold tailWord_3045046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941371982895366831151187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74041301150883912865612661 6941371982895366831151187)
  ·
    refine ⟨10412057974343050246726781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6941371982895366831151187 10412057974343050246726781)
    ·
      refine ⟨3904521740378643842522543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10412057974343050246726781 3904521740378643842522543)
      ·
        refine ⟨5856782610567965763783815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904521740378643842522543 5856782610567965763783815)
        ·
          refine ⟨8785173915851948645675723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856782610567965763783815 8785173915851948645675723)
          ·
            refine ⟨13177760873777922968513585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8785173915851948645675723 13177760873777922968513585)
            ·
              refine ⟨9883320655333442226385189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13177760873777922968513585 9883320655333442226385189)
              ·
                refine ⟨1853122622875020417447223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9883320655333442226385189 1853122622875020417447223)
                ·
                  refine ⟨2779683934312530626170835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853122622875020417447223 2779683934312530626170835)
                  ·
                    refine ⟨4169525901468795939256253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779683934312530626170835 4169525901468795939256253)
                    ·
                      refine ⟨1563572213050798477221095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169525901468795939256253 1563572213050798477221095)
                      ·
                        rfl

theorem cell23_3045046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3045046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045046 prefixEnd_3045046 := by exact prefixLift 3045046
  have htrace : WordTrace (prefixWord ++ tailWord_3045046) baseStart_3045046 baseEnd_3045046 := by
    simpa [prefixWord, tailWord_3045046, baseEnd_3045046] using wordTrace_append hprefix tailTrace_3045046
  have hstable : (prefixWord ++ tailWord_3045046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045046).length < 2 ^ (prefixWord ++ tailWord_3045046).sum := by decide
  have hdescent : baseEnd_3045046 < baseStart_3045046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045052 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_3045052 : Nat := 118140960795 + 3045052 * 2 ^ 59
def prefixEnd_3045052 : Nat := 4983230072969 + 3 ^ 40 * 3045052 * 2
def baseEnd_3045052 : Nat := 1563575293934725453746067

theorem tailTrace_3045052 : CollatzResearch.WordTrace tailWord_3045052 prefixEnd_3045052 1563575293934725453746067 := by
  unfold tailWord_3045052
  simp only [CollatzResearch.WordTrace]
  refine ⟨55531085282152066161568705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74041447042869421548758273 55531085282152066161568705)
  ·
    refine ⟨41648313961614049621176529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55531085282152066161568705 41648313961614049621176529)
    ·
      refine ⟨31236235471210537215882397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41648313961614049621176529 31236235471210537215882397)
      ·
        refine ⟨11713588301703951455955899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31236235471210537215882397 11713588301703951455955899)
        ·
          refine ⟨17570382452555927183933849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713588301703951455955899 17570382452555927183933849)
          ·
            refine ⟨13177786839416945387950387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17570382452555927183933849 13177786839416945387950387)
            ·
              refine ⟨19766680259125418081925581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177786839416945387950387 19766680259125418081925581)
              ·
                refine ⟨7412505097172031780722093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19766680259125418081925581 7412505097172031780722093)
                ·
                  refine ⟨2779689411439511917770785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7412505097172031780722093 2779689411439511917770785)
                  ·
                    refine ⟨2084767058579633938328089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2779689411439511917770785 2084767058579633938328089)
                    ·
                      refine ⟨1563575293934725453746067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084767058579633938328089 1563575293934725453746067)
                      ·
                        rfl

theorem cell23_3045052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_3045052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045052 prefixEnd_3045052 := by exact prefixLift 3045052
  have htrace : WordTrace (prefixWord ++ tailWord_3045052) baseStart_3045052 baseEnd_3045052 := by
    simpa [prefixWord, tailWord_3045052, baseEnd_3045052] using wordTrace_append hprefix tailTrace_3045052
  have hstable : (prefixWord ++ tailWord_3045052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045052).length < 2 ^ (prefixWord ++ tailWord_3045052).sum := by decide
  have hdescent : baseEnd_3045052 < baseStart_3045052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045061 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_3045061 : Nat := 118140960795 + 3045061 * 2 ^ 59
def prefixEnd_3045061 : Nat := 4983230072969 + 3 ^ 40 * 3045061 * 2
def baseEnd_3045061 : Nat := 1563579915260615918533525

theorem tailTrace_3045061 : CollatzResearch.WordTrace tailWord_3045061 prefixEnd_3045061 1563579915260615918533525 := by
  unfold tailWord_3045061
  simp only [CollatzResearch.WordTrace]
  refine ⟨111062498821271526860215037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74041665880847684573476691 111062498821271526860215037)
  ·
    refine ⟨41648437057976822572580639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111062498821271526860215037 41648437057976822572580639)
    ·
      refine ⟨62472655586965233858870959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41648437057976822572580639 62472655586965233858870959)
      ·
        refine ⟨93708983380447850788306439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62472655586965233858870959 93708983380447850788306439)
        ·
          refine ⟨140563475070671776182459659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93708983380447850788306439 140563475070671776182459659)
          ·
            refine ⟨210845212606007664273689489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140563475070671776182459659 210845212606007664273689489)
            ·
              refine ⟨158133909454505748205267117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210845212606007664273689489 158133909454505748205267117)
              ·
                refine ⟨59300216045439655576975169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158133909454505748205267117 59300216045439655576975169)
                ·
                  refine ⟨44475162034079741682731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59300216045439655576975169 44475162034079741682731377)
                  ·
                    refine ⟨33356371525559806262048533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44475162034079741682731377 33356371525559806262048533)
                    ·
                      refine ⟨1563579915260615918533525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33356371525559806262048533 1563579915260615918533525)
                      ·
                        rfl

theorem cell23_3045061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_3045061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045061 prefixEnd_3045061 := by exact prefixLift 3045061
  have htrace : WordTrace (prefixWord ++ tailWord_3045061) baseStart_3045061 baseEnd_3045061 := by
    simpa [prefixWord, tailWord_3045061, baseEnd_3045061] using wordTrace_append hprefix tailTrace_3045061
  have hstable : (prefixWord ++ tailWord_3045061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045061).length < 2 ^ (prefixWord ++ tailWord_3045061).sum := by decide
  have hdescent : baseEnd_3045061 < baseStart_3045061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045069 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3045069 : Nat := 118140960795 + 3045069 * 2 ^ 59
def prefixEnd_3045069 : Nat := 4983230072969 + 3 ^ 40 * 3045069 * 2
def baseEnd_3045069 : Nat := 1563584023105851887233489

theorem tailTrace_3045069 : CollatzResearch.WordTrace tailWord_3045069 prefixEnd_3045069 1563584023105851887233489 := by
  unfold tailWord_3045069
  simp only [CollatzResearch.WordTrace]
  refine ⟨111062790605242544226506261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74041860403495029484337507 111062790605242544226506261)
  ·
    refine ⟨5206068309620744260617481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111062790605242544226506261 5206068309620744260617481)
    ·
      refine ⟨3904551232215558195463111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5206068309620744260617481 3904551232215558195463111)
      ·
        refine ⟨5856826848323337293194667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904551232215558195463111 5856826848323337293194667)
        ·
          refine ⟨8785240272485005939792001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856826848323337293194667 8785240272485005939792001)
          ·
            refine ⟨6588930204363754454844001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8785240272485005939792001 6588930204363754454844001)
            ·
              refine ⟨4941697653272815841133001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6588930204363754454844001 4941697653272815841133001)
              ·
                refine ⟨3706273239954611880849751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941697653272815841133001 3706273239954611880849751)
                ·
                  refine ⟨5559409859931917821274627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706273239954611880849751 5559409859931917821274627)
                  ·
                    refine ⟨8339114789897876731911941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559409859931917821274627 8339114789897876731911941)
                    ·
                      refine ⟨1563584023105851887233489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8339114789897876731911941 1563584023105851887233489)
                      ·
                        rfl

theorem cell23_3045069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3045069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045069 prefixEnd_3045069 := by exact prefixLift 3045069
  have htrace : WordTrace (prefixWord ++ tailWord_3045069) baseStart_3045069 baseEnd_3045069 := by
    simpa [prefixWord, tailWord_3045069, baseEnd_3045069] using wordTrace_append hprefix tailTrace_3045069
  have hstable : (prefixWord ++ tailWord_3045069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045069).length < 2 ^ (prefixWord ++ tailWord_3045069).sum := by decide
  have hdescent : baseEnd_3045069 < baseStart_3045069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045071 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 7]
def baseStart_3045071 : Nat := 118140960795 + 3045071 * 2 ^ 59
def prefixEnd_3045071 : Nat := 4983230072969 + 3 ^ 40 * 3045071 * 2
def baseEnd_3045071 : Nat := 521195016689053626469493

theorem tailTrace_3045071 : CollatzResearch.WordTrace tailWord_3045071 prefixEnd_3045071 521195016689053626469493 := by
  unfold tailWord_3045071
  simp only [CollatzResearch.WordTrace]
  refine ⟨111062863551235298568079067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74041909034156865712052711 111062863551235298568079067)
  ·
    refine ⟨166594295326852947852118601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111062863551235298568079067 166594295326852947852118601)
    ·
      refine ⟨124945721495139710889088951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166594295326852947852118601 124945721495139710889088951)
      ·
        refine ⟨187418582242709566333633427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124945721495139710889088951 187418582242709566333633427)
        ·
          refine ⟨281127873364064349500450141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187418582242709566333633427 281127873364064349500450141)
          ·
            refine ⟨105422952511524131062668803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281127873364064349500450141 105422952511524131062668803)
            ·
              refine ⟨158134428767286196594003205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105422952511524131062668803 158134428767286196594003205)
              ·
                refine ⟨29650205393866161861375601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158134428767286196594003205 29650205393866161861375601)
                ·
                  refine ⟨22237654045399621396031701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29650205393866161861375601 22237654045399621396031701)
                  ·
                    refine ⟨521195016689053626469493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22237654045399621396031701 521195016689053626469493)
                    ·
                      rfl

theorem cell23_3045071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_3045071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045071 prefixEnd_3045071 := by exact prefixLift 3045071
  have htrace : WordTrace (prefixWord ++ tailWord_3045071) baseStart_3045071 baseEnd_3045071 := by
    simpa [prefixWord, tailWord_3045071, baseEnd_3045071] using wordTrace_append hprefix tailTrace_3045071
  have hstable : (prefixWord ++ tailWord_3045071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045071).length < 2 ^ (prefixWord ++ tailWord_3045071).sum := by decide
  have hdescent : baseEnd_3045071 < baseStart_3045071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045102 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3045102 : Nat := 118140960795 + 3045102 * 2 ^ 59
def prefixEnd_3045102 : Nat := 4983230072969 + 3 ^ 40 * 3045102 * 2
def baseEnd_3045102 : Nat := 1563600967967450258120837

theorem tailTrace_3045102 : CollatzResearch.WordTrace tailWord_3045102 prefixEnd_3045102 1563600967967450258120837 := by
  unfold tailWord_3045102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882999276765373857807195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74042662809415327241638373 13882999276765373857807195)
  ·
    refine ⟨20824498915148060786710793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13882999276765373857807195 20824498915148060786710793)
    ·
      refine ⟨15618374186361045590033095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20824498915148060786710793 15618374186361045590033095)
      ·
        refine ⟨23427561279541568385049643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618374186361045590033095 23427561279541568385049643)
        ·
          refine ⟨35141341919312352577574465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23427561279541568385049643 35141341919312352577574465)
          ·
            refine ⟨26356006439484264433180849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35141341919312352577574465 26356006439484264433180849)
            ·
              refine ⟨19767004829613198324885637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26356006439484264433180849 19767004829613198324885637)
              ·
                refine ⟨3706313405552474685916057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19767004829613198324885637 3706313405552474685916057)
                ·
                  refine ⟨2779735054164356014437043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3706313405552474685916057 2779735054164356014437043)
                  ·
                    refine ⟨4169602581246534021655565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779735054164356014437043 4169602581246534021655565)
                    ·
                      refine ⟨1563600967967450258120837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169602581246534021655565 1563600967967450258120837)
                      ·
                        rfl

theorem cell23_3045102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3045102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045102 prefixEnd_3045102 := by exact prefixLift 3045102
  have htrace : WordTrace (prefixWord ++ tailWord_3045102) baseStart_3045102 baseEnd_3045102 := by
    simpa [prefixWord, tailWord_3045102, baseEnd_3045102] using wordTrace_append hprefix tailTrace_3045102
  have hstable : (prefixWord ++ tailWord_3045102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045102).length < 2 ^ (prefixWord ++ tailWord_3045102).sum := by decide
  have hdescent : baseEnd_3045102 < baseStart_3045102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045128 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3045128 : Nat := 118140960795 + 3045128 * 2 ^ 59
def prefixEnd_3045128 : Nat := 4983230072969 + 3 ^ 40 * 3045128 * 2
def baseEnd_3045128 : Nat := 1563614318464467156395717

theorem tailTrace_3045128 : CollatzResearch.WordTrace tailWord_3045128 prefixEnd_3045128 1563614318464467156395717 := by
  unfold tailWord_3045128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55532471256014398651452019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74043295008019198201936025 55532471256014398651452019)
  ·
    refine ⟨83298706884021597977178029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55532471256014398651452019 83298706884021597977178029)
    ·
      refine ⟨31237015081508099241441761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83298706884021597977178029 31237015081508099241441761)
      ·
        refine ⟨23427761311131074431081321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31237015081508099241441761 23427761311131074431081321)
        ·
          refine ⟨17570820983348305823310991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23427761311131074431081321 17570820983348305823310991)
          ·
            refine ⟨26356231475022458734966487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17570820983348305823310991 26356231475022458734966487)
            ·
              refine ⟨39534347212533688102449731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26356231475022458734966487 39534347212533688102449731)
              ·
                refine ⟨59301520818800532153674597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39534347212533688102449731 59301520818800532153674597)
                ·
                  refine ⟨11119035153525099778813987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59301520818800532153674597 11119035153525099778813987)
                  ·
                    refine ⟨16678552730287649668220981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11119035153525099778813987 16678552730287649668220981)
                    ·
                      refine ⟨1563614318464467156395717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16678552730287649668220981 1563614318464467156395717)
                      ·
                        rfl

theorem cell23_3045128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3045128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045128 prefixEnd_3045128 := by exact prefixLift 3045128
  have htrace : WordTrace (prefixWord ++ tailWord_3045128) baseStart_3045128 baseEnd_3045128 := by
    simpa [prefixWord, tailWord_3045128, baseEnd_3045128] using wordTrace_append hprefix tailTrace_3045128
  have hstable : (prefixWord ++ tailWord_3045128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045128).length < 2 ^ (prefixWord ++ tailWord_3045128).sum := by decide
  have hdescent : baseEnd_3045128 < baseStart_3045128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045172 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3045172 : Nat := 118140960795 + 3045172 * 2 ^ 59
def prefixEnd_3045172 : Nat := 4983230072969 + 3 ^ 40 * 3045172 * 2
def baseEnd_3045172 : Nat := 1563636911613264984245515

theorem tailTrace_3045172 : CollatzResearch.WordTrace tailWord_3045172 prefixEnd_3045172 1563636911613264984245515 := by
  unfold tailWord_3045172
  simp only [CollatzResearch.WordTrace]
  refine ⟨55533273661934696408752885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74044364882579595211670513 55533273661934696408752885)
  ·
    refine ⟨5206244405806377788320583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55533273661934696408752885 5206244405806377788320583)
    ·
      refine ⟨7809366608709566682480875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206244405806377788320583 7809366608709566682480875)
      ·
        refine ⟨11714049913064350023721313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7809366608709566682480875 11714049913064350023721313)
        ·
          refine ⟨8785537434798262517790985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714049913064350023721313 8785537434798262517790985)
          ·
            refine ⟨6589153076098696888343239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8785537434798262517790985 6589153076098696888343239)
            ·
              refine ⟨9883729614148045332514859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589153076098696888343239 9883729614148045332514859)
              ·
                refine ⟨14825594421222067998772289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9883729614148045332514859 14825594421222067998772289)
                ·
                  refine ⟨11119195815916550999079217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14825594421222067998772289 11119195815916550999079217)
                  ·
                    refine ⟨8339396861937413249309413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11119195815916550999079217 8339396861937413249309413)
                    ·
                      refine ⟨1563636911613264984245515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8339396861937413249309413 1563636911613264984245515)
                      ·
                        rfl

theorem cell23_3045172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3045172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045172 prefixEnd_3045172 := by exact prefixLift 3045172
  have htrace : WordTrace (prefixWord ++ tailWord_3045172) baseStart_3045172 baseEnd_3045172 := by
    simpa [prefixWord, tailWord_3045172, baseEnd_3045172] using wordTrace_append hprefix tailTrace_3045172
  have hstable : (prefixWord ++ tailWord_3045172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045172).length < 2 ^ (prefixWord ++ tailWord_3045172).sum := by decide
  have hdescent : baseEnd_3045172 < baseStart_3045172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045309 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_3045309 : Nat := 118140960795 + 3045309 * 2 ^ 59
def prefixEnd_3045309 : Nat := 4983230072969 + 3 ^ 40 * 3045309 * 2
def baseEnd_3045309 : Nat := 1563707258462930948232385

theorem tailTrace_3045309 : CollatzResearch.WordTrace tailWord_3045309 prefixEnd_3045309 1563707258462930948232385 := by
  unfold tailWord_3045309
  simp only [CollatzResearch.WordTrace]
  refine ⟨111071544124373065215242981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74047696082915376810161987 111071544124373065215242981)
  ·
    refine ⟨20825914523319949727858059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111071544124373065215242981 20825914523319949727858059)
    ·
      refine ⟨31238871784979924591787089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20825914523319949727858059 31238871784979924591787089)
      ·
        refine ⟨23429153838734943443840317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31238871784979924591787089 23429153838734943443840317)
        ·
          refine ⟨8785932689525603791440119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23429153838734943443840317 8785932689525603791440119)
          ·
            refine ⟨13178899034288405687160179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8785932689525603791440119 13178899034288405687160179)
            ·
              refine ⟨19768348551432608530740269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13178899034288405687160179 19768348551432608530740269)
              ·
                refine ⟨7413130706787228199027601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19768348551432608530740269 7413130706787228199027601)
                ·
                  refine ⟨5559848030090421149270701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413130706787228199027601 5559848030090421149270701)
                  ·
                    refine ⟨2084943011283907930976513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5559848030090421149270701 2084943011283907930976513)
                    ·
                      refine ⟨1563707258462930948232385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2084943011283907930976513 1563707258462930948232385)
                      ·
                        rfl

theorem cell23_3045309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_3045309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045309 prefixEnd_3045309 := by exact prefixLift 3045309
  have htrace : WordTrace (prefixWord ++ tailWord_3045309) baseStart_3045309 baseEnd_3045309 := by
    simpa [prefixWord, tailWord_3045309, baseEnd_3045309] using wordTrace_append hprefix tailTrace_3045309
  have hstable : (prefixWord ++ tailWord_3045309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045309).length < 2 ^ (prefixWord ++ tailWord_3045309).sum := by decide
  have hdescent : baseEnd_3045309 < baseStart_3045309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045322 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_3045322 : Nat := 118140960795 + 3045322 * 2 ^ 59
def prefixEnd_3045322 : Nat := 4983230072969 + 3 ^ 40 * 3045322 * 2
def baseEnd_3045322 : Nat := 1563713933711439397369825

theorem tailTrace_3045322 : CollatzResearch.WordTrace tailWord_3045322 prefixEnd_3045322 1563713933711439397369825 := by
  unfold tailWord_3045322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27768004568331492108866555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74048012182217312290310813 27768004568331492108866555)
  ·
    refine ⟨41652006852497238163299833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27768004568331492108866555 41652006852497238163299833)
    ·
      refine ⟨31239005139372928622474875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41652006852497238163299833 31239005139372928622474875)
      ·
        refine ⟨46858507709059392933712313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31239005139372928622474875 46858507709059392933712313)
        ·
          refine ⟨35143880781794544700284235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46858507709059392933712313 35143880781794544700284235)
          ·
            refine ⟨52715821172691817050426353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35143880781794544700284235 52715821172691817050426353)
            ·
              refine ⟨39536865879518862787819765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52715821172691817050426353 39536865879518862787819765)
              ·
                refine ⟨3706581176204893386358103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39536865879518862787819765 3706581176204893386358103)
                ·
                  refine ⟨5559871764307340079537155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706581176204893386358103 5559871764307340079537155)
                  ·
                    refine ⟨8339807646461010119305733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559871764307340079537155 8339807646461010119305733)
                    ·
                      refine ⟨1563713933711439397369825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8339807646461010119305733 1563713933711439397369825)
                      ·
                        rfl

theorem cell23_3045322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_3045322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045322 prefixEnd_3045322 := by exact prefixLift 3045322
  have htrace : WordTrace (prefixWord ++ tailWord_3045322) baseStart_3045322 baseEnd_3045322 := by
    simpa [prefixWord, tailWord_3045322, baseEnd_3045322] using wordTrace_append hprefix tailTrace_3045322
  have hstable : (prefixWord ++ tailWord_3045322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045322).length < 2 ^ (prefixWord ++ tailWord_3045322).sum := by decide
  have hdescent : baseEnd_3045322 < baseStart_3045322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045333 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3045333 : Nat := 118140960795 + 3045333 * 2 ^ 59
def prefixEnd_3045333 : Nat := 4983230072969 + 3 ^ 40 * 3045333 * 2
def baseEnd_3045333 : Nat := 1563719581998638854332275

theorem tailTrace_3045333 : CollatzResearch.WordTrace tailWord_3045333 prefixEnd_3045333 1563719581998638854332275 := by
  unfold tailWord_3045333
  simp only [CollatzResearch.WordTrace]
  refine ⟨111072419476286117314116653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74048279650857411542744435 111072419476286117314116653)
  ·
    refine ⟨41652157303607293992793745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111072419476286117314116653 41652157303607293992793745)
    ·
      refine ⟨31239117977705470494595309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41652157303607293992793745 31239117977705470494595309)
      ·
        refine ⟨11714669241639551435473241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31239117977705470494595309 11714669241639551435473241)
        ·
          refine ⟨8786001931229663576604931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714669241639551435473241 8786001931229663576604931)
          ·
            refine ⟨13179002896844495364907397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786001931229663576604931 13179002896844495364907397)
            ·
              refine ⟨2471063043158342880920137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13179002896844495364907397 2471063043158342880920137)
              ·
                refine ⟨1853297282368757160690103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471063043158342880920137 1853297282368757160690103)
                ·
                  refine ⟨2779945923553135741035155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853297282368757160690103 2779945923553135741035155)
                  ·
                    refine ⟨4169918885329703611552733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779945923553135741035155 4169918885329703611552733)
                    ·
                      refine ⟨1563719581998638854332275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169918885329703611552733 1563719581998638854332275)
                      ·
                        rfl

theorem cell23_3045333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3045333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045333 prefixEnd_3045333 := by exact prefixLift 3045333
  have htrace : WordTrace (prefixWord ++ tailWord_3045333) baseStart_3045333 baseEnd_3045333 := by
    simpa [prefixWord, tailWord_3045333, baseEnd_3045333] using wordTrace_append hprefix tailTrace_3045333
  have hstable : (prefixWord ++ tailWord_3045333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045333).length < 2 ^ (prefixWord ++ tailWord_3045333).sum := by decide
  have hdescent : baseEnd_3045333 < baseStart_3045333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045335 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3045335 : Nat := 118140960795 + 3045335 * 2 ^ 59
def prefixEnd_3045335 : Nat := 4983230072969 + 3 ^ 40 * 3045335 * 2
def baseEnd_3045335 : Nat := 1563720608959947846507265

theorem tailTrace_3045335 : CollatzResearch.WordTrace tailWord_3045335 prefixEnd_3045335 1563720608959947846507265 := by
  unfold tailWord_3045335
  simp only [CollatzResearch.WordTrace]
  refine ⟨111072492422278871655689459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74048328281519247770459639 111072492422278871655689459)
  ·
    refine ⟨166608738633418307483534189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111072492422278871655689459 166608738633418307483534189)
    ·
      refine ⟨62478276987531865306325321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166608738633418307483534189 62478276987531865306325321)
      ·
        refine ⟨46858707740648898979743991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62478276987531865306325321 46858707740648898979743991)
        ·
          refine ⟨70288061610973348469615987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46858707740648898979743991 70288061610973348469615987)
          ·
            refine ⟨105432092416460022704423981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70288061610973348469615987 105432092416460022704423981)
            ·
              refine ⟨39537034656172508514158993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105432092416460022704423981 39537034656172508514158993)
              ·
                refine ⟨29652775992129381385619245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39537034656172508514158993 29652775992129381385619245)
                ·
                  refine ⟨11119790997048518019607217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29652775992129381385619245 11119790997048518019607217)
                  ·
                    refine ⟨8339843247786388514705413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11119790997048518019607217 8339843247786388514705413)
                    ·
                      refine ⟨1563720608959947846507265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8339843247786388514705413 1563720608959947846507265)
                      ·
                        rfl

theorem cell23_3045335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3045335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045335 prefixEnd_3045335 := by exact prefixLift 3045335
  have htrace : WordTrace (prefixWord ++ tailWord_3045335) baseStart_3045335 baseEnd_3045335 := by
    simpa [prefixWord, tailWord_3045335, baseEnd_3045335] using wordTrace_append hprefix tailTrace_3045335
  have hstable : (prefixWord ++ tailWord_3045335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045335).length < 2 ^ (prefixWord ++ tailWord_3045335).sum := by decide
  have hdescent : baseEnd_3045335 < baseStart_3045335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045345 : List Nat := [1, 2, 3, 1, 2, 1, 5, 8]
def baseStart_3045345 : Nat := 118140960795 + 3045345 * 2 ^ 59
def prefixEnd_3045345 : Nat := 4983230072969 + 3 ^ 40 * 3045345 * 2
def baseEnd_3045345 : Nat := 57915768287647881754897

theorem tailTrace_3045345 : CollatzResearch.WordTrace tailWord_3045345 prefixEnd_3045345 57915768287647881754897 := by
  unfold tailWord_3045345
  simp only [CollatzResearch.WordTrace]
  refine ⟨111072857152242643363553489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74048571434828428909035659 111072857152242643363553489)
  ·
    refine ⟨83304642864181982522665117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111072857152242643363553489 83304642864181982522665117)
    ·
      refine ⟨31239241074068243445999419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83304642864181982522665117 31239241074068243445999419)
      ·
        refine ⟨46858861611102365168999129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31239241074068243445999419 46858861611102365168999129)
        ·
          refine ⟨35144146208326773876749347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46858861611102365168999129 35144146208326773876749347)
          ·
            refine ⟨52716219312490160815124021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35144146208326773876749347 52716219312490160815124021)
            ·
              refine ⟨4942145560545952576417877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52716219312490160815124021 4942145560545952576417877)
              ·
                refine ⟨57915768287647881754897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4942145560545952576417877 57915768287647881754897)
                ·
                  rfl

theorem cell23_3045345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 8].length) (baseStart_3045345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045345 prefixEnd_3045345 := by exact prefixLift 3045345
  have htrace : WordTrace (prefixWord ++ tailWord_3045345) baseStart_3045345 baseEnd_3045345 := by
    simpa [prefixWord, tailWord_3045345, baseEnd_3045345] using wordTrace_append hprefix tailTrace_3045345
  have hstable : (prefixWord ++ tailWord_3045345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045345).length < 2 ^ (prefixWord ++ tailWord_3045345).sum := by decide
  have hdescent : baseEnd_3045345 < baseStart_3045345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045372 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_3045372 : Nat := 118140960795 + 3045372 * 2 ^ 59
def prefixEnd_3045372 : Nat := 4983230072969 + 3 ^ 40 * 3045372 * 2
def baseEnd_3045372 : Nat := 1563739607744164201744595

theorem tailTrace_3045372 : CollatzResearch.WordTrace tailWord_3045372 prefixEnd_3045372 1563739607744164201744595 := by
  unfold tailWord_3045372
  simp only [CollatzResearch.WordTrace]
  refine ⟨55536920961572413487393185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74049227948763217983190913 55536920961572413487393185)
  ·
    refine ⟨41652690721179310115544889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55536920961572413487393185 41652690721179310115544889)
    ·
      refine ⟨31239518040884482586658667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41652690721179310115544889 31239518040884482586658667)
      ·
        refine ⟨46859277061326723879988001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31239518040884482586658667 46859277061326723879988001)
        ·
          refine ⟨35144457795995042909991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46859277061326723879988001 35144457795995042909991001)
          ·
            refine ⟨26358343346996282182493251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35144457795995042909991001 26358343346996282182493251)
            ·
              refine ⟨39537515020494423273739877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26358343346996282182493251 39537515020494423273739877)
              ·
                refine ⟨7413284066342704363826227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39537515020494423273739877 7413284066342704363826227)
                ·
                  refine ⟨11119926099514056545739341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7413284066342704363826227 11119926099514056545739341)
                  ·
                    refine ⟨4169972287317771204652253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11119926099514056545739341 4169972287317771204652253)
                    ·
                      refine ⟨1563739607744164201744595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4169972287317771204652253 1563739607744164201744595)
                      ·
                        rfl

theorem cell23_3045372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_3045372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045372 prefixEnd_3045372 := by exact prefixLift 3045372
  have htrace : WordTrace (prefixWord ++ tailWord_3045372) baseStart_3045372 baseEnd_3045372 := by
    simpa [prefixWord, tailWord_3045372, baseEnd_3045372] using wordTrace_append hprefix tailTrace_3045372
  have hstable : (prefixWord ++ tailWord_3045372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045372).length < 2 ^ (prefixWord ++ tailWord_3045372).sum := by decide
  have hdescent : baseEnd_3045372 < baseStart_3045372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045395 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_3045395 : Nat := 118140960795 + 3045395 * 2 ^ 59
def prefixEnd_3045395 : Nat := 4983230072969 + 3 ^ 40 * 3045395 * 2
def baseEnd_3045395 : Nat := 1563751417799217611756989

theorem tailTrace_3045395 : CollatzResearch.WordTrace tailWord_3045395 prefixEnd_3045395 1563751417799217611756989 := by
  unfold tailWord_3045395
  simp only [CollatzResearch.WordTrace]
  refine ⟨111074680802061501902873639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74049787201374334601915759 111074680802061501902873639)
  ·
    refine ⟨166612021203092252854310459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111074680802061501902873639 166612021203092252854310459)
    ·
      refine ⟨249918031804638379281465689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166612021203092252854310459 249918031804638379281465689)
      ·
        refine ⟨187438523853478784461099267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249918031804638379281465689 187438523853478784461099267)
        ·
          refine ⟨281157785780218176691648901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187438523853478784461099267 281157785780218176691648901)
          ·
            refine ⟨52717084833790908129684169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281157785780218176691648901 52717084833790908129684169)
            ·
              refine ⟨39537813625343181097263127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52717084833790908129684169 39537813625343181097263127)
              ·
                refine ⟨59306720438014771645894691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39537813625343181097263127 59306720438014771645894691)
                ·
                  refine ⟨88960080657022157468842037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59306720438014771645894691 88960080657022157468842037)
                  ·
                    refine ⟨8340007561595827262703941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88960080657022157468842037 8340007561595827262703941)
                    ·
                      refine ⟨1563751417799217611756989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8340007561595827262703941 1563751417799217611756989)
                      ·
                        rfl

theorem cell23_3045395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_3045395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3045395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3045395 prefixEnd_3045395 := by exact prefixLift 3045395
  have htrace : WordTrace (prefixWord ++ tailWord_3045395) baseStart_3045395 baseEnd_3045395 := by
    simpa [prefixWord, tailWord_3045395, baseEnd_3045395] using wordTrace_append hprefix tailTrace_3045395
  have hstable : (prefixWord ++ tailWord_3045395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045395).length < 2 ^ (prefixWord ++ tailWord_3045395).sum := by decide
  have hdescent : baseEnd_3045395 < baseStart_3045395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
