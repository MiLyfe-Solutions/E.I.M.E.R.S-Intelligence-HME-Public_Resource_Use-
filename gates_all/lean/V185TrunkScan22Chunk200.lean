import V185TrunkScan22Chunk199

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1784143 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 4, 3]
def baseStart_1784143 : Nat := 118140960795 + 1784143 * 2 ^ 59
def prefixEnd_1784143 : Nat := 4983230072969 + 3 ^ 40 * 1784143 * 2
def baseEnd_1784143 : Nat := 610748610236478844004921

theorem tailTrace_1784143 : CollatzResearch.WordTrace tailWord_1784143 prefixEnd_1784143 610748610236478844004921 := by
  unfold tailWord_1784143
  simp only [CollatzResearch.WordTrace]
  refine ⟨65073041175362093210517083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43382027450241395473678055 65073041175362093210517083)
  ·
    refine ⟨97609561763043139815775625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65073041175362093210517083 97609561763043139815775625)
    ·
      refine ⟨73207171322282354861831719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97609561763043139815775625 73207171322282354861831719)
      ·
        refine ⟨109810756983423532292747579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73207171322282354861831719 109810756983423532292747579)
        ·
          refine ⟨164716135475135298439121369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109810756983423532292747579 164716135475135298439121369)
          ·
            refine ⟨123537101606351473829341027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164716135475135298439121369 123537101606351473829341027)
            ·
              refine ⟨185305652409527210744011541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123537101606351473829341027 185305652409527210744011541)
              ·
                refine ⟨8686202456696588003625541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185305652409527210744011541 8686202456696588003625541)
                ·
                  refine ⟨1628662960630610250679789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8686202456696588003625541 1628662960630610250679789)
                  ·
                    refine ⟨610748610236478844004921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628662960630610250679789 610748610236478844004921)
                    ·
                      rfl

theorem cell22_1784143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_1784143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784143 prefixEnd_1784143 := by exact prefixLift 1784143
  have htrace : WordTrace (prefixWord ++ tailWord_1784143) baseStart_1784143 baseEnd_1784143 := by
    simpa [prefixWord, tailWord_1784143, baseEnd_1784143] using wordTrace_append hprefix tailTrace_1784143
  have hstable : (prefixWord ++ tailWord_1784143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784143).length < 2 ^ (prefixWord ++ tailWord_1784143).sum := by decide
  have hdescent : baseEnd_1784143 < baseStart_1784143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784162 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1784162 : Nat := 118140960795 + 1784162 * 2 ^ 59
def prefixEnd_1784162 : Nat := 4983230072969 + 3 ^ 40 * 1784162 * 2
def baseEnd_1784162 : Nat := 203585038108256375926621

theorem tailTrace_1784162 : CollatzResearch.WordTrace tailWord_1784162 prefixEnd_1784162 203585038108256375926621 := by
  unfold tailWord_1784162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16268433540573314863864685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43382489441528839636972493 16268433540573314863864685)
  ·
    refine ⟨6100662577714993073949257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16268433540573314863864685 6100662577714993073949257)
    ·
      refine ⟨4575496933286244805461943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6100662577714993073949257 4575496933286244805461943)
      ·
        refine ⟨6863245399929367208192915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575496933286244805461943 6863245399929367208192915)
        ·
          refine ⟨10294868099894050812289373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863245399929367208192915 10294868099894050812289373)
          ·
            refine ⟨3860575537460269054608515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10294868099894050812289373 3860575537460269054608515)
            ·
              refine ⟨5790863306190403581912773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860575537460269054608515 5790863306190403581912773)
              ·
                refine ⟨1085786869910700671608645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5790863306190403581912773 1085786869910700671608645)
                ·
                  refine ⟨203585038108256375926621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085786869910700671608645 203585038108256375926621)
                  ·
                    rfl

theorem cell22_1784162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1784162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784162 prefixEnd_1784162 := by exact prefixLift 1784162
  have htrace : WordTrace (prefixWord ++ tailWord_1784162) baseStart_1784162 baseEnd_1784162 := by
    simpa [prefixWord, tailWord_1784162, baseEnd_1784162] using wordTrace_append hprefix tailTrace_1784162
  have hstable : (prefixWord ++ tailWord_1784162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784162).length < 2 ^ (prefixWord ++ tailWord_1784162).sum := by decide
  have hdescent : baseEnd_1784162 < baseStart_1784162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784265 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_1784265 : Nat := 118140960795 + 1784265 * 2 ^ 59
def prefixEnd_1784265 : Nat := 4983230072969 + 3 ^ 40 * 1784265 * 2
def baseEnd_1784265 : Nat := 610790373329711192454547

theorem tailTrace_1784265 : CollatzResearch.WordTrace tailWord_1784265 prefixEnd_1784265 610790373329711192454547 := by
  unfold tailWord_1784265
  simp only [CollatzResearch.WordTrace]
  refine ⟨65077490880920108046458249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43384993920613405364305499 65077490880920108046458249)
  ·
    refine ⟨48808118160690081034843687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65077490880920108046458249 48808118160690081034843687)
    ·
      refine ⟨73212177241035121552265531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48808118160690081034843687 73212177241035121552265531)
      ·
        refine ⟨109818265861552682328398297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73212177241035121552265531 109818265861552682328398297)
        ·
          refine ⟨82363699396164511746298723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109818265861552682328398297 82363699396164511746298723)
          ·
            refine ⟨123545549094246767619448085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82363699396164511746298723 123545549094246767619448085)
            ·
              refine ⟨5791197613792817232161629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123545549094246767619448085 5791197613792817232161629)
              ·
                refine ⟨2171699105172306462060611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5791197613792817232161629 2171699105172306462060611)
                ·
                  refine ⟨3257548657758459693090917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171699105172306462060611 3257548657758459693090917)
                  ·
                    refine ⟨610790373329711192454547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257548657758459693090917 610790373329711192454547)
                    ·
                      rfl

theorem cell22_1784265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_1784265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784265 prefixEnd_1784265 := by exact prefixLift 1784265
  have htrace : WordTrace (prefixWord ++ tailWord_1784265) baseStart_1784265 baseEnd_1784265 := by
    simpa [prefixWord, tailWord_1784265, baseEnd_1784265] using wordTrace_append hprefix tailTrace_1784265
  have hstable : (prefixWord ++ tailWord_1784265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784265).length < 2 ^ (prefixWord ++ tailWord_1784265).sum := by decide
  have hdescent : baseEnd_1784265 < baseStart_1784265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784295 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1784295 : Nat := 118140960795 + 1784295 * 2 ^ 59
def prefixEnd_1784295 : Nat := 4983230072969 + 3 ^ 40 * 1784295 * 2
def baseEnd_1784295 : Nat := 610800642942801114204455

theorem tailTrace_1784295 : CollatzResearch.WordTrace tailWord_1784295 prefixEnd_1784295 610800642942801114204455 := by
  unfold tailWord_1784295
  simp only [CollatzResearch.WordTrace]
  refine ⟨65078585070811423170050339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43385723380540948780033559 65078585070811423170050339)
  ·
    refine ⟨97617877606217134755075509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65078585070811423170050339 97617877606217134755075509)
    ·
      refine ⟨9151676025582856383288329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97617877606217134755075509 9151676025582856383288329)
      ·
        refine ⟨6863757019187142287466247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9151676025582856383288329 6863757019187142287466247)
        ·
          refine ⟨10295635528780713431199371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863757019187142287466247 10295635528780713431199371)
          ·
            refine ⟨15443453293171070146799057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10295635528780713431199371 15443453293171070146799057)
            ·
              refine ⟨11582589969878302610099293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15443453293171070146799057 11582589969878302610099293)
              ·
                refine ⟨4343471238704363478787235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11582589969878302610099293 4343471238704363478787235)
                ·
                  refine ⟨6515206858056545218180853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343471238704363478787235 6515206858056545218180853)
                  ·
                    refine ⟨610800642942801114204455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6515206858056545218180853 610800642942801114204455)
                    ·
                      rfl

theorem cell22_1784295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1784295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784295 prefixEnd_1784295 := by exact prefixLift 1784295
  have htrace : WordTrace (prefixWord ++ tailWord_1784295) baseStart_1784295 baseEnd_1784295 := by
    simpa [prefixWord, tailWord_1784295, baseEnd_1784295] using wordTrace_append hprefix tailTrace_1784295
  have hstable : (prefixWord ++ tailWord_1784295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784295).length < 2 ^ (prefixWord ++ tailWord_1784295).sum := by decide
  have hdescent : baseEnd_1784295 < baseStart_1784295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784400 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_1784400 : Nat := 118140960795 + 1784400 * 2 ^ 59
def prefixEnd_1784400 : Nat := 4983230072969 + 3 ^ 40 * 1784400 * 2
def baseEnd_1784400 : Nat := 610836586588615840329133

theorem tailTrace_1784400 : CollatzResearch.WordTrace tailWord_1784400 prefixEnd_1784400 610836586588615840329133 := by
  unfold tailWord_1784400
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541207367715513051311327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43388276490287350735081769 32541207367715513051311327)
  ·
    refine ⟨48811811051573269576966991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32541207367715513051311327 48811811051573269576966991)
    ·
      refine ⟨73217716577359904365450487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48811811051573269576966991 73217716577359904365450487)
      ·
        refine ⟨109826574866039856548175731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73217716577359904365450487 109826574866039856548175731)
        ·
          refine ⟨164739862299059784822263597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109826574866039856548175731 164739862299059784822263597)
          ·
            refine ⟨61777448362147419308348849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164739862299059784822263597 61777448362147419308348849)
            ·
              refine ⟨46333086271610564481261637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61777448362147419308348849 46333086271610564481261637)
              ·
                refine ⟨8687453675926980840236557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46333086271610564481261637 8687453675926980840236557)
                ·
                  refine ⟨3257795128472617815088709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8687453675926980840236557 3257795128472617815088709)
                  ·
                    refine ⟨610836586588615840329133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257795128472617815088709 610836586588615840329133)
                    ·
                      rfl

theorem cell22_1784400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_1784400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784400 prefixEnd_1784400 := by exact prefixLift 1784400
  have htrace : WordTrace (prefixWord ++ tailWord_1784400) baseStart_1784400 baseEnd_1784400 := by
    simpa [prefixWord, tailWord_1784400, baseEnd_1784400] using wordTrace_append hprefix tailTrace_1784400
  have hstable : (prefixWord ++ tailWord_1784400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784400).length < 2 ^ (prefixWord ++ tailWord_1784400).sum := by decide
  have hdescent : baseEnd_1784400 < baseStart_1784400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784404 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1784404 : Nat := 118140960795 + 1784404 * 2 ^ 59
def prefixEnd_1784404 : Nat := 4983230072969 + 3 ^ 40 * 1784404 * 2
def baseEnd_1784404 : Nat := 203612651956787054409707

theorem tailTrace_1784404 : CollatzResearch.WordTrace tailWord_1784404 prefixEnd_1784404 203612651956787054409707 := by
  unfold tailWord_1784404
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541280313708267392884133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43388373751611023190512177 32541280313708267392884133)
  ·
    refine ⟨6101490058820300136165775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32541280313708267392884133 6101490058820300136165775)
    ·
      refine ⟨9152235088230450204248663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6101490058820300136165775 9152235088230450204248663)
      ·
        refine ⟨13728352632345675306372995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152235088230450204248663 13728352632345675306372995)
        ·
          refine ⟨20592528948518512959559493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13728352632345675306372995 20592528948518512959559493)
          ·
            refine ⟨3861099177847221179917405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20592528948518512959559493 3861099177847221179917405)
            ·
              refine ⟨1447912191692707942469027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3861099177847221179917405 1447912191692707942469027)
              ·
                refine ⟨2171868287539061913703541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447912191692707942469027 2171868287539061913703541)
                ·
                  refine ⟨203612651956787054409707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2171868287539061913703541 203612651956787054409707)
                  ·
                    rfl

theorem cell22_1784404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1784404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784404 prefixEnd_1784404 := by exact prefixLift 1784404
  have htrace : WordTrace (prefixWord ++ tailWord_1784404) baseStart_1784404 baseEnd_1784404 := by
    simpa [prefixWord, tailWord_1784404, baseEnd_1784404] using wordTrace_append hprefix tailTrace_1784404
  have hstable : (prefixWord ++ tailWord_1784404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784404).length < 2 ^ (prefixWord ++ tailWord_1784404).sum := by decide
  have hdescent : baseEnd_1784404 < baseStart_1784404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784417 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1784417 : Nat := 118140960795 + 1784417 * 2 ^ 59
def prefixEnd_1784417 : Nat := 4983230072969 + 3 ^ 40 * 1784417 * 2
def baseEnd_1784417 : Nat := 610842406036033462654081

theorem tailTrace_1784417 : CollatzResearch.WordTrace tailWord_1784417 prefixEnd_1784417 610842406036033462654081 := by
  unfold tailWord_1784417
  simp only [CollatzResearch.WordTrace]
  refine ⟨65083034776369438005991505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43388689850912958670661003 65083034776369438005991505)
  ·
    refine ⟨48812276082277078504493629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65083034776369438005991505 48812276082277078504493629)
    ·
      refine ⟨18304603530853904439185111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48812276082277078504493629 18304603530853904439185111)
      ·
        refine ⟨27456905296280856658777667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18304603530853904439185111 27456905296280856658777667)
        ·
          refine ⟨41185357944421284988166501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27456905296280856658777667 41185357944421284988166501)
          ·
            refine ⟨7722254614578990935281219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41185357944421284988166501 7722254614578990935281219)
            ·
              refine ⟨11583381921868486402921829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722254614578990935281219 11583381921868486402921829)
              ·
                refine ⟨2171884110350341200547843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11583381921868486402921829 2171884110350341200547843)
                ·
                  refine ⟨3257826165525511800821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171884110350341200547843 3257826165525511800821765)
                  ·
                    refine ⟨610842406036033462654081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257826165525511800821765 610842406036033462654081)
                    ·
                      rfl

theorem cell22_1784417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1784417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784417 prefixEnd_1784417 := by exact prefixLift 1784417
  have htrace : WordTrace (prefixWord ++ tailWord_1784417) baseStart_1784417 baseEnd_1784417 := by
    simpa [prefixWord, tailWord_1784417, baseEnd_1784417] using wordTrace_append hprefix tailTrace_1784417
  have hstable : (prefixWord ++ tailWord_1784417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784417).length < 2 ^ (prefixWord ++ tailWord_1784417).sum := by decide
  have hdescent : baseEnd_1784417 < baseStart_1784417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784462 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1784462 : Nat := 118140960795 + 1784462 * 2 ^ 59
def prefixEnd_1784462 : Nat := 4983230072969 + 3 ^ 40 * 1784462 * 2
def baseEnd_1784462 : Nat := 610857810455668345278943

theorem tailTrace_1784462 : CollatzResearch.WordTrace tailWord_1784462 prefixEnd_1784462 610857810455668345278943 := by
  unfold tailWord_1784462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135584507650801336422455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43389784040804273794253093 8135584507650801336422455)
  ·
    refine ⟨12203376761476202004633683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8135584507650801336422455 12203376761476202004633683)
    ·
      refine ⟨18305065142214303006950525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12203376761476202004633683 18305065142214303006950525)
      ·
        refine ⟨6864399428330363627606447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18305065142214303006950525 6864399428330363627606447)
        ·
          refine ⟨10296599142495545441409671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864399428330363627606447 10296599142495545441409671)
          ·
            refine ⟨15444898713743318162114507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296599142495545441409671 15444898713743318162114507)
            ·
              refine ⟨23167348070614977243171761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444898713743318162114507 23167348070614977243171761)
              ·
                refine ⟨17375511052961232932378821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23167348070614977243171761 17375511052961232932378821)
                ·
                  refine ⟨3257908322430231174821029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17375511052961232932378821 3257908322430231174821029)
                  ·
                    refine ⟨610857810455668345278943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3257908322430231174821029 610857810455668345278943)
                    ·
                      rfl

theorem cell22_1784462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1784462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784462 prefixEnd_1784462 := by exact prefixLift 1784462
  have htrace : WordTrace (prefixWord ++ tailWord_1784462) baseStart_1784462 baseEnd_1784462 := by
    simpa [prefixWord, tailWord_1784462, baseEnd_1784462] using wordTrace_append hprefix tailTrace_1784462
  have hstable : (prefixWord ++ tailWord_1784462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784462).length < 2 ^ (prefixWord ++ tailWord_1784462).sum := by decide
  have hdescent : baseEnd_1784462 < baseStart_1784462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784597 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1784597 : Nat := 118140960795 + 1784597 * 2 ^ 59
def prefixEnd_1784597 : Nat := 4983230072969 + 3 ^ 40 * 1784597 * 2
def baseEnd_1784597 : Nat := 610904023714572993153529

theorem tailTrace_1784597 : CollatzResearch.WordTrace tailWord_1784597 prefixEnd_1784597 610904023714572993153529 := by
  unfold tailWord_1784597
  simp only [CollatzResearch.WordTrace]
  refine ⟨65089599915717328747544045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43393066610478219165029363 65089599915717328747544045)
  ·
    refine ⟨24408599968393998280329017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65089599915717328747544045 24408599968393998280329017)
    ·
      refine ⟨18306449976295498710246763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24408599968393998280329017 18306449976295498710246763)
      ·
        refine ⟨27459674964443248065370145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18306449976295498710246763 27459674964443248065370145)
        ·
          refine ⟨20594756223332436049027609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27459674964443248065370145 20594756223332436049027609)
          ·
            refine ⟨15446067167499327036770707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20594756223332436049027609 15446067167499327036770707)
            ·
              refine ⟨23169100751248990555156061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15446067167499327036770707 23169100751248990555156061)
              ·
                refine ⟨8688412781718371458183523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23169100751248990555156061 8688412781718371458183523)
                ·
                  refine ⟨13032619172577557187275285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8688412781718371458183523 13032619172577557187275285)
                  ·
                    refine ⟨610904023714572993153529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13032619172577557187275285 610904023714572993153529)
                    ·
                      rfl

theorem cell22_1784597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1784597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784597 prefixEnd_1784597 := by exact prefixLift 1784597
  have htrace : WordTrace (prefixWord ++ tailWord_1784597) baseStart_1784597 baseEnd_1784597 := by
    simpa [prefixWord, tailWord_1784597, baseEnd_1784597] using wordTrace_append hprefix tailTrace_1784597
  have hstable : (prefixWord ++ tailWord_1784597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784597).length < 2 ^ (prefixWord ++ tailWord_1784597).sum := by decide
  have hdescent : baseEnd_1784597 < baseStart_1784597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784616 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1784616 : Nat := 118140960795 + 1784616 * 2 ^ 59
def prefixEnd_1784616 : Nat := 4983230072969 + 3 ^ 40 * 1784616 * 2
def baseEnd_1784616 : Nat := 610910527802863276928471

theorem tailTrace_1784616 : CollatzResearch.WordTrace tailWord_1784616 prefixEnd_1784616 610910527802863276928471 := by
  unfold tailWord_1784616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545146451324247496242851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43393528601765663328323801 32545146451324247496242851)
  ·
    refine ⟨48817719676986371244364277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32545146451324247496242851 48817719676986371244364277)
    ·
      refine ⟨4576661219717472304159151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48817719676986371244364277 4576661219717472304159151)
      ·
        refine ⟨6864991829576208456238727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576661219717472304159151 6864991829576208456238727)
        ·
          refine ⟨10297487744364312684358091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864991829576208456238727 10297487744364312684358091)
          ·
            refine ⟨15446231616546469026537137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10297487744364312684358091 15446231616546469026537137)
            ·
              refine ⟨11584673712409851769902853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15446231616546469026537137 11584673712409851769902853)
              ·
                refine ⟨2172126321076847206856785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11584673712409851769902853 2172126321076847206856785)
                ·
                  refine ⟨1629094740807635405142589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2172126321076847206856785 1629094740807635405142589)
                  ·
                    refine ⟨610910527802863276928471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629094740807635405142589 610910527802863276928471)
                    ·
                      rfl

theorem cell22_1784616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1784616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784616 prefixEnd_1784616 := by exact prefixLift 1784616
  have htrace : WordTrace (prefixWord ++ tailWord_1784616) baseStart_1784616 baseEnd_1784616 := by
    simpa [prefixWord, tailWord_1784616, baseEnd_1784616] using wordTrace_append hprefix tailTrace_1784616
  have hstable : (prefixWord ++ tailWord_1784616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784616).length < 2 ^ (prefixWord ++ tailWord_1784616).sum := by decide
  have hdescent : baseEnd_1784616 < baseStart_1784616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784618 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_1784618 : Nat := 118140960795 + 1784618 * 2 ^ 59
def prefixEnd_1784618 : Nat := 4983230072969 + 3 ^ 40 * 1784618 * 2
def baseEnd_1784618 : Nat := 203637070814578646126155

theorem tailTrace_1784618 : CollatzResearch.WordTrace tailWord_1784618 prefixEnd_1784618 203637070814578646126155 := by
  unfold tailWord_1784618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16272591462160312333514627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43393577232427499556039005 16272591462160312333514627)
  ·
    refine ⟨24408887193240468500271941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16272591462160312333514627 24408887193240468500271941)
    ·
      refine ⟨4576666348732587843800989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24408887193240468500271941 4576666348732587843800989)
      ·
        refine ⟨1716249880774720441425371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4576666348732587843800989 1716249880774720441425371)
        ·
          refine ⟨2574374821162080662138057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716249880774720441425371 2574374821162080662138057)
          ·
            refine ⟨1930781115871560496603543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2574374821162080662138057 1930781115871560496603543)
            ·
              refine ⟨2896171673807340744905315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930781115871560496603543 2896171673807340744905315)
              ·
                refine ⟨4344257510711011117357973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896171673807340744905315 4344257510711011117357973)
                ·
                  refine ⟨203637070814578646126155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4344257510711011117357973 203637070814578646126155)
                  ·
                    rfl

theorem cell22_1784618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_1784618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784618 prefixEnd_1784618 := by exact prefixLift 1784618
  have htrace : WordTrace (prefixWord ++ tailWord_1784618) baseStart_1784618 baseEnd_1784618 := by
    simpa [prefixWord, tailWord_1784618, baseEnd_1784618] using wordTrace_append hprefix tailTrace_1784618
  have hstable : (prefixWord ++ tailWord_1784618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784618).length < 2 ^ (prefixWord ++ tailWord_1784618).sum := by decide
  have hdescent : baseEnd_1784618 < baseStart_1784618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784629 : List Nat := [1, 3, 3, 1, 3, 2, 2, 7]
def baseStart_1784629 : Nat := 118140960795 + 1784629 * 2 ^ 59
def prefixEnd_1784629 : Nat := 4983230072969 + 3 ^ 40 * 1784629 * 2
def baseEnd_1784629 : Nat := 67879441996503952928159

theorem tailTrace_1784629 : CollatzResearch.WordTrace tailWord_1784629 prefixEnd_1784629 67879441996503952928159 := by
  unfold tailWord_1784629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65090767051601398212708941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43393844701067598808472627 65090767051601398212708941)
  ·
    refine ⟨24409037644350524329765853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65090767051601398212708941 24409037644350524329765853)
    ·
      refine ⟨9153389116631446623662195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24409037644350524329765853 9153389116631446623662195)
      ·
        refine ⟨13730083674947169935493293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9153389116631446623662195 13730083674947169935493293)
        ·
          refine ⟨5148781378105188725809985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13730083674947169935493293 5148781378105188725809985)
          ·
            refine ⟨3861586033578891544357489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5148781378105188725809985 3861586033578891544357489)
            ·
              refine ⟨2896189525184168658268117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861586033578891544357489 2896189525184168658268117)
              ·
                refine ⟨67879441996503952928159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2896189525184168658268117 67879441996503952928159)
                ·
                  rfl

theorem cell22_1784629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 7].length) (baseStart_1784629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784629 prefixEnd_1784629 := by exact prefixLift 1784629
  have htrace : WordTrace (prefixWord ++ tailWord_1784629) baseStart_1784629 baseEnd_1784629 := by
    simpa [prefixWord, tailWord_1784629, baseEnd_1784629] using wordTrace_append hprefix tailTrace_1784629
  have hstable : (prefixWord ++ tailWord_1784629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784629).length < 2 ^ (prefixWord ++ tailWord_1784629).sum := by decide
  have hdescent : baseEnd_1784629 < baseStart_1784629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784689 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1784689 : Nat := 118140960795 + 1784689 * 2 ^ 59
def prefixEnd_1784689 : Nat := 4983230072969 + 3 ^ 40 * 1784689 * 2
def baseEnd_1784689 : Nat := 610935517194715419853247

theorem tailTrace_1784689 : CollatzResearch.WordTrace tailWord_1784689 prefixEnd_1784689 610935517194715419853247 := by
  unfold tailWord_1784689
  simp only [CollatzResearch.WordTrace]
  refine ⟨65092955431384028459893121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43395303620922685639928747 65092955431384028459893121)
  ·
    refine ⟨48819716573538021344919841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65092955431384028459893121 48819716573538021344919841)
    ·
      refine ⟨36614787430153516008689881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48819716573538021344919841 36614787430153516008689881)
      ·
        refine ⟨27461090572615137006517411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36614787430153516008689881 27461090572615137006517411)
        ·
          refine ⟨41191635858922705509776117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27461090572615137006517411 41191635858922705509776117)
          ·
            refine ⟨3861715861774003641541511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41191635858922705509776117 3861715861774003641541511)
            ·
              refine ⟨5792573792661005462312267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861715861774003641541511 5792573792661005462312267)
              ·
                refine ⟨8688860688991508193468401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792573792661005462312267 8688860688991508193468401)
                ·
                  refine ⟨6516645516743631145101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688860688991508193468401 6516645516743631145101301)
                  ·
                    refine ⟨610935517194715419853247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6516645516743631145101301 610935517194715419853247)
                    ·
                      rfl

theorem cell22_1784689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1784689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784689 prefixEnd_1784689 := by exact prefixLift 1784689
  have htrace : WordTrace (prefixWord ++ tailWord_1784689) baseStart_1784689 baseEnd_1784689 := by
    simpa [prefixWord, tailWord_1784689, baseEnd_1784689] using wordTrace_append hprefix tailTrace_1784689
  have hstable : (prefixWord ++ tailWord_1784689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784689).length < 2 ^ (prefixWord ++ tailWord_1784689).sum := by decide
  have hdescent : baseEnd_1784689 < baseStart_1784689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784736 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_1784736 : Nat := 118140960795 + 1784736 * 2 ^ 59
def prefixEnd_1784736 : Nat := 4983230072969 + 3 ^ 40 * 1784736 * 2
def baseEnd_1784736 : Nat := 203650535418407654642701

theorem tailTrace_1784736 : CollatzResearch.WordTrace tailWord_1784736 prefixEnd_1784736 203650535418407654642701 := by
  unfold tailWord_1784736
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547334831106877743427031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43396446441475836991236041 32547334831106877743427031)
  ·
    refine ⟨48821002246660316615140547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32547334831106877743427031 48821002246660316615140547)
    ·
      refine ⟨73231503369990474922710821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48821002246660316615140547 73231503369990474922710821)
      ·
        refine ⟨13730906881873214048008279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73231503369990474922710821 13730906881873214048008279)
        ·
          refine ⟨20596360322809821072012419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13730906881873214048008279 20596360322809821072012419)
          ·
            refine ⟨30894540484214731608018629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20596360322809821072012419 30894540484214731608018629)
            ·
              refine ⟨5792726340790262176503493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30894540484214731608018629 5792726340790262176503493)
              ·
                refine ⟨1086136188898174158094405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5792726340790262176503493 1086136188898174158094405)
                ·
                  refine ⟨203650535418407654642701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086136188898174158094405 203650535418407654642701)
                  ·
                    rfl

theorem cell22_1784736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_1784736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784736 prefixEnd_1784736 := by exact prefixLift 1784736
  have htrace : WordTrace (prefixWord ++ tailWord_1784736) baseStart_1784736 baseEnd_1784736 := by
    simpa [prefixWord, tailWord_1784736, baseEnd_1784736] using wordTrace_append hprefix tailTrace_1784736
  have hstable : (prefixWord ++ tailWord_1784736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784736).length < 2 ^ (prefixWord ++ tailWord_1784736).sum := by decide
  have hdescent : baseEnd_1784736 < baseStart_1784736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784766 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1784766 : Nat := 118140960795 + 1784766 * 2 ^ 59
def prefixEnd_1784766 : Nat := 4983230072969 + 3 ^ 40 * 1784766 * 2
def baseEnd_1784766 : Nat := 610961875868312885678011

theorem tailTrace_1784766 : CollatzResearch.WordTrace tailWord_1784766 prefixEnd_1784766 610961875868312885678011 := by
  unfold tailWord_1784766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136970481513133826305769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43397175901403380406964101 8136970481513133826305769)
  ·
    refine ⟨6102727861134850369729327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8136970481513133826305769 6102727861134850369729327)
    ·
      refine ⟨9154091791702275554593991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6102727861134850369729327 9154091791702275554593991)
      ·
        refine ⟨13731137687553413331890987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9154091791702275554593991 13731137687553413331890987)
        ·
          refine ⟨20596706531330119997836481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13731137687553413331890987 20596706531330119997836481)
          ·
            refine ⟨15447529898497589998377361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20596706531330119997836481 15447529898497589998377361)
            ·
              refine ⟨11585647423873192498783021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15447529898497589998377361 11585647423873192498783021)
              ·
                refine ⟨4344617783952447187043633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11585647423873192498783021 4344617783952447187043633)
                ·
                  refine ⟨3258463337964335390282725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344617783952447187043633 3258463337964335390282725)
                  ·
                    refine ⟨610961875868312885678011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3258463337964335390282725 610961875868312885678011)
                    ·
                      rfl

theorem cell22_1784766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1784766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784766 prefixEnd_1784766 := by exact prefixLift 1784766
  have htrace : WordTrace (prefixWord ++ tailWord_1784766) baseStart_1784766 baseEnd_1784766 := by
    simpa [prefixWord, tailWord_1784766, baseEnd_1784766] using wordTrace_append hprefix tailTrace_1784766
  have hstable : (prefixWord ++ tailWord_1784766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784766).length < 2 ^ (prefixWord ++ tailWord_1784766).sum := by decide
  have hdescent : baseEnd_1784766 < baseStart_1784766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784802 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1784802 : Nat := 118140960795 + 1784802 * 2 ^ 59
def prefixEnd_1784802 : Nat := 4983230072969 + 3 ^ 40 * 1784802 * 2
def baseEnd_1784802 : Nat := 610974199404020791777901

theorem tailTrace_1784802 : CollatzResearch.WordTrace tailWord_1784802 prefixEnd_1784802 610974199404020791777901 := by
  unfold tailWord_1784802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274269219993662189689165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43398051253316432505837773 16274269219993662189689165)
  ·
    refine ⟨6102850957497623321133437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16274269219993662189689165 6102850957497623321133437)
    ·
      refine ⟨2288569109061608745425039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6102850957497623321133437 2288569109061608745425039)
      ·
        refine ⟨3432853663592413118137559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288569109061608745425039 3432853663592413118137559)
        ·
          refine ⟨5149280495388619677206339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432853663592413118137559 5149280495388619677206339)
          ·
            refine ⟨7723920743082929515809509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149280495388619677206339 7723920743082929515809509)
            ·
              refine ⟨1448235139328049284214283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7723920743082929515809509 1448235139328049284214283)
              ·
                refine ⟨2172352708992073926321425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448235139328049284214283 2172352708992073926321425)
                ·
                  refine ⟨1629264531744055444741069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2172352708992073926321425 1629264531744055444741069)
                  ·
                    refine ⟨610974199404020791777901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629264531744055444741069 610974199404020791777901)
                    ·
                      rfl

theorem cell22_1784802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1784802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784802 prefixEnd_1784802 := by exact prefixLift 1784802
  have htrace : WordTrace (prefixWord ++ tailWord_1784802) baseStart_1784802 baseEnd_1784802 := by
    simpa [prefixWord, tailWord_1784802, baseEnd_1784802] using wordTrace_append hprefix tailTrace_1784802
  have hstable : (prefixWord ++ tailWord_1784802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784802).length < 2 ^ (prefixWord ++ tailWord_1784802).sum := by decide
  have hdescent : baseEnd_1784802 < baseStart_1784802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784824 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_1784824 : Nat := 118140960795 + 1784824 * 2 ^ 59
def prefixEnd_1784824 : Nat := 4983230072969 + 3 ^ 40 * 1784824 * 2
def baseEnd_1784824 : Nat := 610981730453620067727833

theorem tailTrace_1784824 : CollatzResearch.WordTrace tailWord_1784824 prefixEnd_1784824 610981730453620067727833 := by
  unfold tailWord_1784824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32548939642947473258028763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43398586190596631010705017 32548939642947473258028763)
  ·
    refine ⟨48823409464421209887043145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32548939642947473258028763 48823409464421209887043145)
    ·
      refine ⟨36617557098315907415282359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48823409464421209887043145 36617557098315907415282359)
      ·
        refine ⟨54926335647473861122923539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36617557098315907415282359 54926335647473861122923539)
        ·
          refine ⟨82389503471210791684385309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54926335647473861122923539 82389503471210791684385309)
          ·
            refine ⟨30896063801704046881644491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82389503471210791684385309 30896063801704046881644491)
            ·
              refine ⟨46344095702556070322466737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30896063801704046881644491 46344095702556070322466737)
              ·
                refine ⟨34758071776917052741850053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46344095702556070322466737 34758071776917052741850053)
                ·
                  refine ⟨6517138458171947389096885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34758071776917052741850053 6517138458171947389096885)
                  ·
                    refine ⟨610981730453620067727833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6517138458171947389096885 610981730453620067727833)
                    ·
                      rfl

theorem cell22_1784824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_1784824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784824 prefixEnd_1784824 := by exact prefixLift 1784824
  have htrace : WordTrace (prefixWord ++ tailWord_1784824) baseStart_1784824 baseEnd_1784824 := by
    simpa [prefixWord, tailWord_1784824, baseEnd_1784824] using wordTrace_append hprefix tailTrace_1784824
  have hstable : (prefixWord ++ tailWord_1784824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784824).length < 2 ^ (prefixWord ++ tailWord_1784824).sum := by decide
  have hdescent : baseEnd_1784824 < baseStart_1784824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784856 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_1784856 : Nat := 118140960795 + 1784856 * 2 ^ 59
def prefixEnd_1784856 : Nat := 4983230072969 + 3 ^ 40 * 1784856 * 2
def baseEnd_1784856 : Nat := 610992684707582650927735

theorem tailTrace_1784856 : CollatzResearch.WordTrace tailWord_1784856 prefixEnd_1784856 610992684707582650927735 := by
  unfold tailWord_1784856
  simp only [CollatzResearch.WordTrace]
  refine ⟨32549523210889507990611211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43399364281186010654148281 32549523210889507990611211)
  ·
    refine ⟨48824284816334261985916817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32549523210889507990611211 48824284816334261985916817)
    ·
      refine ⟨36618213612250696489437613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48824284816334261985916817 36618213612250696489437613)
      ·
        refine ⟨13731830104594011183539105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36618213612250696489437613 13731830104594011183539105)
        ·
          refine ⟨10298872578445508387654329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13731830104594011183539105 10298872578445508387654329)
          ·
            refine ⟨7724154433834131290740747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298872578445508387654329 7724154433834131290740747)
            ·
              refine ⟨11586231650751196936111121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724154433834131290740747 11586231650751196936111121)
              ·
                refine ⟨8689673738063397702083341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11586231650751196936111121 8689673738063397702083341)
                ·
                  refine ⟨3258627651773774138281253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8689673738063397702083341 3258627651773774138281253)
                  ·
                    refine ⟨610992684707582650927735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3258627651773774138281253 610992684707582650927735)
                    ·
                      rfl

theorem cell22_1784856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_1784856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784856 prefixEnd_1784856 := by exact prefixLift 1784856
  have htrace : WordTrace (prefixWord ++ tailWord_1784856) baseStart_1784856 baseEnd_1784856 := by
    simpa [prefixWord, tailWord_1784856, baseEnd_1784856] using wordTrace_append hprefix tailTrace_1784856
  have hstable : (prefixWord ++ tailWord_1784856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784856).length < 2 ^ (prefixWord ++ tailWord_1784856).sum := by decide
  have hdescent : baseEnd_1784856 < baseStart_1784856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784888 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_1784888 : Nat := 118140960795 + 1784888 * 2 ^ 59
def prefixEnd_1784888 : Nat := 4983230072969 + 3 ^ 40 * 1784888 * 2
def baseEnd_1784888 : Nat := 203667879653848411375879

theorem tailTrace_1784888 : CollatzResearch.WordTrace tailWord_1784888 prefixEnd_1784888 203667879653848411375879 := by
  unfold tailWord_1784888
  simp only [CollatzResearch.WordTrace]
  refine ⟨32550106778831542723193659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43400142371775390297591545 32550106778831542723193659)
  ·
    refine ⟨48825160168247314084790489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32550106778831542723193659 48825160168247314084790489)
    ·
      refine ⟨36618870126185485563592867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48825160168247314084790489 36618870126185485563592867)
      ·
        refine ⟨54928305189278228345389301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36618870126185485563592867 54928305189278228345389301)
        ·
          refine ⟨5149528611494833907380247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54928305189278228345389301 5149528611494833907380247)
          ·
            refine ⟨7724292917242250861070371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149528611494833907380247 7724292917242250861070371)
            ·
              refine ⟨11586439375863376291605557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724292917242250861070371 11586439375863376291605557)
              ·
                refine ⟨1086228691487191527338021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11586439375863376291605557 1086228691487191527338021)
                ·
                  refine ⟨203667879653848411375879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086228691487191527338021 203667879653848411375879)
                  ·
                    rfl

theorem cell22_1784888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_1784888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784888 prefixEnd_1784888 := by exact prefixLift 1784888
  have htrace : WordTrace (prefixWord ++ tailWord_1784888) baseStart_1784888 baseEnd_1784888 := by
    simpa [prefixWord, tailWord_1784888, baseEnd_1784888] using wordTrace_append hprefix tailTrace_1784888
  have hstable : (prefixWord ++ tailWord_1784888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784888).length < 2 ^ (prefixWord ++ tailWord_1784888).sum := by decide
  have hdescent : baseEnd_1784888 < baseStart_1784888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784899 : List Nat := [1, 1, 1, 3, 1, 2, 13]
def baseStart_1784899 : Nat := 118140960795 + 1784899 * 2 ^ 59
def prefixEnd_1784899 : Nat := 4983230072969 + 3 ^ 40 * 1784899 * 2
def baseEnd_1784899 : Nat := 22629903869864624892689

theorem tailTrace_1784899 : CollatzResearch.WordTrace tailWord_1784899 prefixEnd_1784899 22629903869864624892689 := by
  unfold tailWord_1784899
  simp only [CollatzResearch.WordTrace]
  refine ⟨65100614760623234325037751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43400409840415489550025167 65100614760623234325037751)
  ·
    refine ⟨97650922140934851487556627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65100614760623234325037751 97650922140934851487556627)
    ·
      refine ⟨146476383211402277231334941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97650922140934851487556627 146476383211402277231334941)
      ·
        refine ⟨54928643704275853961750603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146476383211402277231334941 54928643704275853961750603)
        ·
          refine ⟨82392965556413780942625905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54928643704275853961750603 82392965556413780942625905)
          ·
            refine ⟨61794724167310335706969429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82392965556413780942625905 61794724167310335706969429)
            ·
              refine ⟨22629903869864624892689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 61794724167310335706969429 22629903869864624892689)
              ·
                rfl

theorem cell22_1784899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 13].length) (baseStart_1784899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784899 prefixEnd_1784899 := by exact prefixLift 1784899
  have htrace : WordTrace (prefixWord ++ tailWord_1784899) baseStart_1784899 baseEnd_1784899 := by
    simpa [prefixWord, tailWord_1784899, baseEnd_1784899] using wordTrace_append hprefix tailTrace_1784899
  have hstable : (prefixWord ++ tailWord_1784899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784899).length < 2 ^ (prefixWord ++ tailWord_1784899).sum := by decide
  have hdescent : baseEnd_1784899 < baseStart_1784899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784901 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_1784901 : Nat := 118140960795 + 1784901 * 2 ^ 59
def prefixEnd_1784901 : Nat := 4983230072969 + 3 ^ 40 * 1784901 * 2
def baseEnd_1784901 : Nat := 611008089127217533552597

theorem tailTrace_1784901 : CollatzResearch.WordTrace tailWord_1784901 prefixEnd_1784901 611008089127217533552597 := by
  unfold tailWord_1784901
  simp only [CollatzResearch.WordTrace]
  refine ⟨65100687706615988666610557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43400458471077325777740371 65100687706615988666610557)
  ·
    refine ⟨24412757889980995749978959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65100687706615988666610557 24412757889980995749978959)
    ·
      refine ⟨36619136834971493624968439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24412757889980995749978959 36619136834971493624968439)
      ·
        refine ⟨54928705252457240437452659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36619136834971493624968439 54928705252457240437452659)
        ·
          refine ⟨82393057878685860656178989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54928705252457240437452659 82393057878685860656178989)
          ·
            refine ⟨30897396704507197746067121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82393057878685860656178989 30897396704507197746067121)
            ·
              refine ⟨23173047528380398309550341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30897396704507197746067121 23173047528380398309550341)
              ·
                refine ⟨4344946411571324683040689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23173047528380398309550341 4344946411571324683040689)
                ·
                  refine ⟨3258709808678493512280517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344946411571324683040689 3258709808678493512280517)
                  ·
                    refine ⟨611008089127217533552597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3258709808678493512280517 611008089127217533552597)
                    ·
                      rfl

theorem cell22_1784901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_1784901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784901 prefixEnd_1784901 := by exact prefixLift 1784901
  have htrace : WordTrace (prefixWord ++ tailWord_1784901) baseStart_1784901 baseEnd_1784901 := by
    simpa [prefixWord, tailWord_1784901, baseEnd_1784901] using wordTrace_append hprefix tailTrace_1784901
  have hstable : (prefixWord ++ tailWord_1784901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784901).length < 2 ^ (prefixWord ++ tailWord_1784901).sum := by decide
  have hdescent : baseEnd_1784901 < baseStart_1784901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784903 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1784903 : Nat := 118140960795 + 1784903 * 2 ^ 59
def prefixEnd_1784903 : Nat := 4983230072969 + 3 ^ 40 * 1784903 * 2
def baseEnd_1784903 : Nat := 611008773768090195002591

theorem tailTrace_1784903 : CollatzResearch.WordTrace tailWord_1784903 prefixEnd_1784903 611008773768090195002591 := by
  unfold tailWord_1784903
  simp only [CollatzResearch.WordTrace]
  refine ⟨65100760652608743008183363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43400507101739162005455575 65100760652608743008183363)
  ·
    refine ⟨97651140978913114512275045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65100760652608743008183363 97651140978913114512275045)
    ·
      refine ⟨18309588933546208971051571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97651140978913114512275045 18309588933546208971051571)
      ·
        refine ⟨27464383400319313456577357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18309588933546208971051571 27464383400319313456577357)
        ·
          refine ⟨10299143775119742546216509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27464383400319313456577357 10299143775119742546216509)
          ·
            refine ⟨3862178915669903454831191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10299143775119742546216509 3862178915669903454831191)
            ·
              refine ⟨5793268373504855182246787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862178915669903454831191 5793268373504855182246787)
              ·
                refine ⟨8689902560257282773370181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793268373504855182246787 8689902560257282773370181)
                ·
                  refine ⟨1629356730048240520006909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8689902560257282773370181 1629356730048240520006909)
                  ·
                    refine ⟨611008773768090195002591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629356730048240520006909 611008773768090195002591)
                    ·
                      rfl

theorem cell22_1784903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1784903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784903 prefixEnd_1784903 := by exact prefixLift 1784903
  have htrace : WordTrace (prefixWord ++ tailWord_1784903) baseStart_1784903 baseEnd_1784903 := by
    simpa [prefixWord, tailWord_1784903, baseEnd_1784903] using wordTrace_append hprefix tailTrace_1784903
  have hstable : (prefixWord ++ tailWord_1784903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784903).length < 2 ^ (prefixWord ++ tailWord_1784903).sum := by decide
  have hdescent : baseEnd_1784903 < baseStart_1784903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784920 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_1784920 : Nat := 118140960795 + 1784920 * 2 ^ 59
def prefixEnd_1784920 : Nat := 4983230072969 + 3 ^ 40 * 1784920 * 2
def baseEnd_1784920 : Nat := 611014593215507817327539

theorem tailTrace_1784920 : CollatzResearch.WordTrace tailWord_1784920 prefixEnd_1784920 611014593215507817327539 := by
  unfold tailWord_1784920
  simp only [CollatzResearch.WordTrace]
  refine ⟨32550690346773577455776107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43400920462364769941034809 32550690346773577455776107)
  ·
    refine ⟨48826035520160366183664161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32550690346773577455776107 48826035520160366183664161)
    ·
      refine ⟨36619526640120274637748121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48826035520160366183664161 36619526640120274637748121)
      ·
        refine ⟨27464644980090205978311091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36619526640120274637748121 27464644980090205978311091)
        ·
          refine ⟨41196967470135308967466637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27464644980090205978311091 41196967470135308967466637)
          ·
            refine ⟨15448862801300740862799989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41196967470135308967466637 15448862801300740862799989)
            ·
              refine ⟨1448330887621944455887499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15448862801300740862799989 1448330887621944455887499)
              ·
                refine ⟨2172496331432916683831249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448330887621944455887499 2172496331432916683831249)
                ·
                  refine ⟨1629372248574687512873437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2172496331432916683831249 1629372248574687512873437)
                  ·
                    refine ⟨611014593215507817327539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629372248574687512873437 611014593215507817327539)
                    ·
                      rfl

theorem cell22_1784920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_1784920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784920 prefixEnd_1784920 := by exact prefixLift 1784920
  have htrace : WordTrace (prefixWord ++ tailWord_1784920) baseStart_1784920 baseEnd_1784920 := by
    simpa [prefixWord, tailWord_1784920, baseEnd_1784920] using wordTrace_append hprefix tailTrace_1784920
  have hstable : (prefixWord ++ tailWord_1784920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784920).length < 2 ^ (prefixWord ++ tailWord_1784920).sum := by decide
  have hdescent : baseEnd_1784920 < baseStart_1784920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785025 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1785025 : Nat := 118140960795 + 1785025 * 2 ^ 59
def prefixEnd_1785025 : Nat := 4983230072969 + 3 ^ 40 * 1785025 * 2
def baseEnd_1785025 : Nat := 611050536861322543452217

theorem tailTrace_1785025 : CollatzResearch.WordTrace tailWord_1785025 prefixEnd_1785025 611050536861322543452217 := by
  unfold tailWord_1785025
  simp only [CollatzResearch.WordTrace]
  refine ⟨65105210358166757844124529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43403473572111171896083019 65105210358166757844124529)
  ·
    refine ⟨48828907768625068383093397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65105210358166757844124529 48828907768625068383093397)
    ·
      refine ⟨2288855051654300080457503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48828907768625068383093397 2288855051654300080457503)
      ·
        refine ⟨3433282577481450120686255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288855051654300080457503 3433282577481450120686255)
        ·
          refine ⟨5149923866222175181029383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433282577481450120686255 5149923866222175181029383)
          ·
            refine ⟨7724885799333262771544075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149923866222175181029383 7724885799333262771544075)
            ·
              refine ⟨11587328698999894157316113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724885799333262771544075 11587328698999894157316113)
              ·
                refine ⟨8690496524249920617987085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11587328698999894157316113 8690496524249920617987085)
                ·
                  refine ⟨3258936196593720231745157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8690496524249920617987085 3258936196593720231745157)
                  ·
                    refine ⟨611050536861322543452217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3258936196593720231745157 611050536861322543452217)
                    ·
                      rfl

theorem cell22_1785025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1785025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785025 prefixEnd_1785025 := by exact prefixLift 1785025
  have htrace : WordTrace (prefixWord ++ tailWord_1785025) baseStart_1785025 baseEnd_1785025 := by
    simpa [prefixWord, tailWord_1785025, baseEnd_1785025] using wordTrace_append hprefix tailTrace_1785025
  have hstable : (prefixWord ++ tailWord_1785025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785025).length < 2 ^ (prefixWord ++ tailWord_1785025).sum := by decide
  have hdescent : baseEnd_1785025 < baseStart_1785025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785100 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1785100 : Nat := 118140960795 + 1785100 * 2 ^ 59
def prefixEnd_1785100 : Nat := 4983230072969 + 3 ^ 40 * 1785100 * 2
def baseEnd_1785100 : Nat := 611076210894047347826987

theorem tailTrace_1785100 : CollatzResearch.WordTrace tailWord_1785100 prefixEnd_1785100 611076210894047347826987 := by
  unfold tailWord_1785100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32553972916447522826552377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43405297221930030435403169 32553972916447522826552377)
  ·
    refine ⟨24415479687335642119914283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32553972916447522826552377 24415479687335642119914283)
    ·
      refine ⟨36623219531003463179871425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24415479687335642119914283 36623219531003463179871425)
      ·
        refine ⟨27467414648252597384903569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36623219531003463179871425 27467414648252597384903569)
        ·
          refine ⟨20600560986189448038677677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27467414648252597384903569 20600560986189448038677677)
          ·
            refine ⟨7725210369821043014504129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20600560986189448038677677 7725210369821043014504129)
            ·
              refine ⟨5793907777365782260878097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7725210369821043014504129 5793907777365782260878097)
              ·
                refine ⟨4345430833024336695658573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793907777365782260878097 4345430833024336695658573)
                ·
                  refine ⟨1629536562384126260871965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4345430833024336695658573 1629536562384126260871965)
                  ·
                    refine ⟨611076210894047347826987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629536562384126260871965 611076210894047347826987)
                    ·
                      rfl

theorem cell22_1785100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1785100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785100 prefixEnd_1785100 := by exact prefixLift 1785100
  have htrace : WordTrace (prefixWord ++ tailWord_1785100) baseStart_1785100 baseEnd_1785100 := by
    simpa [prefixWord, tailWord_1785100, baseEnd_1785100] using wordTrace_append hprefix tailTrace_1785100
  have hstable : (prefixWord ++ tailWord_1785100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785100).length < 2 ^ (prefixWord ++ tailWord_1785100).sum := by decide
  have hdescent : baseEnd_1785100 < baseStart_1785100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785130 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1785130 : Nat := 118140960795 + 1785130 * 2 ^ 59
def prefixEnd_1785130 : Nat := 4983230072969 + 3 ^ 40 * 1785130 * 2
def baseEnd_1785130 : Nat := 203695493502379089858965

theorem tailTrace_1785130 : CollatzResearch.WordTrace tailWord_1785130 prefixEnd_1785130 203695493502379089858965 := by
  unfold tailWord_1785130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277260005696590194174211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43406026681857573851131229 16277260005696590194174211)
  ·
    refine ⟨24415890008544885291261317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16277260005696590194174211 24415890008544885291261317)
    ·
      refine ⟨4577979376602165992111497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24415890008544885291261317 4577979376602165992111497)
      ·
        refine ⟨3433484532451624494083623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577979376602165992111497 3433484532451624494083623)
        ·
          refine ⟨5150226798677436741125435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433484532451624494083623 5150226798677436741125435)
          ·
            refine ⟨7725340198016155111688153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150226798677436741125435 7725340198016155111688153)
            ·
              refine ⟨5794005148512116333766115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7725340198016155111688153 5794005148512116333766115)
              ·
                refine ⟨8691007722768174500649173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794005148512116333766115 8691007722768174500649173)
                ·
                  refine ⟨203695493502379089858965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8691007722768174500649173 203695493502379089858965)
                  ·
                    rfl

theorem cell22_1785130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1785130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785130 prefixEnd_1785130 := by exact prefixLift 1785130
  have htrace : WordTrace (prefixWord ++ tailWord_1785130) baseStart_1785130 baseEnd_1785130 := by
    simpa [prefixWord, tailWord_1785130, baseEnd_1785130] using wordTrace_append hprefix tailTrace_1785130
  have hstable : (prefixWord ++ tailWord_1785130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785130).length < 2 ^ (prefixWord ++ tailWord_1785130).sum := by decide
  have hdescent : baseEnd_1785130 < baseStart_1785130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785181 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 5]
def baseStart_1785181 : Nat := 118140960795 + 1785181 * 2 ^ 59
def prefixEnd_1785181 : Nat := 4983230072969 + 3 ^ 40 * 1785181 * 2
def baseEnd_1785181 : Nat := 203701312949796712183913

theorem tailTrace_1785181 : CollatzResearch.WordTrace tailWord_1785181 prefixEnd_1785181 203701312949796712183913 := by
  unfold tailWord_1785181
  simp only [CollatzResearch.WordTrace]
  refine ⟨65110900145601596486803397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43407266763734397657868931 65110900145601596486803397)
  ·
    refine ⟨12208293777300299341275637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65110900145601596486803397 12208293777300299341275637)
    ·
      refine ⟨1144527541621903063244591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12208293777300299341275637 1144527541621903063244591)
      ·
        refine ⟨1716791312432854594866887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144527541621903063244591 1716791312432854594866887)
        ·
          refine ⟨2575186968649281892300331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716791312432854594866887 2575186968649281892300331)
          ·
            refine ⟨3862780452973922838450497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575186968649281892300331 3862780452973922838450497)
            ·
              refine ⟨2897085339730442128837873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862780452973922838450497 2897085339730442128837873)
              ·
                refine ⟨2172814004797831596628405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897085339730442128837873 2172814004797831596628405)
                ·
                  refine ⟨203701312949796712183913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2172814004797831596628405 203701312949796712183913)
                  ·
                    rfl

theorem cell22_1785181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_1785181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785181 prefixEnd_1785181 := by exact prefixLift 1785181
  have htrace : WordTrace (prefixWord ++ tailWord_1785181) baseStart_1785181 baseEnd_1785181 := by
    simpa [prefixWord, tailWord_1785181, baseEnd_1785181] using wordTrace_append hprefix tailTrace_1785181
  have hstable : (prefixWord ++ tailWord_1785181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785181).length < 2 ^ (prefixWord ++ tailWord_1785181).sum := by decide
  have hdescent : baseEnd_1785181 < baseStart_1785181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785233 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1785233 : Nat := 118140960795 + 1785233 * 2 ^ 59
def prefixEnd_1785233 : Nat := 4983230072969 + 3 ^ 40 * 1785233 * 2
def baseEnd_1785233 : Nat := 611121739512079334251579

theorem tailTrace_1785233 : CollatzResearch.WordTrace tailWord_1785233 prefixEnd_1785233 611121739512079334251579 := by
  unfold tailWord_1785233
  simp only [CollatzResearch.WordTrace]
  refine ⟨65112796741413209367696353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43408531160942139578464235 65112796741413209367696353)
  ·
    refine ⟨48834597556059907025772265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65112796741413209367696353 48834597556059907025772265)
    ·
      refine ⟨36625948167044930269329199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48834597556059907025772265 36625948167044930269329199)
      ·
        refine ⟨54938922250567395403993799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36625948167044930269329199 54938922250567395403993799)
        ·
          refine ⟨82408383375851093105990699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54938922250567395403993799 82408383375851093105990699)
          ·
            refine ⟨123612575063776639658986049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82408383375851093105990699 123612575063776639658986049)
            ·
              refine ⟨92709431297832479744239537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123612575063776639658986049 92709431297832479744239537)
              ·
                refine ⟨69532073473374359808179653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92709431297832479744239537 69532073473374359808179653)
                ·
                  refine ⟨13037263776257692464033685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69532073473374359808179653 13037263776257692464033685)
                  ·
                    refine ⟨611121739512079334251579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13037263776257692464033685 611121739512079334251579)
                    ·
                      rfl

theorem cell22_1785233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1785233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785233 prefixEnd_1785233 := by exact prefixLift 1785233
  have htrace : WordTrace (prefixWord ++ tailWord_1785233) baseStart_1785233 baseEnd_1785233 := by
    simpa [prefixWord, tailWord_1785233, baseEnd_1785233] using wordTrace_append hprefix tailTrace_1785233
  have hstable : (prefixWord ++ tailWord_1785233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785233).length < 2 ^ (prefixWord ++ tailWord_1785233).sum := by decide
  have hdescent : baseEnd_1785233 < baseStart_1785233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785329 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_1785329 : Nat := 118140960795 + 1785329 * 2 ^ 59
def prefixEnd_1785329 : Nat := 4983230072969 + 3 ^ 40 * 1785329 * 2
def baseEnd_1785329 : Nat := 611154602273967083851285

theorem tailTrace_1785329 : CollatzResearch.WordTrace tailWord_1785329 prefixEnd_1785329 611154602273967083851285 := by
  unfold tailWord_1785329
  simp only [CollatzResearch.WordTrace]
  refine ⟨65116298149065417763191041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43410865432710278508794027 65116298149065417763191041)
  ·
    refine ⟨48837223611799063322393281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65116298149065417763191041 48837223611799063322393281)
    ·
      refine ⟨36627917708849297491794961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48837223611799063322393281 36627917708849297491794961)
      ·
        refine ⟨27470938281636973118846221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36627917708849297491794961 27470938281636973118846221)
        ·
          refine ⟨10301601855613864919567333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27470938281636973118846221 10301601855613864919567333)
          ·
            refine ⟨1931550347927599672418875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10301601855613864919567333 1931550347927599672418875)
            ·
              refine ⟨2897325521891399508628313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931550347927599672418875 2897325521891399508628313)
              ·
                refine ⟨2172994141418549631471235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897325521891399508628313 2172994141418549631471235)
                ·
                  refine ⟨3259491212127824447206853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172994141418549631471235 3259491212127824447206853)
                  ·
                    refine ⟨611154602273967083851285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259491212127824447206853 611154602273967083851285)
                    ·
                      rfl

theorem cell22_1785329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_1785329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785329 prefixEnd_1785329 := by exact prefixLift 1785329
  have htrace : WordTrace (prefixWord ++ tailWord_1785329) baseStart_1785329 baseEnd_1785329 := by
    simpa [prefixWord, tailWord_1785329, baseEnd_1785329] using wordTrace_append hprefix tailTrace_1785329
  have hstable : (prefixWord ++ tailWord_1785329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785329).length < 2 ^ (prefixWord ++ tailWord_1785329).sum := by decide
  have hdescent : baseEnd_1785329 < baseStart_1785329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785340 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1785340 : Nat := 118140960795 + 1785340 * 2 ^ 59
def prefixEnd_1785340 : Nat := 4983230072969 + 3 ^ 40 * 1785340 * 2
def baseEnd_1785340 : Nat := 611158367798766721826251

theorem tailTrace_1785340 : CollatzResearch.WordTrace tailWord_1785340 prefixEnd_1785340 611158367798766721826251 := by
  unfold tailWord_1785340
  simp only [CollatzResearch.WordTrace]
  refine ⟨32558349676012783320920737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43411132901350377761227649 32558349676012783320920737)
  ·
    refine ⟨24418762257009587490690553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32558349676012783320920737 24418762257009587490690553)
    ·
      refine ⟨18314071692757190618017915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24418762257009587490690553 18314071692757190618017915)
      ·
        refine ⟨27471107539135785927026873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314071692757190618017915 27471107539135785927026873)
        ·
          refine ⟨20603330654351839445270155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27471107539135785927026873 20603330654351839445270155)
          ·
            refine ⟨30904995981527759167905233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20603330654351839445270155 30904995981527759167905233)
            ·
              refine ⟨23178746986145819375928925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30904995981527759167905233 23178746986145819375928925)
              ·
                refine ⟨8692030119804682265973347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23178746986145819375928925 8692030119804682265973347)
                ·
                  refine ⟨13038045179707023398960021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692030119804682265973347 13038045179707023398960021)
                  ·
                    refine ⟨611158367798766721826251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13038045179707023398960021 611158367798766721826251)
                    ·
                      rfl

theorem cell22_1785340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1785340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785340 prefixEnd_1785340 := by exact prefixLift 1785340
  have htrace : WordTrace (prefixWord ++ tailWord_1785340) baseStart_1785340 baseEnd_1785340 := by
    simpa [prefixWord, tailWord_1785340, baseEnd_1785340] using wordTrace_append hprefix tailTrace_1785340
  have hstable : (prefixWord ++ tailWord_1785340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785340).length < 2 ^ (prefixWord ++ tailWord_1785340).sum := by decide
  have hdescent : baseEnd_1785340 < baseStart_1785340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785355 : List Nat := [1, 1, 1, 1, 8, 10]
def baseStart_1785355 : Nat := 118140960795 + 1785355 * 2 ^ 59
def prefixEnd_1785355 : Nat := 4983230072969 + 3 ^ 40 * 1785355 * 2
def baseEnd_1785355 : Nat := 7545228427226070156805

theorem tailTrace_1785355 : CollatzResearch.WordTrace tailWord_1785355 prefixEnd_1785355 7545228427226070156805 := by
  unfold tailWord_1785355
  simp only [CollatzResearch.WordTrace]
  refine ⟨65117246446971224203637519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43411497631314149469091679 65117246446971224203637519)
  ·
    refine ⟨97675869670456836305456279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65117246446971224203637519 97675869670456836305456279)
    ·
      refine ⟨146513804505685254458184419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97675869670456836305456279 146513804505685254458184419)
      ·
        refine ⟨219770706758527881687276629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146513804505685254458184419 219770706758527881687276629)
        ·
          refine ⟨2575437969826498613522773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 219770706758527881687276629 2575437969826498613522773)
          ·
            refine ⟨7545228427226070156805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2575437969826498613522773 7545228427226070156805)
            ·
              rfl

theorem cell22_1785355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 10].length) (baseStart_1785355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785355 prefixEnd_1785355 := by exact prefixLift 1785355
  have htrace : WordTrace (prefixWord ++ tailWord_1785355) baseStart_1785355 baseEnd_1785355 := by
    simpa [prefixWord, tailWord_1785355, baseEnd_1785355] using wordTrace_append hprefix tailTrace_1785355
  have hstable : (prefixWord ++ tailWord_1785355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785355).length < 2 ^ (prefixWord ++ tailWord_1785355).sum := by decide
  have hdescent : baseEnd_1785355 < baseStart_1785355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785370 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1785370 : Nat := 118140960795 + 1785370 * 2 ^ 59
def prefixEnd_1785370 : Nat := 4983230072969 + 3 ^ 40 * 1785370 * 2
def baseEnd_1785370 : Nat := 611168637411856643576159

theorem tailTrace_1785370 : CollatzResearch.WordTrace tailWord_1785370 prefixEnd_1785370 611168637411856643576159 := by
  unfold tailWord_1785370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16279448385479220441358391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43411862361277921176955709 16279448385479220441358391)
  ·
    refine ⟨24419172578218830662037587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16279448385479220441358391 24419172578218830662037587)
    ·
      refine ⟨36628758867328245993056381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24419172578218830662037587 36628758867328245993056381)
      ·
        refine ⟨13735784575248092247396143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36628758867328245993056381 13735784575248092247396143)
        ·
          refine ⟨20603676862872138371094215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13735784575248092247396143 20603676862872138371094215)
          ·
            refine ⟨30905515294308207556641323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20603676862872138371094215 30905515294308207556641323)
            ·
              refine ⟨46358272941462311334961985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30905515294308207556641323 46358272941462311334961985)
              ·
                refine ⟨34768704706096733501221489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46358272941462311334961985 34768704706096733501221489)
                ·
                  refine ⟨26076528529572550125916117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34768704706096733501221489 26076528529572550125916117)
                  ·
                    refine ⟨611168637411856643576159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26076528529572550125916117 611168637411856643576159)
                    ·
                      rfl

theorem cell22_1785370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1785370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785370 prefixEnd_1785370 := by exact prefixLift 1785370
  have htrace : WordTrace (prefixWord ++ tailWord_1785370) baseStart_1785370 baseEnd_1785370 := by
    simpa [prefixWord, tailWord_1785370, baseEnd_1785370] using wordTrace_append hprefix tailTrace_1785370
  have hstable : (prefixWord ++ tailWord_1785370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785370).length < 2 ^ (prefixWord ++ tailWord_1785370).sum := by decide
  have hdescent : baseEnd_1785370 < baseStart_1785370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785447 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1785447 : Nat := 118140960795 + 1785447 * 2 ^ 59
def prefixEnd_1785447 : Nat := 4983230072969 + 3 ^ 40 * 1785447 * 2
def baseEnd_1785447 : Nat := 611194996085454109400923

theorem tailTrace_1785447 : CollatzResearch.WordTrace tailWord_1785447 prefixEnd_1785447 611194996085454109400923 := by
  unfold tailWord_1785447
  simp only [CollatzResearch.WordTrace]
  refine ⟨65120601962637923915986595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43413734641758615943991063 65120601962637923915986595)
  ·
    refine ⟨97680902943956885873979893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65120601962637923915986595 97680902943956885873979893)
    ·
      refine ⟨9157584650995958050685615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97680902943956885873979893 9157584650995958050685615)
      ·
        refine ⟨13736376976493937076028423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157584650995958050685615 13736376976493937076028423)
        ·
          refine ⟨20604565464740905614042635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13736376976493937076028423 20604565464740905614042635)
          ·
            refine ⟨30906848197111358421063953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20604565464740905614042635 30906848197111358421063953)
            ·
              refine ⟨23180136147833518815797965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30906848197111358421063953 23180136147833518815797965)
              ·
                refine ⟨8692551055437569555924237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23180136147833518815797965 8692551055437569555924237)
                ·
                  refine ⟨3259706645789088583471589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8692551055437569555924237 3259706645789088583471589)
                  ·
                    refine ⟨611194996085454109400923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259706645789088583471589 611194996085454109400923)
                    ·
                      rfl

theorem cell22_1785447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1785447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785447 prefixEnd_1785447 := by exact prefixLift 1785447
  have htrace : WordTrace (prefixWord ++ tailWord_1785447) baseStart_1785447 baseEnd_1785447 := by
    simpa [prefixWord, tailWord_1785447, baseEnd_1785447] using wordTrace_append hprefix tailTrace_1785447
  have hstable : (prefixWord ++ tailWord_1785447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785447).length < 2 ^ (prefixWord ++ tailWord_1785447).sum := by decide
  have hdescent : baseEnd_1785447 < baseStart_1785447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785479 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 6]
def baseStart_1785479 : Nat := 118140960795 + 1785479 * 2 ^ 59
def prefixEnd_1785479 : Nat := 4983230072969 + 3 ^ 40 * 1785479 * 2
def baseEnd_1785479 : Nat := 203735316779805564200275

theorem tailTrace_1785479 : CollatzResearch.WordTrace tailWord_1785479 prefixEnd_1785479 203735316779805564200275 := by
  unfold tailWord_1785479
  simp only [CollatzResearch.WordTrace]
  refine ⟨65121769098521993381151491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43414512732347995587434327 65121769098521993381151491)
  ·
    refine ⟨97682653647782990071727237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65121769098521993381151491 97682653647782990071727237)
    ·
      refine ⟨18315497558959310638448857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97682653647782990071727237 18315497558959310638448857)
      ·
        refine ⟨13736623169219482978836643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18315497558959310638448857 13736623169219482978836643)
        ·
          refine ⟨20604934753829224468254965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13736623169219482978836643 20604934753829224468254965)
          ·
            refine ⟨1931712633171489793898903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20604934753829224468254965 1931712633171489793898903)
            ·
              refine ⟨2897568949757234690848355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931712633171489793898903 2897568949757234690848355)
              ·
                refine ⟨4346353424635852036272533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897568949757234690848355 4346353424635852036272533)
                ·
                  refine ⟨203735316779805564200275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4346353424635852036272533 203735316779805564200275)
                  ·
                    rfl

theorem cell22_1785479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 6].length) (baseStart_1785479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785479 prefixEnd_1785479 := by exact prefixLift 1785479
  have htrace : WordTrace (prefixWord ++ tailWord_1785479) baseStart_1785479 baseEnd_1785479 := by
    simpa [prefixWord, tailWord_1785479, baseEnd_1785479] using wordTrace_append hprefix tailTrace_1785479
  have hstable : (prefixWord ++ tailWord_1785479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785479).length < 2 ^ (prefixWord ++ tailWord_1785479).sum := by decide
  have hdescent : baseEnd_1785479 < baseStart_1785479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785556 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1785556 : Nat := 118140960795 + 1785556 * 2 ^ 59
def prefixEnd_1785556 : Nat := 4983230072969 + 3 ^ 40 * 1785556 * 2
def baseEnd_1785556 : Nat := 611232309013014158425589

theorem tailTrace_1785556 : CollatzResearch.WordTrace tailWord_1785556 prefixEnd_1785556 611232309013014158425589 := by
  unfold tailWord_1785556
  simp only [CollatzResearch.WordTrace]
  refine ⟨32562288759621517765852261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43416385012828690354469681 32562288759621517765852261)
  ·
    refine ⟨6105429142429034581097299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32562288759621517765852261 6105429142429034581097299)
    ·
      refine ⟨9158143713643551871645949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105429142429034581097299 9158143713643551871645949)
      ·
        refine ⟨3434303892616331951867231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9158143713643551871645949 3434303892616331951867231)
        ·
          refine ⟨5151455838924497927800847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434303892616331951867231 5151455838924497927800847)
          ·
            refine ⟨7727183758386746891701271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151455838924497927800847 7727183758386746891701271)
            ·
              refine ⟨11590775637580120337551907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727183758386746891701271 11590775637580120337551907)
              ·
                refine ⟨17386163456370180506327861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11590775637580120337551907 17386163456370180506327861)
                ·
                  refine ⟨1629952824034704422468237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17386163456370180506327861 1629952824034704422468237)
                  ·
                    refine ⟨611232309013014158425589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629952824034704422468237 611232309013014158425589)
                    ·
                      rfl

theorem cell22_1785556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1785556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785556 prefixEnd_1785556 := by exact prefixLift 1785556
  have htrace : WordTrace (prefixWord ++ tailWord_1785556) baseStart_1785556 baseEnd_1785556 := by
    simpa [prefixWord, tailWord_1785556, baseEnd_1785556] using wordTrace_append hprefix tailTrace_1785556
  have hstable : (prefixWord ++ tailWord_1785556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785556).length < 2 ^ (prefixWord ++ tailWord_1785556).sum := by decide
  have hdescent : baseEnd_1785556 < baseStart_1785556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785567 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_1785567 : Nat := 118140960795 + 1785567 * 2 ^ 59
def prefixEnd_1785567 : Nat := 4983230072969 + 3 ^ 40 * 1785567 * 2
def baseEnd_1785567 : Nat := 611236074537813796400555

theorem tailTrace_1785567 : CollatzResearch.WordTrace tailWord_1785567 prefixEnd_1785567 611236074537813796400555 := by
  unfold tailWord_1785567
  simp only [CollatzResearch.WordTrace]
  refine ⟨65124978722203184410354955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43416652481468789606903303 65124978722203184410354955)
  ·
    refine ⟨97687468083304776615532433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65124978722203184410354955 97687468083304776615532433)
    ·
      refine ⟨73265601062478582461649325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97687468083304776615532433 73265601062478582461649325)
      ·
        refine ⟨27474600398429468423118497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73265601062478582461649325 27474600398429468423118497)
        ·
          refine ⟨20605950298822101317338873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27474600398429468423118497 20605950298822101317338873)
          ·
            refine ⟨15454462724116575988004155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20605950298822101317338873 15454462724116575988004155)
            ·
              refine ⟨23181694086174863982006233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15454462724116575988004155 23181694086174863982006233)
              ·
                refine ⟨17386270564631147986504675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23181694086174863982006233 17386270564631147986504675)
                ·
                  refine ⟨26079405846946721979757013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17386270564631147986504675 26079405846946721979757013)
                  ·
                    refine ⟨611236074537813796400555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26079405846946721979757013 611236074537813796400555)
                    ·
                      rfl

theorem cell22_1785567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_1785567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785567 prefixEnd_1785567 := by exact prefixLift 1785567
  have htrace : WordTrace (prefixWord ++ tailWord_1785567) baseStart_1785567 baseEnd_1785567 := by
    simpa [prefixWord, tailWord_1785567, baseEnd_1785567] using wordTrace_append hprefix tailTrace_1785567
  have hstable : (prefixWord ++ tailWord_1785567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785567).length < 2 ^ (prefixWord ++ tailWord_1785567).sum := by decide
  have hdescent : baseEnd_1785567 < baseStart_1785567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785573 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_1785573 : Nat := 118140960795 + 1785573 * 2 ^ 59
def prefixEnd_1785573 : Nat := 4983230072969 + 3 ^ 40 * 1785573 * 2
def baseEnd_1785573 : Nat := 611238128460431780750537

theorem tailTrace_1785573 : CollatzResearch.WordTrace tailWord_1785573 prefixEnd_1785573 611238128460431780750537 := by
  unfold tailWord_1785573
  simp only [CollatzResearch.WordTrace]
  refine ⟨65125197560181447435073373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43416798373454298290048915 65125197560181447435073373)
  ·
    refine ⟨24421949085068042788152515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65125197560181447435073373 24421949085068042788152515)
    ·
      refine ⟨36632923627602064182228773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24421949085068042788152515 36632923627602064182228773)
      ·
        refine ⟨6868673180175387034167895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36632923627602064182228773 6868673180175387034167895)
        ·
          refine ⟨10303009770263080551251843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868673180175387034167895 10303009770263080551251843)
          ·
            refine ⟨15454514655394620826877765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10303009770263080551251843 15454514655394620826877765)
            ·
              refine ⟨2897721497886491405039581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15454514655394620826877765 2897721497886491405039581)
              ·
                refine ⟨1086645561707434276889843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897721497886491405039581 1086645561707434276889843)
                ·
                  refine ⟨1629968342561151415334765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086645561707434276889843 1629968342561151415334765)
                  ·
                    refine ⟨611238128460431780750537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629968342561151415334765 611238128460431780750537)
                    ·
                      rfl

theorem cell22_1785573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_1785573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785573 prefixEnd_1785573 := by exact prefixLift 1785573
  have htrace : WordTrace (prefixWord ++ tailWord_1785573) baseStart_1785573 baseEnd_1785573 := by
    simpa [prefixWord, tailWord_1785573, baseEnd_1785573] using wordTrace_append hprefix tailTrace_1785573
  have hstable : (prefixWord ++ tailWord_1785573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785573).length < 2 ^ (prefixWord ++ tailWord_1785573).sum := by decide
  have hdescent : baseEnd_1785573 < baseStart_1785573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785614 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1785614 : Nat := 118140960795 + 1785614 * 2 ^ 59
def prefixEnd_1785614 : Nat := 4983230072969 + 3 ^ 40 * 1785614 * 2
def baseEnd_1785614 : Nat := 203750721199440446825137

theorem tailTrace_1785614 : CollatzResearch.WordTrace tailWord_1785614 prefixEnd_1785614 203750721199440446825137 := by
  unfold tailWord_1785614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140836619129113929664487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43417795302021940958210597 8140836619129113929664487)
  ·
    refine ⟨12211254928693670894496731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140836619129113929664487 12211254928693670894496731)
    ·
      refine ⟨18316882393040506341745097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211254928693670894496731 18316882393040506341745097)
      ·
        refine ⟨13737661794780379756308823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18316882393040506341745097 13737661794780379756308823)
        ·
          refine ⟨20606492692170569634463235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13737661794780379756308823 20606492692170569634463235)
          ·
            refine ⟨30909739038255854451694853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20606492692170569634463235 30909739038255854451694853)
            ·
              refine ⟨5795576069672972709692785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30909739038255854451694853 5795576069672972709692785)
              ·
                refine ⟨4346682052254729532269589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5795576069672972709692785 4346682052254729532269589)
                ·
                  refine ⟨203750721199440446825137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4346682052254729532269589 203750721199440446825137)
                  ·
                    rfl

theorem cell22_1785614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1785614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785614 prefixEnd_1785614 := by exact prefixLift 1785614
  have htrace : WordTrace (prefixWord ++ tailWord_1785614) baseStart_1785614 baseEnd_1785614 := by
    simpa [prefixWord, tailWord_1785614, baseEnd_1785614] using wordTrace_append hprefix tailTrace_1785614
  have hstable : (prefixWord ++ tailWord_1785614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785614).length < 2 ^ (prefixWord ++ tailWord_1785614).sum := by decide
  have hdescent : baseEnd_1785614 < baseStart_1785614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785644 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_1785644 : Nat := 118140960795 + 1785644 * 2 ^ 59
def prefixEnd_1785644 : Nat := 4983230072969 + 3 ^ 40 * 1785644 * 2
def baseEnd_1785644 : Nat := 611262433211411262225319

theorem tailTrace_1785644 : CollatzResearch.WordTrace tailWord_1785644 prefixEnd_1785644 611262433211411262225319 := by
  unfold tailWord_1785644
  simp only [CollatzResearch.WordTrace]
  refine ⟨32563893571462113280453993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43418524761949484373938657 32563893571462113280453993)
  ·
    refine ⟨24422920178596584960340495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32563893571462113280453993 24422920178596584960340495)
    ·
      refine ⟨36634380267894877440510743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24422920178596584960340495 36634380267894877440510743)
      ·
        refine ⟨54951570401842316160766115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36634380267894877440510743 54951570401842316160766115)
        ·
          refine ⟨82427355602763474241149173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54951570401842316160766115 82427355602763474241149173)
          ·
            refine ⟨7727564587759075710107735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82427355602763474241149173 7727564587759075710107735)
            ·
              refine ⟨11591346881638613565161603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727564587759075710107735 11591346881638613565161603)
              ·
                refine ⟨17387020322457920347742405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591346881638613565161603 17387020322457920347742405)
                ·
                  refine ⟨3260066310460860065201701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17387020322457920347742405 3260066310460860065201701)
                  ·
                    refine ⟨611262433211411262225319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260066310460860065201701 611262433211411262225319)
                    ·
                      rfl

theorem cell22_1785644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_1785644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785644 prefixEnd_1785644 := by exact prefixLift 1785644
  have htrace : WordTrace (prefixWord ++ tailWord_1785644) baseStart_1785644 baseEnd_1785644 := by
    simpa [prefixWord, tailWord_1785644, baseEnd_1785644] using wordTrace_append hprefix tailTrace_1785644
  have hstable : (prefixWord ++ tailWord_1785644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785644).length < 2 ^ (prefixWord ++ tailWord_1785644).sum := by decide
  have hdescent : baseEnd_1785644 < baseStart_1785644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785663 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 2, 3]
def baseStart_1785663 : Nat := 118140960795 + 1785663 * 2 ^ 59
def prefixEnd_1785663 : Nat := 4983230072969 + 3 ^ 40 * 1785663 * 2
def baseEnd_1785663 : Nat := 611268937299701546000261

theorem tailTrace_1785663 : CollatzResearch.WordTrace tailWord_1785663 prefixEnd_1785663 611268937299701546000261 := by
  unfold tailWord_1785663
  simp only [CollatzResearch.WordTrace]
  refine ⟨65128480129855392805849643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43418986753236928537233095 65128480129855392805849643)
  ·
    refine ⟨97692720194783089208774465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65128480129855392805849643 97692720194783089208774465)
    ·
      refine ⟨73269540146087316906580849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97692720194783089208774465 73269540146087316906580849)
      ·
        refine ⟨54952155109565487679935637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73269540146087316906580849 54952155109565487679935637)
        ·
          refine ⟨2575882270760882234996983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54952155109565487679935637 2575882270760882234996983)
          ·
            refine ⟨3863823406141323352495475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575882270760882234996983 3863823406141323352495475)
            ·
              refine ⟨5795735109211985028743213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863823406141323352495475 5795735109211985028743213)
              ·
                refine ⟨2173400665954494385778705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5795735109211985028743213 2173400665954494385778705)
                ·
                  refine ⟨1630050499465870789334029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173400665954494385778705 1630050499465870789334029)
                  ·
                    refine ⟨611268937299701546000261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630050499465870789334029 611268937299701546000261)
                    ·
                      rfl

theorem cell22_1785663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_1785663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785663 prefixEnd_1785663 := by exact prefixLift 1785663
  have htrace : WordTrace (prefixWord ++ tailWord_1785663) baseStart_1785663 baseEnd_1785663 := by
    simpa [prefixWord, tailWord_1785663, baseEnd_1785663] using wordTrace_append hprefix tailTrace_1785663
  have hstable : (prefixWord ++ tailWord_1785663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785663).length < 2 ^ (prefixWord ++ tailWord_1785663).sum := by decide
  have hdescent : baseEnd_1785663 < baseStart_1785663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785749 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 8]
def baseStart_1785749 : Nat := 118140960795 + 1785749 * 2 ^ 59
def prefixEnd_1785749 : Nat := 4983230072969 + 3 ^ 40 * 1785749 * 2
def baseEnd_1785749 : Nat := 203766125619075329449999

theorem tailTrace_1785749 : CollatzResearch.WordTrace tailWord_1785749 prefixEnd_1785749 203766125619075329449999 := by
  unfold tailWord_1785749
  simp only [CollatzResearch.WordTrace]
  refine ⟨65131616807543829493480301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43421077871695886328986867 65131616807543829493480301)
  ·
    refine ⟨24424356302828936060055113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65131616807543829493480301 24424356302828936060055113)
    ·
      refine ⟨18318267227121702045041335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24424356302828936060055113 18318267227121702045041335)
      ·
        refine ⟨27477400840682553067562003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18318267227121702045041335 27477400840682553067562003)
        ·
          refine ⟨41216101261023829601343005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27477400840682553067562003 41216101261023829601343005)
          ·
            refine ⟨15456037972883936100503627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41216101261023829601343005 15456037972883936100503627)
            ·
              refine ⟨23184056959325904150755441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456037972883936100503627 23184056959325904150755441)
              ·
                refine ⟨17388042719494428113066581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23184056959325904150755441 17388042719494428113066581)
                ·
                  refine ⟨203766125619075329449999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17388042719494428113066581 203766125619075329449999)
                  ·
                    rfl

theorem cell22_1785749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_1785749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785749 prefixEnd_1785749 := by exact prefixLift 1785749
  have htrace : WordTrace (prefixWord ++ tailWord_1785749) baseStart_1785749 baseEnd_1785749 := by
    simpa [prefixWord, tailWord_1785749, baseEnd_1785749] using wordTrace_append hprefix tailTrace_1785749
  have hstable : (prefixWord ++ tailWord_1785749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785749).length < 2 ^ (prefixWord ++ tailWord_1785749).sum := by decide
  have hdescent : baseEnd_1785749 < baseStart_1785749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785779 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_1785779 : Nat := 118140960795 + 1785779 * 2 ^ 59
def prefixEnd_1785779 : Nat := 4983230072969 + 3 ^ 40 * 1785779 * 2
def baseEnd_1785779 : Nat := 611308646470315910099905

theorem tailTrace_1785779 : CollatzResearch.WordTrace tailWord_1785779 prefixEnd_1785779 611308646470315910099905 := by
  unfold tailWord_1785779
  simp only [CollatzResearch.WordTrace]
  refine ⟨65132710997435144617072391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43421807331623429744714927 65132710997435144617072391)
  ·
    refine ⟨97699066496152716925608587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65132710997435144617072391 97699066496152716925608587)
    ·
      refine ⟨146548599744229075388412881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97699066496152716925608587 146548599744229075388412881)
      ·
        refine ⟨109911449808171806541309661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146548599744229075388412881 109911449808171806541309661)
        ·
          refine ⟨41216793678064427452991123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109911449808171806541309661 41216793678064427452991123)
          ·
            refine ⟨61825190517096641179486685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41216793678064427452991123 61825190517096641179486685)
            ·
              refine ⟨23184446443911240442307507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61825190517096641179486685 23184446443911240442307507)
              ·
                refine ⟨34776669665866860663461261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23184446443911240442307507 34776669665866860663461261)
                ·
                  refine ⟨13041251124700072748797973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34776669665866860663461261 13041251124700072748797973)
                  ·
                    refine ⟨611308646470315910099905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13041251124700072748797973 611308646470315910099905)
                    ·
                      rfl

theorem cell22_1785779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_1785779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785779 prefixEnd_1785779 := by exact prefixLift 1785779
  have htrace : WordTrace (prefixWord ++ tailWord_1785779) baseStart_1785779 baseEnd_1785779 := by
    simpa [prefixWord, tailWord_1785779, baseEnd_1785779] using wordTrace_append hprefix tailTrace_1785779
  have hstable : (prefixWord ++ tailWord_1785779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785779).length < 2 ^ (prefixWord ++ tailWord_1785779).sum := by decide
  have hdescent : baseEnd_1785779 < baseStart_1785779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785800 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_1785800 : Nat := 118140960795 + 1785800 * 2 ^ 59
def prefixEnd_1785800 : Nat := 4983230072969 + 3 ^ 40 * 1785800 * 2
def baseEnd_1785800 : Nat := 203771945066492951774947

theorem tailTrace_1785800 : CollatzResearch.WordTrace tailWord_1785800 prefixEnd_1785800 203771945066492951774947 := by
  unfold tailWord_1785800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32566738465179532601793427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43422317953572710135724569 32566738465179532601793427)
  ·
    refine ⟨48850107697769298902690141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32566738465179532601793427 48850107697769298902690141)
    ·
      refine ⟨18318790386663487088508803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48850107697769298902690141 18318790386663487088508803)
      ·
        refine ⟨27478185579995230632763205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18318790386663487088508803 27478185579995230632763205)
        ·
          refine ⟨5152159796249105743643101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27478185579995230632763205 5152159796249105743643101)
          ·
            refine ⟨1932059923593414653866163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5152159796249105743643101 1932059923593414653866163)
            ·
              refine ⟨2898089885390121980799245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932059923593414653866163 2898089885390121980799245)
              ·
                refine ⟨1086783707021295742799717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2898089885390121980799245 1086783707021295742799717)
                ·
                  refine ⟨203771945066492951774947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086783707021295742799717 203771945066492951774947)
                  ·
                    rfl

theorem cell22_1785800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_1785800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785800 prefixEnd_1785800 := by exact prefixLift 1785800
  have htrace : WordTrace (prefixWord ++ tailWord_1785800) baseStart_1785800 baseEnd_1785800 := by
    simpa [prefixWord, tailWord_1785800, baseEnd_1785800] using wordTrace_append hprefix tailTrace_1785800
  have hstable : (prefixWord ++ tailWord_1785800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785800).length < 2 ^ (prefixWord ++ tailWord_1785800).sum := by decide
  have hdescent : baseEnd_1785800 < baseStart_1785800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785813 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1785813 : Nat := 118140960795 + 1785813 * 2 ^ 59
def prefixEnd_1785813 : Nat := 4983230072969 + 3 ^ 40 * 1785813 * 2
def baseEnd_1785813 : Nat := 611320285365151154749801

theorem tailTrace_1785813 : CollatzResearch.WordTrace tailWord_1785813 prefixEnd_1785813 611320285365151154749801 := by
  unfold tailWord_1785813
  simp only [CollatzResearch.WordTrace]
  refine ⟨65133951079311968423810093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43422634052874645615873395 65133951079311968423810093)
  ·
    refine ⟨24425231654741988158928785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65133951079311968423810093 24425231654741988158928785)
    ·
      refine ⟨18318923741056491119196589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24425231654741988158928785 18318923741056491119196589)
      ·
        refine ⟨6869596402896184169698721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18318923741056491119196589 6869596402896184169698721)
        ·
          refine ⟨5152197302172138127274041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6869596402896184169698721 5152197302172138127274041)
          ·
            refine ⟨3864147976629103595455531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152197302172138127274041 3864147976629103595455531)
            ·
              refine ⟨5796221964943655393183297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864147976629103595455531 5796221964943655393183297)
              ·
                refine ⟨4347166473707741544887473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796221964943655393183297 4347166473707741544887473)
                ·
                  refine ⟨3260374855280806158665605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347166473707741544887473 3260374855280806158665605)
                  ·
                    refine ⟨611320285365151154749801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260374855280806158665605 611320285365151154749801)
                    ·
                      rfl

theorem cell22_1785813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1785813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785813 prefixEnd_1785813 := by exact prefixLift 1785813
  have htrace : WordTrace (prefixWord ++ tailWord_1785813) baseStart_1785813 baseEnd_1785813 := by
    simpa [prefixWord, tailWord_1785813, baseEnd_1785813] using wordTrace_append hprefix tailTrace_1785813
  have hstable : (prefixWord ++ tailWord_1785813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785813).length < 2 ^ (prefixWord ++ tailWord_1785813).sum := by decide
  have hdescent : baseEnd_1785813 < baseStart_1785813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785862 : List Nat := [6, 2, 1, 2, 1, 10]
def baseStart_1785862 : Nat := 118140960795 + 1785862 * 2 ^ 59
def prefixEnd_1785862 : Nat := 4983230072969 + 3 ^ 40 * 1785862 * 2
def baseEnd_1785862 : Nat := 7547371099586806916971

theorem tailTrace_1785862 : CollatzResearch.WordTrace tailWord_1785862 prefixEnd_1785862 7547371099586806916971 := by
  unfold tailWord_1785862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035491820504201556010745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43423825504089633194895893 2035491820504201556010745)
  ·
    refine ⟨1526618865378151167008059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2035491820504201556010745 1526618865378151167008059)
    ·
      refine ⟨2289928298067226750512089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526618865378151167008059 2289928298067226750512089)
      ·
        refine ⟨1717446223550420062884067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289928298067226750512089 1717446223550420062884067)
        ·
          refine ⟨2576169335325630094326101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717446223550420062884067 2576169335325630094326101)
          ·
            refine ⟨7547371099586806916971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2576169335325630094326101 7547371099586806916971)
            ·
              rfl

theorem cell22_1785862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 10].length) (baseStart_1785862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785862 prefixEnd_1785862 := by exact prefixLift 1785862
  have htrace : WordTrace (prefixWord ++ tailWord_1785862) baseStart_1785862 baseEnd_1785862 := by
    simpa [prefixWord, tailWord_1785862, baseEnd_1785862] using wordTrace_append hprefix tailTrace_1785862
  have hstable : (prefixWord ++ tailWord_1785862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785862).length < 2 ^ (prefixWord ++ tailWord_1785862).sum := by decide
  have hdescent : baseEnd_1785862 < baseStart_1785862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785877 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1785877 : Nat := 118140960795 + 1785877 * 2 ^ 59
def prefixEnd_1785877 : Nat := 4983230072969 + 3 ^ 40 * 1785877 * 2
def baseEnd_1785877 : Nat := 611342193873076321149605

theorem tailTrace_1785877 : CollatzResearch.WordTrace tailWord_1785877 prefixEnd_1785877 611342193873076321149605 := by
  unfold tailWord_1785877
  simp only [CollatzResearch.WordTrace]
  refine ⟨65136285351080107354139885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43424190234053404902759923 65136285351080107354139885)
  ·
    refine ⟨24426107006655040257802457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65136285351080107354139885 24426107006655040257802457)
    ·
      refine ⟨18319580254991280193351843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24426107006655040257802457 18319580254991280193351843)
      ·
        refine ⟨27479370382486920290027765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18319580254991280193351843 27479370382486920290027765)
        ·
          refine ⟨2576190973358148777190103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27479370382486920290027765 2576190973358148777190103)
          ·
            refine ⟨3864286460037223165785155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576190973358148777190103 3864286460037223165785155)
            ·
              refine ⟨5796429690055834748677733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864286460037223165785155 5796429690055834748677733)
              ·
                refine ⟨1086830566885469015377075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5796429690055834748677733 1086830566885469015377075)
                ·
                  refine ⟨1630245850328203523065613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086830566885469015377075 1630245850328203523065613)
                  ·
                    refine ⟨611342193873076321149605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630245850328203523065613 611342193873076321149605)
                    ·
                      rfl

theorem cell22_1785877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1785877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785877 prefixEnd_1785877 := by exact prefixLift 1785877
  have htrace : WordTrace (prefixWord ++ tailWord_1785877) baseStart_1785877 baseEnd_1785877 := by
    simpa [prefixWord, tailWord_1785877, baseEnd_1785877] using wordTrace_append hprefix tailTrace_1785877
  have hstable : (prefixWord ++ tailWord_1785877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785877).length < 2 ^ (prefixWord ++ tailWord_1785877).sum := by decide
  have hdescent : baseEnd_1785877 < baseStart_1785877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785920 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_1785920 : Nat := 118140960795 + 1785920 * 2 ^ 59
def prefixEnd_1785920 : Nat := 4983230072969 + 3 ^ 40 * 1785920 * 2
def baseEnd_1785920 : Nat := 611356913651838542324473

theorem tailTrace_1785920 : CollatzResearch.WordTrace tailWord_1785920 prefixEnd_1785920 611356913651838542324473 := by
  unfold tailWord_1785920
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568926844962162848977607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43425235793282883798636809 32568926844962162848977607)
  ·
    refine ⟨48853390267443244273466411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32568926844962162848977607 48853390267443244273466411)
    ·
      refine ⟨73280085401164866410199617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48853390267443244273466411 73280085401164866410199617)
      ·
        refine ⟨54960064050873649807649713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73280085401164866410199617 54960064050873649807649713)
        ·
          refine ⟨41220048038155237355737285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54960064050873649807649713 41220048038155237355737285)
          ·
            refine ⟨7728759007154107004200741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41220048038155237355737285 7728759007154107004200741)
            ·
              refine ⟨1449142313841395063287639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7728759007154107004200741 1449142313841395063287639)
              ·
                refine ⟨2173713470762092594931459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449142313841395063287639 2173713470762092594931459)
                ·
                  refine ⟨3260570206143138892397189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173713470762092594931459 3260570206143138892397189)
                  ·
                    refine ⟨611356913651838542324473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260570206143138892397189 611356913651838542324473)
                    ·
                      rfl

theorem cell22_1785920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_1785920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785920 prefixEnd_1785920 := by exact prefixLift 1785920
  have htrace : WordTrace (prefixWord ++ tailWord_1785920) baseStart_1785920 baseEnd_1785920 := by
    simpa [prefixWord, tailWord_1785920, baseEnd_1785920] using wordTrace_append hprefix tailTrace_1785920
  have hstable : (prefixWord ++ tailWord_1785920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785920).length < 2 ^ (prefixWord ++ tailWord_1785920).sum := by decide
  have hdescent : baseEnd_1785920 < baseStart_1785920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785946 : List Nat := [3, 1, 1, 2, 1, 1, 4, 9]
def baseStart_1785946 : Nat := 118140960795 + 1785946 * 2 ^ 59
def prefixEnd_1785946 : Nat := 4983230072969 + 3 ^ 40 * 1785946 * 2
def baseEnd_1785946 : Nat := 67929534887020349019377

theorem tailTrace_1785946 : CollatzResearch.WordTrace tailWord_1785946 prefixEnd_1785946 67929534887020349019377 := by
  unfold tailWord_1785946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284700496957533034600423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43425867991886754758934461 16284700496957533034600423)
  ·
    refine ⟨24427050745436299551900635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16284700496957533034600423 24427050745436299551900635)
    ·
      refine ⟨36640576118154449327850953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427050745436299551900635 36640576118154449327850953)
      ·
        refine ⟨27480432088615836995888215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36640576118154449327850953 27480432088615836995888215)
        ·
          refine ⟨41220648132923755493832323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27480432088615836995888215 41220648132923755493832323)
          ·
            refine ⟨61830972199385633240748485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41220648132923755493832323 61830972199385633240748485)
            ·
              refine ⟨11593307287384806232640341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61830972199385633240748485 11593307287384806232640341)
              ·
                refine ⟨67929534887020349019377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11593307287384806232640341 67929534887020349019377)
                ·
                  rfl

theorem cell22_1785946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_1785946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785946 prefixEnd_1785946 := by exact prefixLift 1785946
  have htrace : WordTrace (prefixWord ++ tailWord_1785946) baseStart_1785946 baseEnd_1785946 := by
    simpa [prefixWord, tailWord_1785946, baseEnd_1785946] using wordTrace_append hprefix tailTrace_1785946
  have hstable : (prefixWord ++ tailWord_1785946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785946).length < 2 ^ (prefixWord ++ tailWord_1785946).sum := by decide
  have hdescent : baseEnd_1785946 < baseStart_1785946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785948 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1785948 : Nat := 118140960795 + 1785948 * 2 ^ 59
def prefixEnd_1785948 : Nat := 4983230072969 + 3 ^ 40 * 1785948 * 2
def baseEnd_1785948 : Nat := 611366498624055802624387

theorem tailTrace_1785948 : CollatzResearch.WordTrace tailWord_1785948 prefixEnd_1785948 611366498624055802624387 := by
  unfold tailWord_1785948
  simp only [CollatzResearch.WordTrace]
  refine ⟨32569437466911443239987249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43425916622548590986649665 32569437466911443239987249)
  ·
    refine ⟨24427078100183582429990437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32569437466911443239987249 24427078100183582429990437)
    ·
      refine ⟨4580077143784421705623207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24427078100183582429990437 4580077143784421705623207)
      ·
        refine ⟨6870115715676632558434811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4580077143784421705623207 6870115715676632558434811)
        ·
          refine ⟨10305173573514948837652217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870115715676632558434811 10305173573514948837652217)
          ·
            refine ⟨7728880180136211628239163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305173573514948837652217 7728880180136211628239163)
            ·
              refine ⟨11593320270204317442358745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728880180136211628239163 11593320270204317442358745)
              ·
                refine ⟨8694990202653238081769059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593320270204317442358745 8694990202653238081769059)
                ·
                  refine ⟨13042485303979857122653589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8694990202653238081769059 13042485303979857122653589)
                  ·
                    refine ⟨611366498624055802624387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13042485303979857122653589 611366498624055802624387)
                    ·
                      rfl

theorem cell22_1785948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1785948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785948 prefixEnd_1785948 := by exact prefixLift 1785948
  have htrace : WordTrace (prefixWord ++ tailWord_1785948) baseStart_1785948 baseEnd_1785948 := by
    simpa [prefixWord, tailWord_1785948, baseEnd_1785948] using wordTrace_append hprefix tailTrace_1785948
  have hstable : (prefixWord ++ tailWord_1785948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785948).length < 2 ^ (prefixWord ++ tailWord_1785948).sum := by decide
  have hdescent : baseEnd_1785948 < baseStart_1785948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785961 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1785961 : Nat := 118140960795 + 1785961 * 2 ^ 59
def prefixEnd_1785961 : Nat := 4983230072969 + 3 ^ 40 * 1785961 * 2
def baseEnd_1785961 : Nat := 611370948789728102049347

theorem tailTrace_1785961 : CollatzResearch.WordTrace tailWord_1785961 prefixEnd_1785961 611370948789728102049347 := by
  unfold tailWord_1785961
  simp only [CollatzResearch.WordTrace]
  refine ⟨65139349082775789700197737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43426232721850526466798491 65139349082775789700197737)
  ·
    refine ⟨48854511812081842275148303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65139349082775789700197737 48854511812081842275148303)
    ·
      refine ⟨73281767718122763412722455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48854511812081842275148303 73281767718122763412722455)
      ·
        refine ⟨109922651577184145119083683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73281767718122763412722455 109922651577184145119083683)
        ·
          refine ⟨164883977365776217678625525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109922651577184145119083683 164883977365776217678625525)
          ·
            refine ⟨15457872878041520407371143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164883977365776217678625525 15457872878041520407371143)
            ·
              refine ⟨23186809317062280611056715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457872878041520407371143 23186809317062280611056715)
              ·
                refine ⟨34780213975593420916585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23186809317062280611056715 34780213975593420916585073)
                ·
                  refine ⟨26085160481695065687438805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34780213975593420916585073 26085160481695065687438805)
                  ·
                    refine ⟨611370948789728102049347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26085160481695065687438805 611370948789728102049347)
                    ·
                      rfl

theorem cell22_1785961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1785961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785961 prefixEnd_1785961 := by exact prefixLift 1785961
  have htrace : WordTrace (prefixWord ++ tailWord_1785961) baseStart_1785961 baseEnd_1785961 := by
    simpa [prefixWord, tailWord_1785961, baseEnd_1785961] using wordTrace_append hprefix tailTrace_1785961
  have hstable : (prefixWord ++ tailWord_1785961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785961).length < 2 ^ (prefixWord ++ tailWord_1785961).sum := by decide
  have hdescent : baseEnd_1785961 < baseStart_1785961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785976 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_1785976 : Nat := 118140960795 + 1785976 * 2 ^ 59
def prefixEnd_1785976 : Nat := 4983230072969 + 3 ^ 40 * 1785976 * 2
def baseEnd_1785976 : Nat := 611376083596273062924301

theorem tailTrace_1785976 : CollatzResearch.WordTrace tailWord_1785976 prefixEnd_1785976 611376083596273062924301 := by
  unfold tailWord_1785976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32569948088860723630996891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43426597451814298174662521 32569948088860723630996891)
  ·
    refine ⟨48854922133291085446495337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32569948088860723630996891 48854922133291085446495337)
    ·
      refine ⟨36641191599968314084871503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48854922133291085446495337 36641191599968314084871503)
      ·
        refine ⟨54961787399952471127307255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36641191599968314084871503 54961787399952471127307255)
        ·
          refine ⟨82442681099928706690960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54961787399952471127307255 82442681099928706690960883)
          ·
            refine ⟨123664021649893060036441325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82442681099928706690960883 123664021649893060036441325)
            ·
              refine ⟨46374008118709897513665497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123664021649893060036441325 46374008118709897513665497)
              ·
                refine ⟨34780506089032423135249123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46374008118709897513665497 34780506089032423135249123)
                ·
                  refine ⟨52170759133548634702873685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34780506089032423135249123 52170759133548634702873685)
                  ·
                    refine ⟨611376083596273062924301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52170759133548634702873685 611376083596273062924301)
                    ·
                      rfl

theorem cell22_1785976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_1785976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1785976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1785976 prefixEnd_1785976 := by exact prefixLift 1785976
  have htrace : WordTrace (prefixWord ++ tailWord_1785976) baseStart_1785976 baseEnd_1785976 := by
    simpa [prefixWord, tailWord_1785976, baseEnd_1785976] using wordTrace_append hprefix tailTrace_1785976
  have hstable : (prefixWord ++ tailWord_1785976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785976).length < 2 ^ (prefixWord ++ tailWord_1785976).sum := by decide
  have hdescent : baseEnd_1785976 < baseStart_1785976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786085 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1786085 : Nat := 118140960795 + 1786085 * 2 ^ 59
def prefixEnd_1786085 : Nat := 4983230072969 + 3 ^ 40 * 1786085 * 2
def baseEnd_1786085 : Nat := 611413396523833111948967

theorem tailTrace_1786085 : CollatzResearch.WordTrace tailWord_1786085 prefixEnd_1786085 611413396523833111948967 := by
  unfold tailWord_1786085
  simp only [CollatzResearch.WordTrace]
  refine ⟨65143871734326558877711709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43429247822884372585141139 65143871734326558877711709)
  ·
    refine ⟨24428951900372459579141891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65143871734326558877711709 24428951900372459579141891)
    ·
      refine ⟨36643427850558689368712837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24428951900372459579141891 36643427850558689368712837)
      ·
        refine ⟨6870642721979754256633657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36643427850558689368712837 6870642721979754256633657)
        ·
          refine ⟨5152982041484815692475243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6870642721979754256633657 5152982041484815692475243)
          ·
            refine ⟨7729473062227223538712865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152982041484815692475243 7729473062227223538712865)
            ·
              refine ⟨5797104796670417654034649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7729473062227223538712865 5797104796670417654034649)
              ·
                refine ⟨4347828597502813240525987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797104796670417654034649 4347828597502813240525987)
                ·
                  refine ⟨6521742896254219860788981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347828597502813240525987 6521742896254219860788981)
                  ·
                    refine ⟨611413396523833111948967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6521742896254219860788981 611413396523833111948967)
                    ·
                      rfl

theorem cell22_1786085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1786085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786085 prefixEnd_1786085 := by exact prefixLift 1786085
  have htrace : WordTrace (prefixWord ++ tailWord_1786085) baseStart_1786085 baseEnd_1786085 := by
    simpa [prefixWord, tailWord_1786085, baseEnd_1786085] using wordTrace_append hprefix tailTrace_1786085
  have hstable : (prefixWord ++ tailWord_1786085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786085).length < 2 ^ (prefixWord ++ tailWord_1786085).sum := by decide
  have hdescent : baseEnd_1786085 < baseStart_1786085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786087 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 4]
def baseStart_1786087 : Nat := 118140960795 + 1786087 * 2 ^ 59
def prefixEnd_1786087 : Nat := 4983230072969 + 3 ^ 40 * 1786087 * 2
def baseEnd_1786087 : Nat := 203804693721568591132987

theorem tailTrace_1786087 : CollatzResearch.WordTrace tailWord_1786087 prefixEnd_1786087 203804693721568591132987 := by
  unfold tailWord_1786087
  simp only [CollatzResearch.WordTrace]
  refine ⟨65143944680319313219284515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43429296453546208812856343 65143944680319313219284515)
  ·
    refine ⟨97715917020478969828926773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65143944680319313219284515 97715917020478969828926773)
    ·
      refine ⟨9160867220669903421461885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97715917020478969828926773 9160867220669903421461885)
      ·
        refine ⟨3435325207751213783048207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9160867220669903421461885 3435325207751213783048207)
        ·
          refine ⟨5152987811626820674572311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435325207751213783048207 5152987811626820674572311)
          ·
            refine ⟨7729481717440231011858467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152987811626820674572311 7729481717440231011858467)
            ·
              refine ⟨11594222576160346517787701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729481717440231011858467 11594222576160346517787701)
              ·
                refine ⟨1086958366515032486042597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11594222576160346517787701 1086958366515032486042597)
                ·
                  refine ⟨203804693721568591132987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086958366515032486042597 203804693721568591132987)
                  ·
                    rfl

theorem cell22_1786087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 4].length) (baseStart_1786087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786087 prefixEnd_1786087 := by exact prefixLift 1786087
  have htrace : WordTrace (prefixWord ++ tailWord_1786087) baseStart_1786087 baseEnd_1786087 := by
    simpa [prefixWord, tailWord_1786087, baseEnd_1786087] using wordTrace_append hprefix tailTrace_1786087
  have hstable : (prefixWord ++ tailWord_1786087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786087).length < 2 ^ (prefixWord ++ tailWord_1786087).sum := by decide
  have hdescent : baseEnd_1786087 < baseStart_1786087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786119 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1786119 : Nat := 118140960795 + 1786119 * 2 ^ 59
def prefixEnd_1786119 : Nat := 4983230072969 + 3 ^ 40 * 1786119 * 2
def baseEnd_1786119 : Nat := 611425035418668356598863

theorem tailTrace_1786119 : CollatzResearch.WordTrace tailWord_1786119 prefixEnd_1786119 611425035418668356598863 := by
  unfold tailWord_1786119
  simp only [CollatzResearch.WordTrace]
  refine ⟨65145111816203382684449411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43430074544135588456299607 65145111816203382684449411)
  ·
    refine ⟨97717667724305074026674117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65145111816203382684449411 97717667724305074026674117)
    ·
      refine ⟨18322062698307201380001397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97717667724305074026674117 18322062698307201380001397)
      ·
        refine ⟨1717693377966300129375131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18322062698307201380001397 1717693377966300129375131)
        ·
          refine ⟨2576540066949450194062697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717693377966300129375131 2576540066949450194062697)
          ·
            refine ⟨1932405050212087645547023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576540066949450194062697 1932405050212087645547023)
            ·
              refine ⟨2898607575318131468320535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932405050212087645547023 2898607575318131468320535)
              ·
                refine ⟨4347911362977197202480803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898607575318131468320535 4347911362977197202480803)
                ·
                  refine ⟨6521867044465795803721205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347911362977197202480803 6521867044465795803721205)
                  ·
                    refine ⟨611425035418668356598863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6521867044465795803721205 611425035418668356598863)
                    ·
                      rfl

theorem cell22_1786119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1786119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786119 prefixEnd_1786119 := by exact prefixLift 1786119
  have htrace : WordTrace (prefixWord ++ tailWord_1786119) baseStart_1786119 baseEnd_1786119 := by
    simpa [prefixWord, tailWord_1786119, baseEnd_1786119] using wordTrace_append hprefix tailTrace_1786119
  have hstable : (prefixWord ++ tailWord_1786119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786119).length < 2 ^ (prefixWord ++ tailWord_1786119).sum := by decide
  have hdescent : baseEnd_1786119 < baseStart_1786119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786151 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1786151 : Nat := 118140960795 + 1786151 * 2 ^ 59
def prefixEnd_1786151 : Nat := 4983230072969 + 3 ^ 40 * 1786151 * 2
def baseEnd_1786151 : Nat := 611435989672630939798765

theorem tailTrace_1786151 : CollatzResearch.WordTrace tailWord_1786151 prefixEnd_1786151 611435989672630939798765 := by
  unfold tailWord_1786151
  simp only [CollatzResearch.WordTrace]
  refine ⟨65146278952087452149614307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43430852634724968099742871 65146278952087452149614307)
  ·
    refine ⟨97719418428131178224421461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65146278952087452149614307 97719418428131178224421461)
    ·
      refine ⟨1145149434704662244817439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 97719418428131178224421461 1145149434704662244817439)
      ·
        refine ⟨1717724152056993367226159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145149434704662244817439 1717724152056993367226159)
        ·
          refine ⟨2576586228085490050839239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717724152056993367226159 2576586228085490050839239)
          ·
            refine ⟨3864879342128235076258859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576586228085490050839239 3864879342128235076258859)
            ·
              refine ⟨5797319013192352614388289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864879342128235076258859 5797319013192352614388289)
              ·
                refine ⟨4347989259894264460791217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797319013192352614388289 4347989259894264460791217)
                ·
                  refine ⟨3260991944920698345593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347989259894264460791217 3260991944920698345593413)
                  ·
                    refine ⟨611435989672630939798765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260991944920698345593413 611435989672630939798765)
                    ·
                      rfl

theorem cell22_1786151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1786151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786151 prefixEnd_1786151 := by exact prefixLift 1786151
  have htrace : WordTrace (prefixWord ++ tailWord_1786151) baseStart_1786151 baseEnd_1786151 := by
    simpa [prefixWord, tailWord_1786151, baseEnd_1786151] using wordTrace_append hprefix tailTrace_1786151
  have hstable : (prefixWord ++ tailWord_1786151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786151).length < 2 ^ (prefixWord ++ tailWord_1786151).sum := by decide
  have hdescent : baseEnd_1786151 < baseStart_1786151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786164 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1786164 : Nat := 118140960795 + 1786164 * 2 ^ 59
def prefixEnd_1786164 : Nat := 4983230072969 + 3 ^ 40 * 1786164 * 2
def baseEnd_1786164 : Nat := 611440439838303239223725

theorem tailTrace_1786164 : CollatzResearch.WordTrace tailWord_1786164 prefixEnd_1786164 611440439838303239223725 := by
  unfold tailWord_1786164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32573376550520177684918773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43431168734026903579891697 32573376550520177684918773)
  ·
    refine ⟨3053754051611266657961135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32573376550520177684918773 3053754051611266657961135)
    ·
      refine ⟨4580631077416899986941703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053754051611266657961135 4580631077416899986941703)
      ·
        refine ⟨6870946616125349980412555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4580631077416899986941703 6870946616125349980412555)
        ·
          refine ⟨10306419924188024970618833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870946616125349980412555 10306419924188024970618833)
          ·
            refine ⟨7729814943141018727964125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10306419924188024970618833 7729814943141018727964125)
            ·
              refine ⟨2898680603677882022986547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7729814943141018727964125 2898680603677882022986547)
              ·
                refine ⟨4348020905516823034479821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898680603677882022986547 4348020905516823034479821)
                ·
                  refine ⟨1630507839568808637929933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4348020905516823034479821 1630507839568808637929933)
                  ·
                    refine ⟨611440439838303239223725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630507839568808637929933 611440439838303239223725)
                    ·
                      rfl

theorem cell22_1786164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1786164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786164 prefixEnd_1786164 := by exact prefixLift 1786164
  have htrace : WordTrace (prefixWord ++ tailWord_1786164) baseStart_1786164 baseEnd_1786164 := by
    simpa [prefixWord, tailWord_1786164, baseEnd_1786164] using wordTrace_append hprefix tailTrace_1786164
  have hstable : (prefixWord ++ tailWord_1786164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786164).length < 2 ^ (prefixWord ++ tailWord_1786164).sum := by decide
  have hdescent : baseEnd_1786164 < baseStart_1786164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786237 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1786237 : Nat := 118140960795 + 1786237 * 2 ^ 59
def prefixEnd_1786237 : Nat := 4983230072969 + 3 ^ 40 * 1786237 * 2
def baseEnd_1786237 : Nat := 611465429230155382148501

theorem tailTrace_1786237 : CollatzResearch.WordTrace tailWord_1786237 prefixEnd_1786237 611465429230155382148501 := by
  unfold tailWord_1786237
  simp only [CollatzResearch.WordTrace]
  refine ⟨65149415629775888837244965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43432943753183925891496643 65149415629775888837244965)
  ·
    refine ⟨12215515430582979156983431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65149415629775888837244965 12215515430582979156983431)
    ·
      refine ⟨18323273145874468735475147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12215515430582979156983431 18323273145874468735475147)
      ·
        refine ⟨27484909718811703103212721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18323273145874468735475147 27484909718811703103212721)
        ·
          refine ⟨20613682289108777327409541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27484909718811703103212721 20613682289108777327409541)
          ·
            refine ⟨3865065429207895748889289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20613682289108777327409541 3865065429207895748889289)
            ·
              refine ⟨2898799071905921811666967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865065429207895748889289 2898799071905921811666967)
              ·
                refine ⟨4348198607858882717500451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898799071905921811666967 4348198607858882717500451)
                ·
                  refine ⟨6522297911788324076250677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348198607858882717500451 6522297911788324076250677)
                  ·
                    refine ⟨611465429230155382148501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6522297911788324076250677 611465429230155382148501)
                    ·
                      rfl

theorem cell22_1786237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1786237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786237 prefixEnd_1786237 := by exact prefixLift 1786237
  have htrace : WordTrace (prefixWord ++ tailWord_1786237) baseStart_1786237 baseEnd_1786237 := by
    simpa [prefixWord, tailWord_1786237, baseEnd_1786237] using wordTrace_append hprefix tailTrace_1786237
  have hstable : (prefixWord ++ tailWord_1786237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786237).length < 2 ^ (prefixWord ++ tailWord_1786237).sum := by decide
  have hdescent : baseEnd_1786237 < baseStart_1786237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786252 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_1786252 : Nat := 118140960795 + 1786252 * 2 ^ 59
def prefixEnd_1786252 : Nat := 4983230072969 + 3 ^ 40 * 1786252 * 2
def baseEnd_1786252 : Nat := 611470564036700343023455

theorem tailTrace_1786252 : CollatzResearch.WordTrace tailWord_1786252 prefixEnd_1786252 611470564036700343023455 := by
  unfold tailWord_1786252
  simp only [CollatzResearch.WordTrace]
  refine ⟨32574981362360773199520505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43433308483147697599360673 32574981362360773199520505)
  ·
    refine ⟨24431236021770579899640379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32574981362360773199520505 24431236021770579899640379)
    ·
      refine ⟨36646854032655869849460569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24431236021770579899640379 36646854032655869849460569)
      ·
        refine ⟨27485140524491902387095427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36646854032655869849460569 27485140524491902387095427)
        ·
          refine ⟨41227710786737853580643141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27485140524491902387095427 41227710786737853580643141)
          ·
            refine ⟨7730195772513347546370589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41227710786737853580643141 7730195772513347546370589)
            ·
              refine ⟨2898823414692505329888971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7730195772513347546370589 2898823414692505329888971)
              ·
                refine ⟨4348235122038757994833457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898823414692505329888971 4348235122038757994833457)
                ·
                  refine ⟨3261176341529068496125093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348235122038757994833457 3261176341529068496125093)
                  ·
                    refine ⟨611470564036700343023455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261176341529068496125093 611470564036700343023455)
                    ·
                      rfl

theorem cell22_1786252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_1786252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786252 prefixEnd_1786252 := by exact prefixLift 1786252
  have htrace : WordTrace (prefixWord ++ tailWord_1786252) baseStart_1786252 baseEnd_1786252 := by
    simpa [prefixWord, tailWord_1786252, baseEnd_1786252] using wordTrace_append hprefix tailTrace_1786252
  have hstable : (prefixWord ++ tailWord_1786252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786252).length < 2 ^ (prefixWord ++ tailWord_1786252).sum := by decide
  have hdescent : baseEnd_1786252 < baseStart_1786252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786333 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1786333 : Nat := 118140960795 + 1786333 * 2 ^ 59
def prefixEnd_1786333 : Nat := 4983230072969 + 3 ^ 40 * 1786333 * 2
def baseEnd_1786333 : Nat := 611498291992043131748207

theorem tailTrace_1786333 : CollatzResearch.WordTrace tailWord_1786333 prefixEnd_1786333 611498291992043131748207 := by
  unfold tailWord_1786333
  simp only [CollatzResearch.WordTrace]
  refine ⟨65152917037428097232739653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43435278024952064821826435 65152917037428097232739653)
  ·
    refine ⟨12216171944517768231138685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65152917037428097232739653 12216171944517768231138685)
    ·
      refine ⟨4581064479194163086677007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12216171944517768231138685 4581064479194163086677007)
      ·
        refine ⟨6871596718791244630015511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581064479194163086677007 6871596718791244630015511)
        ·
          refine ⟨10307395078186866945023267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871596718791244630015511 10307395078186866945023267)
          ·
            refine ⟨15461092617280300417534901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307395078186866945023267 15461092617280300417534901)
            ·
              refine ⟨1449477432870028164143897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15461092617280300417534901 1449477432870028164143897)
              ·
                refine ⟨1087108074652521123107923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449477432870028164143897 1087108074652521123107923)
                ·
                  refine ⟨1630662111978781684661885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087108074652521123107923 1630662111978781684661885)
                  ·
                    refine ⟨611498291992043131748207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630662111978781684661885 611498291992043131748207)
                    ·
                      rfl

theorem cell22_1786333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1786333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786333 prefixEnd_1786333 := by exact prefixLift 1786333
  have htrace : WordTrace (prefixWord ++ tailWord_1786333) baseStart_1786333 baseEnd_1786333 := by
    simpa [prefixWord, tailWord_1786333, baseEnd_1786333] using wordTrace_append hprefix tailTrace_1786333
  have hstable : (prefixWord ++ tailWord_1786333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786333).length < 2 ^ (prefixWord ++ tailWord_1786333).sum := by decide
  have hdescent : baseEnd_1786333 < baseStart_1786333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786346 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_1786346 : Nat := 118140960795 + 1786346 * 2 ^ 59
def prefixEnd_1786346 : Nat := 4983230072969 + 3 ^ 40 * 1786346 * 2
def baseEnd_1786346 : Nat := 203834247385905143724389

theorem tailTrace_1786346 : CollatzResearch.WordTrace tailWord_1786346 prefixEnd_1786346 203834247385905143724389 := by
  unfold tailWord_1786346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288347796595250113240723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43435594124254000301975261 16288347796595250113240723)
  ·
    refine ⟨24432521694892875169861085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16288347796595250113240723 24432521694892875169861085)
    ·
      refine ⟨9162195635584828188697907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24432521694892875169861085 9162195635584828188697907)
      ·
        refine ⟨13743293453377242283046861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9162195635584828188697907 13743293453377242283046861)
        ·
          refine ⟨5153735045016465856142573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13743293453377242283046861 5153735045016465856142573)
          ·
            refine ⟨1932650641881174696053465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5153735045016465856142573 1932650641881174696053465)
            ·
              refine ⟨1449487981410881022040099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932650641881174696053465 1449487981410881022040099)
              ·
                refine ⟨2174231972116321533060149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449487981410881022040099 2174231972116321533060149)
                ·
                  refine ⟨203834247385905143724389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2174231972116321533060149 203834247385905143724389)
                  ·
                    rfl

theorem cell22_1786346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_1786346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786346 prefixEnd_1786346 := by exact prefixLift 1786346
  have htrace : WordTrace (prefixWord ++ tailWord_1786346) baseStart_1786346 baseEnd_1786346 := by
    simpa [prefixWord, tailWord_1786346, baseEnd_1786346] using wordTrace_append hprefix tailTrace_1786346
  have hstable : (prefixWord ++ tailWord_1786346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786346).length < 2 ^ (prefixWord ++ tailWord_1786346).sum := by decide
  have hdescent : baseEnd_1786346 < baseStart_1786346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786387 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_1786387 : Nat := 118140960795 + 1786387 * 2 ^ 59
def prefixEnd_1786387 : Nat := 4983230072969 + 3 ^ 40 * 1786387 * 2
def baseEnd_1786387 : Nat := 611516777295604990898041

theorem tailTrace_1786387 : CollatzResearch.WordTrace tailWord_1786387 prefixEnd_1786387 611516777295604990898041 := by
  unfold tailWord_1786387
  simp only [CollatzResearch.WordTrace]
  refine ⟨65154886579232464455205415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43436591052821642970136943 65154886579232464455205415)
  ·
    refine ⟨97732329868848696682808123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65154886579232464455205415 97732329868848696682808123)
    ·
      refine ⟨146598494803273045024212185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97732329868848696682808123 146598494803273045024212185)
      ·
        refine ⟨109948871102454783768159139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146598494803273045024212185 109948871102454783768159139)
        ·
          refine ⟨164923306653682175652238709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109948871102454783768159139 164923306653682175652238709)
          ·
            refine ⟨15461559998782703967397379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164923306653682175652238709 15461559998782703967397379)
            ·
              refine ⟨23192339998174055951096069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461559998782703967397379 23192339998174055951096069)
              ·
                refine ⟨4348563749657635490830513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23192339998174055951096069 4348563749657635490830513)
                ·
                  refine ⟨3261422812243226618122885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348563749657635490830513 3261422812243226618122885)
                  ·
                    refine ⟨611516777295604990898041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261422812243226618122885 611516777295604990898041)
                    ·
                      rfl

theorem cell22_1786387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_1786387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786387 prefixEnd_1786387 := by exact prefixLift 1786387
  have htrace : WordTrace (prefixWord ++ tailWord_1786387) baseStart_1786387 baseEnd_1786387 := by
    simpa [prefixWord, tailWord_1786387, baseEnd_1786387] using wordTrace_append hprefix tailTrace_1786387
  have hstable : (prefixWord ++ tailWord_1786387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786387).length < 2 ^ (prefixWord ++ tailWord_1786387).sum := by decide
  have hdescent : baseEnd_1786387 < baseStart_1786387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786492 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_1786492 : Nat := 118140960795 + 1786492 * 2 ^ 59
def prefixEnd_1786492 : Nat := 4983230072969 + 3 ^ 40 * 1786492 * 2
def baseEnd_1786492 : Nat := 203850906980473239007573

theorem tailTrace_1786492 : CollatzResearch.WordTrace tailWord_1786492 prefixEnd_1786492 203850906980473239007573 := by
  unfold tailWord_1786492
  simp only [CollatzResearch.WordTrace]
  refine ⟨32579358121926033693888865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43439144162568044925185153 32579358121926033693888865)
  ·
    refine ⟨24434518591444525270416649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32579358121926033693888865 24434518591444525270416649)
    ·
      refine ⟨18325888943583393952812487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24434518591444525270416649 18325888943583393952812487)
      ·
        refine ⟨27488833415375090929218731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325888943583393952812487 27488833415375090929218731)
        ·
          refine ⟨41233250123062636393828097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27488833415375090929218731 41233250123062636393828097)
          ·
            refine ⟨30924937592296977295371073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41233250123062636393828097 30924937592296977295371073)
            ·
              refine ⟨23193703194222732971528305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30924937592296977295371073 23193703194222732971528305)
              ·
                refine ⟨17395277395667049728646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23193703194222732971528305 17395277395667049728646229)
                ·
                  refine ⟨203850906980473239007573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17395277395667049728646229 203850906980473239007573)
                  ·
                    rfl

theorem cell22_1786492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_1786492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786492 prefixEnd_1786492 := by exact prefixLift 1786492
  have htrace : WordTrace (prefixWord ++ tailWord_1786492) baseStart_1786492 baseEnd_1786492 := by
    simpa [prefixWord, tailWord_1786492, baseEnd_1786492] using wordTrace_append hprefix tailTrace_1786492
  have hstable : (prefixWord ++ tailWord_1786492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786492).length < 2 ^ (prefixWord ++ tailWord_1786492).sum := by decide
  have hdescent : baseEnd_1786492 < baseStart_1786492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786507 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_1786507 : Nat := 118140960795 + 1786507 * 2 ^ 59
def prefixEnd_1786507 : Nat := 4983230072969 + 3 ^ 40 * 1786507 * 2
def baseEnd_1786507 : Nat := 611557855747964677897673

theorem tailTrace_1786507 : CollatzResearch.WordTrace tailWord_1786507 prefixEnd_1786507 611557855747964677897673 := by
  unfold tailWord_1786507
  simp only [CollatzResearch.WordTrace]
  refine ⟨65159263338797724949573775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43439508892531816633049183 65159263338797724949573775)
  ·
    refine ⟨97738895008196587424360663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65159263338797724949573775 97738895008196587424360663)
    ·
      refine ⟨146608342512294881136540995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97738895008196587424360663 146608342512294881136540995)
      ·
        refine ⟨219912513768442321704811493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146608342512294881136540995 219912513768442321704811493)
        ·
          refine ⟨41233596331582935319652155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219912513768442321704811493 41233596331582935319652155)
          ·
            refine ⟨61850394497374402979478233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41233596331582935319652155 61850394497374402979478233)
            ·
              refine ⟨46387795873030802234608675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61850394497374402979478233 46387795873030802234608675)
              ·
                refine ⟨69581693809546203351913013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46387795873030802234608675 69581693809546203351913013)
                ·
                  refine ⟨6523283794644956564241845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69581693809546203351913013 6523283794644956564241845)
                  ·
                    refine ⟨611557855747964677897673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6523283794644956564241845 611557855747964677897673)
                    ·
                      rfl

theorem cell22_1786507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_1786507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786507 prefixEnd_1786507 := by exact prefixLift 1786507
  have htrace : WordTrace (prefixWord ++ tailWord_1786507) baseStart_1786507 baseEnd_1786507 := by
    simpa [prefixWord, tailWord_1786507, baseEnd_1786507] using wordTrace_append hprefix tailTrace_1786507
  have hstable : (prefixWord ++ tailWord_1786507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786507).length < 2 ^ (prefixWord ++ tailWord_1786507).sum := by decide
  have hdescent : baseEnd_1786507 < baseStart_1786507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786528 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_1786528 : Nat := 118140960795 + 1786528 * 2 ^ 59
def prefixEnd_1786528 : Nat := 4983230072969 + 3 ^ 40 * 1786528 * 2
def baseEnd_1786528 : Nat := 611565044477127623122609

theorem tailTrace_1786528 : CollatzResearch.WordTrace tailWord_1786528 prefixEnd_1786528 611565044477127623122609 := by
  unfold tailWord_1786528
  simp only [CollatzResearch.WordTrace]
  refine ⟨32580014635860822768044119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43440019514481097024058825 32580014635860822768044119)
  ·
    refine ⟨48870021953791234152066179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32580014635860822768044119 48870021953791234152066179)
    ·
      refine ⟨73305032930686851228099269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48870021953791234152066179 73305032930686851228099269)
      ·
        refine ⟨13744693674503784605268613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73305032930686851228099269 13744693674503784605268613)
        ·
          refine ⟨2577130063969459613487865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13744693674503784605268613 2577130063969459613487865)
          ·
            refine ⟨1932847547977094710115899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577130063969459613487865 1932847547977094710115899)
            ·
              refine ⟨2899271321965642065173849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932847547977094710115899 2899271321965642065173849)
              ·
                refine ⟨2174453491474231548880387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899271321965642065173849 2174453491474231548880387)
                ·
                  refine ⟨3261680237211347323320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174453491474231548880387 3261680237211347323320581)
                  ·
                    refine ⟨611565044477127623122609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261680237211347323320581 611565044477127623122609)
                    ·
                      rfl

theorem cell22_1786528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_1786528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786528 prefixEnd_1786528 := by exact prefixLift 1786528
  have htrace : WordTrace (prefixWord ++ tailWord_1786528) baseStart_1786528 baseEnd_1786528 := by
    simpa [prefixWord, tailWord_1786528, baseEnd_1786528] using wordTrace_append hprefix tailTrace_1786528
  have hstable : (prefixWord ++ tailWord_1786528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786528).length < 2 ^ (prefixWord ++ tailWord_1786528).sum := by decide
  have hdescent : baseEnd_1786528 < baseStart_1786528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786541 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1786541 : Nat := 118140960795 + 1786541 * 2 ^ 59
def prefixEnd_1786541 : Nat := 4983230072969 + 3 ^ 40 * 1786541 * 2
def baseEnd_1786541 : Nat := 611569494642799922547569

theorem tailTrace_1786541 : CollatzResearch.WordTrace tailWord_1786541 prefixEnd_1786541 611569494642799922547569 := by
  unfold tailWord_1786541
  simp only [CollatzResearch.WordTrace]
  refine ⟨65160503420674548756311477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43440335613783032504207651 65160503420674548756311477)
  ·
    refine ⟨6108797195688238945904201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65160503420674548756311477 6108797195688238945904201)
    ·
      refine ⟨4581597896766179209428151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6108797195688238945904201 4581597896766179209428151)
      ·
        refine ⟨6872396845149268814142227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581597896766179209428151 6872396845149268814142227)
        ·
          refine ⟨10308595267723903221213341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6872396845149268814142227 10308595267723903221213341)
          ·
            refine ⟨3865723225396463707955003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10308595267723903221213341 3865723225396463707955003)
            ·
              refine ⟨5798584838094695561932505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865723225396463707955003 5798584838094695561932505)
              ·
                refine ⟨4348938628571021671449379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798584838094695561932505 4348938628571021671449379)
                ·
                  refine ⟨6523407942856532507174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348938628571021671449379 6523407942856532507174069)
                  ·
                    refine ⟨611569494642799922547569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6523407942856532507174069 611569494642799922547569)
                    ·
                      rfl

theorem cell22_1786541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1786541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786541 prefixEnd_1786541 := by exact prefixLift 1786541
  have htrace : WordTrace (prefixWord ++ tailWord_1786541) baseStart_1786541 baseEnd_1786541 := by
    simpa [prefixWord, tailWord_1786541, baseEnd_1786541] using wordTrace_append hprefix tailTrace_1786541
  have hstable : (prefixWord ++ tailWord_1786541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786541).length < 2 ^ (prefixWord ++ tailWord_1786541).sum := by decide
  have hdescent : baseEnd_1786541 < baseStart_1786541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786545 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_1786545 : Nat := 118140960795 + 1786545 * 2 ^ 59
def prefixEnd_1786545 : Nat := 4983230072969 + 3 ^ 40 * 1786545 * 2
def baseEnd_1786545 : Nat := 611570863924545245447557

theorem tailTrace_1786545 : CollatzResearch.WordTrace tailWord_1786545 prefixEnd_1786545 611570863924545245447557 := by
  unfold tailWord_1786545
  simp only [CollatzResearch.WordTrace]
  refine ⟨65160649312660057439457089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43440432875106704959638059 65160649312660057439457089)
  ·
    refine ⟨48870486984495043079592817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65160649312660057439457089 48870486984495043079592817)
    ·
      refine ⟨36652865238371282309694613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48870486984495043079592817 36652865238371282309694613)
      ·
        refine ⟨1718103058048653858266935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36652865238371282309694613 1718103058048653858266935)
        ·
          refine ⟨2577154587072980787400403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718103058048653858266935 2577154587072980787400403)
          ·
            refine ⟨3865731880609471181100605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577154587072980787400403 3865731880609471181100605)
            ·
              refine ⟨1449649455228551692912727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3865731880609471181100605 1449649455228551692912727)
              ·
                refine ⟨2174474182842827539369091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449649455228551692912727 2174474182842827539369091)
                ·
                  refine ⟨3261711274264241309053637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174474182842827539369091 3261711274264241309053637)
                  ·
                    refine ⟨611570863924545245447557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261711274264241309053637 611570863924545245447557)
                    ·
                      rfl

theorem cell22_1786545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_1786545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786545 prefixEnd_1786545 := by exact prefixLift 1786545
  have htrace : WordTrace (prefixWord ++ tailWord_1786545) baseStart_1786545 baseEnd_1786545 := by
    simpa [prefixWord, tailWord_1786545, baseEnd_1786545] using wordTrace_append hprefix tailTrace_1786545
  have hstable : (prefixWord ++ tailWord_1786545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786545).length < 2 ^ (prefixWord ++ tailWord_1786545).sum := by decide
  have hdescent : baseEnd_1786545 < baseStart_1786545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786558 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1786558 : Nat := 118140960795 + 1786558 * 2 ^ 59
def prefixEnd_1786558 : Nat := 4983230072969 + 3 ^ 40 * 1786558 * 2
def baseEnd_1786558 : Nat := 611575314090217544872517

theorem tailTrace_1786558 : CollatzResearch.WordTrace tailWord_1786558 prefixEnd_1786558 611575314090217544872517 := by
  unfold tailWord_1786558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145140432701620082460041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43440748974408640439786885 8145140432701620082460041)
  ·
    refine ⟨6108855324526215061845031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8145140432701620082460041 6108855324526215061845031)
    ·
      refine ⟨9163282986789322592767547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6108855324526215061845031 9163282986789322592767547)
      ·
        refine ⟨13744924480183983889151321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9163282986789322592767547 13744924480183983889151321)
        ·
          refine ⟨10308693360137987916863491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13744924480183983889151321 10308693360137987916863491)
          ·
            refine ⟨15463040040206981875295237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308693360137987916863491 15463040040206981875295237)
            ·
              refine ⟨2899320007538809101617857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15463040040206981875295237 2899320007538809101617857)
              ·
                refine ⟨2174490005654106826213393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899320007538809101617857 2174490005654106826213393)
                ·
                  refine ⟨1630867504240580119660045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174490005654106826213393 1630867504240580119660045)
                  ·
                    refine ⟨611575314090217544872517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630867504240580119660045 611575314090217544872517)
                    ·
                      rfl

theorem cell22_1786558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1786558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786558 prefixEnd_1786558 := by exact prefixLift 1786558
  have htrace : WordTrace (prefixWord ++ tailWord_1786558) baseStart_1786558 baseEnd_1786558 := by
    simpa [prefixWord, tailWord_1786558, baseEnd_1786558] using wordTrace_append hprefix tailTrace_1786558
  have hstable : (prefixWord ++ tailWord_1786558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786558).length < 2 ^ (prefixWord ++ tailWord_1786558).sum := by decide
  have hdescent : baseEnd_1786558 < baseStart_1786558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786569 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_1786569 : Nat := 118140960795 + 1786569 * 2 ^ 59
def prefixEnd_1786569 : Nat := 4983230072969 + 3 ^ 40 * 1786569 * 2
def baseEnd_1786569 : Nat := 611579079615017182847483

theorem tailTrace_1786569 : CollatzResearch.WordTrace tailWord_1786569 prefixEnd_1786569 611579079615017182847483 := by
  unfold tailWord_1786569
  simp only [CollatzResearch.WordTrace]
  refine ⟨65161524664573109538330761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43441016443048739692220507 65161524664573109538330761)
  ·
    refine ⟨48871143498429832153748071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65161524664573109538330761 48871143498429832153748071)
    ·
      refine ⟨73306715247644748230622107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48871143498429832153748071 73306715247644748230622107)
      ·
        refine ⟨109960072871467122345933161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73306715247644748230622107 109960072871467122345933161)
        ·
          refine ⟨82470054653600341759449871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109960072871467122345933161 82470054653600341759449871)
          ·
            refine ⟨123705081980400512639174807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82470054653600341759449871 123705081980400512639174807)
            ·
              refine ⟨185557622970600768958762211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123705081980400512639174807 185557622970600768958762211)
              ·
                refine ⟨278336434455901153438143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185557622970600768958762211 278336434455901153438143317)
                ·
                  refine ⟨1630877545640045820926621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 278336434455901153438143317 1630877545640045820926621)
                  ·
                    refine ⟨611579079615017182847483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630877545640045820926621 611579079615017182847483)
                    ·
                      rfl

theorem cell22_1786569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_1786569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786569 prefixEnd_1786569 := by exact prefixLift 1786569
  have htrace : WordTrace (prefixWord ++ tailWord_1786569) baseStart_1786569 baseEnd_1786569 := by
    simpa [prefixWord, tailWord_1786569, baseEnd_1786569] using wordTrace_append hprefix tailTrace_1786569
  have hstable : (prefixWord ++ tailWord_1786569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786569).length < 2 ^ (prefixWord ++ tailWord_1786569).sum := by decide
  have hdescent : baseEnd_1786569 < baseStart_1786569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786586 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_1786586 : Nat := 118140960795 + 1786586 * 2 ^ 59
def prefixEnd_1786586 : Nat := 4983230072969 + 3 ^ 40 * 1786586 * 2
def baseEnd_1786586 : Nat := 611584899062434805172431

theorem tailTrace_1786586 : CollatzResearch.WordTrace tailWord_1786586 prefixEnd_1786586 611584899062434805172431 := by
  unfold tailWord_1786586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16290536176377880360424903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43441429803674347627799741 16290536176377880360424903)
  ·
    refine ⟨24435804264566820540637355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16290536176377880360424903 24435804264566820540637355)
    ·
      refine ⟨36653706396850230810956033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24435804264566820540637355 36653706396850230810956033)
      ·
        refine ⟨27490279797637673108217025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36653706396850230810956033 27490279797637673108217025)
        ·
          refine ⟨20617709848228254831162769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27490279797637673108217025 20617709848228254831162769)
          ·
            refine ⟨15463282386171191123372077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20617709848228254831162769 15463282386171191123372077)
            ·
              refine ⟨5798730894814196671264529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15463282386171191123372077 5798730894814196671264529)
              ·
                refine ⟨4349048171110647503448397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798730894814196671264529 4349048171110647503448397)
                ·
                  refine ⟨1630893064166492813793149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4349048171110647503448397 1630893064166492813793149)
                  ·
                    refine ⟨611584899062434805172431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630893064166492813793149 611584899062434805172431)
                    ·
                      rfl

theorem cell22_1786586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_1786586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786586 prefixEnd_1786586 := by exact prefixLift 1786586
  have htrace : WordTrace (prefixWord ++ tailWord_1786586) baseStart_1786586 baseEnd_1786586 := by
    simpa [prefixWord, tailWord_1786586, baseEnd_1786586] using wordTrace_append hprefix tailTrace_1786586
  have hstable : (prefixWord ++ tailWord_1786586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786586).length < 2 ^ (prefixWord ++ tailWord_1786586).sum := by decide
  have hdescent : baseEnd_1786586 < baseStart_1786586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786588 : List Nat := [2, 2, 5, 1, 1, 2, 3, 6]
def baseStart_1786588 : Nat := 118140960795 + 1786588 * 2 ^ 59
def prefixEnd_1786588 : Nat := 4983230072969 + 3 ^ 40 * 1786588 * 2
def baseEnd_1786588 : Nat := 67953953744811940735825

theorem tailTrace_1786588 : CollatzResearch.WordTrace tailWord_1786588 prefixEnd_1786588 67953953744811940735825 := by
  unfold tailWord_1786588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32581108825752137891636209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43441478434336183855514945 32581108825752137891636209)
  ·
    refine ⟨24435831619314103418727157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32581108825752137891636209 24435831619314103418727157)
    ·
      refine ⟨2290859214310697195505671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24435831619314103418727157 2290859214310697195505671)
      ·
        refine ⟨3436288821466045793258507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290859214310697195505671 3436288821466045793258507)
        ·
          refine ⟨5154433232199068689887761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436288821466045793258507 5154433232199068689887761)
          ·
            refine ⟨3865824924149301517415821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5154433232199068689887761 3865824924149301517415821)
            ·
              refine ⟨1449684346555988069030933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3865824924149301517415821 1449684346555988069030933)
              ·
                refine ⟨67953953744811940735825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1449684346555988069030933 67953953744811940735825)
                ·
                  rfl

theorem cell22_1786588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_1786588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786588 prefixEnd_1786588 := by exact prefixLift 1786588
  have htrace : WordTrace (prefixWord ++ tailWord_1786588) baseStart_1786588 baseEnd_1786588 := by
    simpa [prefixWord, tailWord_1786588, baseEnd_1786588] using wordTrace_append hprefix tailTrace_1786588
  have hstable : (prefixWord ++ tailWord_1786588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786588).length < 2 ^ (prefixWord ++ tailWord_1786588).sum := by decide
  have hdescent : baseEnd_1786588 < baseStart_1786588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786629 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_1786629 : Nat := 118140960795 + 1786629 * 2 ^ 59
def prefixEnd_1786629 : Nat := 4983230072969 + 3 ^ 40 * 1786629 * 2
def baseEnd_1786629 : Nat := 611599618841197026347299

theorem tailTrace_1786629 : CollatzResearch.WordTrace tailWord_1786629 prefixEnd_1786629 611599618841197026347299 := by
  unfold tailWord_1786629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65163713044355739785514941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43442475362903826523676627 65163713044355739785514941)
  ·
    refine ⟨24436392391633402419568103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65163713044355739785514941 24436392391633402419568103)
    ·
      refine ⟨36654588587450103629352155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24436392391633402419568103 36654588587450103629352155)
      ·
        refine ⟨54981882881175155444028233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36654588587450103629352155 54981882881175155444028233)
        ·
          refine ⟨41236412160881366583021175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54981882881175155444028233 41236412160881366583021175)
          ·
            refine ⟨61854618241322049874531763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41236412160881366583021175 61854618241322049874531763)
            ·
              refine ⟨92781927361983074811797645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61854618241322049874531763 92781927361983074811797645)
              ·
                refine ⟨34793222760743653054424117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92781927361983074811797645 34793222760743653054424117)
                ·
                  refine ⟨3261864633819717473852261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34793222760743653054424117 3261864633819717473852261)
                  ·
                    refine ⟨611599618841197026347299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261864633819717473852261 611599618841197026347299)
                    ·
                      rfl

theorem cell22_1786629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_1786629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786629 prefixEnd_1786629 := by exact prefixLift 1786629
  have htrace : WordTrace (prefixWord ++ tailWord_1786629) baseStart_1786629 baseEnd_1786629 := by
    simpa [prefixWord, tailWord_1786629, baseEnd_1786629] using wordTrace_append hprefix tailTrace_1786629
  have hstable : (prefixWord ++ tailWord_1786629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786629).length < 2 ^ (prefixWord ++ tailWord_1786629).sum := by decide
  have hdescent : baseEnd_1786629 < baseStart_1786629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786631 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1786631 : Nat := 118140960795 + 1786631 * 2 ^ 59
def prefixEnd_1786631 : Nat := 4983230072969 + 3 ^ 40 * 1786631 * 2
def baseEnd_1786631 : Nat := 611600303482069687797293

theorem tailTrace_1786631 : CollatzResearch.WordTrace tailWord_1786631 prefixEnd_1786631 611600303482069687797293 := by
  unfold tailWord_1786631
  simp only [CollatzResearch.WordTrace]
  refine ⟨65163785990348494127087747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43442523993565662751391831 65163785990348494127087747)
  ·
    refine ⟨97745678985522741190631621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65163785990348494127087747 97745678985522741190631621)
    ·
      refine ⟨18327314809785513973243429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97745678985522741190631621 18327314809785513973243429)
      ·
        refine ⟨3436371526834783869983143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18327314809785513973243429 3436371526834783869983143)
        ·
          refine ⟨5154557290252175804974715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436371526834783869983143 5154557290252175804974715)
          ·
            refine ⟨7731835935378263707462073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154557290252175804974715 7731835935378263707462073)
            ·
              refine ⟨5798876951533697780596555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731835935378263707462073 5798876951533697780596555)
              ·
                refine ⟨8698315427300546670894833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798876951533697780596555 8698315427300546670894833)
                ·
                  refine ⟨6523736570475410003171125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698315427300546670894833 6523736570475410003171125)
                  ·
                    refine ⟨611600303482069687797293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6523736570475410003171125 611600303482069687797293)
                    ·
                      rfl

theorem cell22_1786631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1786631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786631 prefixEnd_1786631 := by exact prefixLift 1786631
  have htrace : WordTrace (prefixWord ++ tailWord_1786631) baseStart_1786631 baseEnd_1786631 := by
    simpa [prefixWord, tailWord_1786631, baseEnd_1786631] using wordTrace_append hprefix tailTrace_1786631
  have hstable : (prefixWord ++ tailWord_1786631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786631).length < 2 ^ (prefixWord ++ tailWord_1786631).sum := by decide
  have hdescent : baseEnd_1786631 < baseStart_1786631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786659 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_1786659 : Nat := 118140960795 + 1786659 * 2 ^ 59
def prefixEnd_1786659 : Nat := 4983230072969 + 3 ^ 40 * 1786659 * 2
def baseEnd_1786659 : Nat := 611609888454286948097207

theorem tailTrace_1786659 : CollatzResearch.WordTrace tailWord_1786659 prefixEnd_1786659 611609888454286948097207 := by
  unfold tailWord_1786659
  simp only [CollatzResearch.WordTrace]
  refine ⟨65164807234247054909107031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43443204822831369939404687 65164807234247054909107031)
  ·
    refine ⟨97747210851370582363660547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65164807234247054909107031 97747210851370582363660547)
    ·
      refine ⟨146620816277055873545490821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97747210851370582363660547 146620816277055873545490821)
      ·
        refine ⟨27491403051947976289779529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146620816277055873545490821 27491403051947976289779529)
        ·
          refine ⟨20618552288960982217334647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27491403051947976289779529 20618552288960982217334647)
          ·
            refine ⟨30927828433441473326001971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20618552288960982217334647 30927828433441473326001971)
            ·
              refine ⟨46391742650162209989002957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30927828433441473326001971 46391742650162209989002957)
              ·
                refine ⟨17396903493810828745876109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46391742650162209989002957 17396903493810828745876109)
                ·
                  refine ⟨6523838810179060779703541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17396903493810828745876109 6523838810179060779703541)
                  ·
                    refine ⟨611609888454286948097207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6523838810179060779703541 611609888454286948097207)
                    ·
                      rfl

theorem cell22_1786659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_1786659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786659 prefixEnd_1786659 := by exact prefixLift 1786659
  have htrace : WordTrace (prefixWord ++ tailWord_1786659) baseStart_1786659 baseEnd_1786659 := by
    simpa [prefixWord, tailWord_1786659, baseEnd_1786659] using wordTrace_append hprefix tailTrace_1786659
  have hstable : (prefixWord ++ tailWord_1786659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786659).length < 2 ^ (prefixWord ++ tailWord_1786659).sum := by decide
  have hdescent : baseEnd_1786659 < baseStart_1786659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786704 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_1786704 : Nat := 118140960795 + 1786704 * 2 ^ 59
def prefixEnd_1786704 : Nat := 4983230072969 + 3 ^ 40 * 1786704 * 2
def baseEnd_1786704 : Nat := 611625292873921830722069

theorem tailTrace_1786704 : CollatzResearch.WordTrace tailWord_1786704 prefixEnd_1786704 611625292873921830722069 := by
  unfold tailWord_1786704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32583224259542013797247583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43444299012722685062996777 32583224259542013797247583)
  ·
    refine ⟨48874836389313020695871375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32583224259542013797247583 48874836389313020695871375)
    ·
      refine ⟨73312254583969531043807063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48874836389313020695871375 73312254583969531043807063)
      ·
        refine ⟨109968381875954296565710595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73312254583969531043807063 109968381875954296565710595)
        ·
          refine ⟨164952572813931444848565893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109968381875954296565710595 164952572813931444848565893)
          ·
            refine ⟨30928607402612145909106105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164952572813931444848565893 30928607402612145909106105)
            ·
              refine ⟨23196455551959109431829579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30928607402612145909106105 23196455551959109431829579)
              ·
                refine ⟨34794683327938664147744369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23196455551959109431829579 34794683327938664147744369)
                ·
                  refine ⟨26096012495953998110808277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34794683327938664147744369 26096012495953998110808277)
                  ·
                    refine ⟨611625292873921830722069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26096012495953998110808277 611625292873921830722069)
                    ·
                      rfl

theorem cell22_1786704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_1786704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786704 prefixEnd_1786704 := by exact prefixLift 1786704
  have htrace : WordTrace (prefixWord ++ tailWord_1786704) baseStart_1786704 baseEnd_1786704 := by
    simpa [prefixWord, tailWord_1786704, baseEnd_1786704] using wordTrace_append hprefix tailTrace_1786704
  have hstable : (prefixWord ++ tailWord_1786704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786704).length < 2 ^ (prefixWord ++ tailWord_1786704).sum := by decide
  have hdescent : baseEnd_1786704 < baseStart_1786704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786721 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1786721 : Nat := 118140960795 + 1786721 * 2 ^ 59
def prefixEnd_1786721 : Nat := 4983230072969 + 3 ^ 40 * 1786721 * 2
def baseEnd_1786721 : Nat := 611631112321339453047017

theorem tailTrace_1786721 : CollatzResearch.WordTrace tailWord_1786721 prefixEnd_1786721 611631112321339453047017 := by
  unfold tailWord_1786721
  simp only [CollatzResearch.WordTrace]
  refine ⟨65167068560022439497864017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43444712373348292998576011 65167068560022439497864017)
  ·
    refine ⟨48875301420016829623398013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65167068560022439497864017 48875301420016829623398013)
    ·
      refine ⟨18328238032506311108774255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48875301420016829623398013 18328238032506311108774255)
      ·
        refine ⟨27492357048759466663161383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18328238032506311108774255 27492357048759466663161383)
        ·
          refine ⟨41238535573139199994742075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27492357048759466663161383 41238535573139199994742075)
          ·
            refine ⟨61857803359708799992113113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41238535573139199994742075 61857803359708799992113113)
            ·
              refine ⟨46393352519781599994084835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61857803359708799992113113 46393352519781599994084835)
              ·
                refine ⟨69590028779672399991127253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46393352519781599994084835 69590028779672399991127253)
                ·
                  refine ⟨1631016299523571874792045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 69590028779672399991127253 1631016299523571874792045)
                  ·
                    refine ⟨611631112321339453047017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631016299523571874792045 611631112321339453047017)
                    ·
                      rfl

theorem cell22_1786721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1786721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786721 prefixEnd_1786721 := by exact prefixLift 1786721
  have htrace : WordTrace (prefixWord ++ tailWord_1786721) baseStart_1786721 baseEnd_1786721 := by
    simpa [prefixWord, tailWord_1786721, baseEnd_1786721] using wordTrace_append hprefix tailTrace_1786721
  have hstable : (prefixWord ++ tailWord_1786721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786721).length < 2 ^ (prefixWord ++ tailWord_1786721).sum := by decide
  have hdescent : baseEnd_1786721 < baseStart_1786721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786751 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 5]
def baseStart_1786751 : Nat := 118140960795 + 1786751 * 2 ^ 59
def prefixEnd_1786751 : Nat := 4983230072969 + 3 ^ 40 * 1786751 * 2
def baseEnd_1786751 : Nat := 203880460644809791598975

theorem tailTrace_1786751 : CollatzResearch.WordTrace tailWord_1786751 prefixEnd_1786751 203880460644809791598975 := by
  unfold tailWord_1786751
  simp only [CollatzResearch.WordTrace]
  refine ⟨65168162749913754621456107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43445441833275836414304071 65168162749913754621456107)
  ·
    refine ⟨97752244124870631932184161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65168162749913754621456107 97752244124870631932184161)
    ·
      refine ⟨73314183093652973949138121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97752244124870631932184161 73314183093652973949138121)
      ·
        refine ⟨54985637320239730461853591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73314183093652973949138121 54985637320239730461853591)
        ·
          refine ⟨82478455980359595692780387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54985637320239730461853591 82478455980359595692780387)
          ·
            refine ⟨123717683970539393539170581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82478455980359595692780387 123717683970539393539170581)
            ·
              refine ⟨5799266436119034072148621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123717683970539393539170581 5799266436119034072148621)
              ·
                refine ⟨2174724913544637777055733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5799266436119034072148621 2174724913544637777055733)
                ·
                  refine ⟨203880460644809791598975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2174724913544637777055733 203880460644809791598975)
                  ·
                    rfl

theorem cell22_1786751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 5].length) (baseStart_1786751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786751 prefixEnd_1786751 := by exact prefixLift 1786751
  have htrace : WordTrace (prefixWord ++ tailWord_1786751) baseStart_1786751 baseEnd_1786751 := by
    simpa [prefixWord, tailWord_1786751, baseEnd_1786751] using wordTrace_append hprefix tailTrace_1786751
  have hstable : (prefixWord ++ tailWord_1786751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786751).length < 2 ^ (prefixWord ++ tailWord_1786751).sum := by decide
  have hdescent : baseEnd_1786751 < baseStart_1786751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786772 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1786772 : Nat := 118140960795 + 1786772 * 2 ^ 59
def prefixEnd_1786772 : Nat := 4983230072969 + 3 ^ 40 * 1786772 * 2
def baseEnd_1786772 : Nat := 611648570663592320021861

theorem tailTrace_1786772 : CollatzResearch.WordTrace tailWord_1786772 prefixEnd_1786772 611648570663592320021861 := by
  unfold tailWord_1786772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32584464341418837603985285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43445952455225116805313713 32584464341418837603985285)
  ·
    refine ⟨6109587064016032050747241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32584464341418837603985285 6109587064016032050747241)
    ·
      refine ⟨4582190298012024038060431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6109587064016032050747241 4582190298012024038060431)
      ·
        refine ⟨6873285447018036057090647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582190298012024038060431 6873285447018036057090647)
        ·
          refine ⟨10309928170527054085635971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6873285447018036057090647 10309928170527054085635971)
          ·
            refine ⟨15464892255790581128453957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10309928170527054085635971 15464892255790581128453957)
            ·
              refine ⟨2899667297960733961585117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15464892255790581128453957 2899667297960733961585117)
              ·
                refine ⟨1087375236735275235594419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2899667297960733961585117 1087375236735275235594419)
                ·
                  refine ⟨1631062855102912853391629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087375236735275235594419 1631062855102912853391629)
                  ·
                    refine ⟨611648570663592320021861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631062855102912853391629 611648570663592320021861)
                    ·
                      rfl

theorem cell22_1786772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1786772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786772 prefixEnd_1786772 := by exact prefixLift 1786772
  have htrace : WordTrace (prefixWord ++ tailWord_1786772) baseStart_1786772 baseEnd_1786772 := by
    simpa [prefixWord, tailWord_1786772, baseEnd_1786772] using wordTrace_append hprefix tailTrace_1786772
  have hstable : (prefixWord ++ tailWord_1786772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786772).length < 2 ^ (prefixWord ++ tailWord_1786772).sum := by decide
  have hdescent : baseEnd_1786772 < baseStart_1786772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786785 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 5]
def baseStart_1786785 : Nat := 118140960795 + 1786785 * 2 ^ 59
def prefixEnd_1786785 : Nat := 4983230072969 + 3 ^ 40 * 1786785 * 2
def baseEnd_1786785 : Nat := 203884340276421539815607

theorem tailTrace_1786785 : CollatzResearch.WordTrace tailWord_1786785 prefixEnd_1786785 203884340276421539815607 := by
  unfold tailWord_1786785
  simp only [CollatzResearch.WordTrace]
  refine ⟨65169402831790578428193809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43446268554527052285462539 65169402831790578428193809)
  ·
    refine ⟨48877052123842933821145357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65169402831790578428193809 48877052123842933821145357)
    ·
      refine ⟨18328894546441100182929509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48877052123842933821145357 18328894546441100182929509)
      ·
        refine ⟨3436667727457706284299283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18328894546441100182929509 3436667727457706284299283)
        ·
          refine ⟨5155001591186559426448925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436667727457706284299283 5155001591186559426448925)
          ·
            refine ⟨1933125596694959784918347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5155001591186559426448925 1933125596694959784918347)
            ·
              refine ⟨2899688395042439677377521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933125596694959784918347 2899688395042439677377521)
              ·
                refine ⟨2174766296281829758033141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899688395042439677377521 2174766296281829758033141)
                ·
                  refine ⟨203884340276421539815607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2174766296281829758033141 203884340276421539815607)
                  ·
                    rfl

theorem cell22_1786785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_1786785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786785 prefixEnd_1786785 := by exact prefixLift 1786785
  have htrace : WordTrace (prefixWord ++ tailWord_1786785) baseStart_1786785 baseEnd_1786785 := by
    simpa [prefixWord, tailWord_1786785, baseEnd_1786785] using wordTrace_append hprefix tailTrace_1786785
  have hstable : (prefixWord ++ tailWord_1786785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786785).length < 2 ^ (prefixWord ++ tailWord_1786785).sum := by decide
  have hdescent : baseEnd_1786785 < baseStart_1786785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786828 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_1786828 : Nat := 118140960795 + 1786828 * 2 ^ 59
def prefixEnd_1786828 : Nat := 4983230072969 + 3 ^ 40 * 1786828 * 2
def baseEnd_1786828 : Nat := 611667740608026840621689

theorem tailTrace_1786828 : CollatzResearch.WordTrace tailWord_1786828 prefixEnd_1786828 611667740608026840621689 := by
  unfold tailWord_1786828
  simp only [CollatzResearch.WordTrace]
  refine ⟨32585485585317398386004569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43447314113756531181339425 32585485585317398386004569)
  ·
    refine ⟨24439114188988048789503427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32585485585317398386004569 24439114188988048789503427)
    ·
      refine ⟨36658671283482073184255141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24439114188988048789503427 36658671283482073184255141)
      ·
        refine ⟨6873500865652888722047839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36658671283482073184255141 6873500865652888722047839)
        ·
          refine ⟨10310251298479333083071759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6873500865652888722047839 10310251298479333083071759)
          ·
            refine ⟨15465376947718999624607639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10310251298479333083071759 15465376947718999624607639)
            ·
              refine ⟨23198065421578499436911459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15465376947718999624607639 23198065421578499436911459)
              ·
                refine ⟨34797098132367749155367189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23198065421578499436911459 34797098132367749155367189)
                ·
                  refine ⟨1631113974954738241657837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34797098132367749155367189 1631113974954738241657837)
                  ·
                    refine ⟨611667740608026840621689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631113974954738241657837 611667740608026840621689)
                    ·
                      rfl

theorem cell22_1786828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_1786828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786828 prefixEnd_1786828 := by exact prefixLift 1786828
  have htrace : WordTrace (prefixWord ++ tailWord_1786828) baseStart_1786828 baseEnd_1786828 := by
    simpa [prefixWord, tailWord_1786828, baseEnd_1786828] using wordTrace_append hprefix tailTrace_1786828
  have hstable : (prefixWord ++ tailWord_1786828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786828).length < 2 ^ (prefixWord ++ tailWord_1786828).sum := by decide
  have hdescent : baseEnd_1786828 < baseStart_1786828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786830 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_1786830 : Nat := 118140960795 + 1786830 * 2 ^ 59
def prefixEnd_1786830 : Nat := 4983230072969 + 3 ^ 40 * 1786830 * 2
def baseEnd_1786830 : Nat := 203889475082966500690561

theorem tailTrace_1786830 : CollatzResearch.WordTrace tailWord_1786830 prefixEnd_1786830 203889475082966500690561 := by
  unfold tailWord_1786830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146380514578443889197743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43447362744418367409054629 8146380514578443889197743)
  ·
    refine ⟨12219570771867665833796615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8146380514578443889197743 12219570771867665833796615)
    ·
      refine ⟨18329356157801498750694923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12219570771867665833796615 18329356157801498750694923)
      ·
        refine ⟨27494034236702248126042385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18329356157801498750694923 27494034236702248126042385)
        ·
          refine ⟨20620525677526686094531789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27494034236702248126042385 20620525677526686094531789)
          ·
            refine ⟨7732697129072507285449421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20620525677526686094531789 7732697129072507285449421)
            ·
              refine ⟨2899761423402190232043533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732697129072507285449421 2899761423402190232043533)
              ·
                refine ⟨1087410533775821337016325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2899761423402190232043533 1087410533775821337016325)
                ·
                  refine ⟨203889475082966500690561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087410533775821337016325 203889475082966500690561)
                  ·
                    rfl

theorem cell22_1786830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_1786830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786830 prefixEnd_1786830 := by exact prefixLift 1786830
  have htrace : WordTrace (prefixWord ++ tailWord_1786830) baseStart_1786830 baseEnd_1786830 := by
    simpa [prefixWord, tailWord_1786830, baseEnd_1786830] using wordTrace_append hprefix tailTrace_1786830
  have hstable : (prefixWord ++ tailWord_1786830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786830).length < 2 ^ (prefixWord ++ tailWord_1786830).sum := by decide
  have hdescent : baseEnd_1786830 < baseStart_1786830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786841 : List Nat := [1, 2, 1, 2, 5, 1, 10]
def baseStart_1786841 : Nat := 118140960795 + 1786841 * 2 ^ 59
def prefixEnd_1786841 : Nat := 4983230072969 + 3 ^ 40 * 1786841 * 2
def baseEnd_1786841 : Nat := 22654525584211079260987

theorem tailTrace_1786841 : CollatzResearch.WordTrace tailWord_1786841 prefixEnd_1786841 22654525584211079260987 := by
  unfold tailWord_1786841
  simp only [CollatzResearch.WordTrace]
  refine ⟨65171445319587699992232377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43447630213058466661488251 65171445319587699992232377)
  ·
    refine ⟨48878583989690774994174283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65171445319587699992232377 48878583989690774994174283)
    ·
      refine ⟨73317875984536162491261425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48878583989690774994174283 73317875984536162491261425)
      ·
        refine ⟨54988406988402121868446069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73317875984536162491261425 54988406988402121868446069)
        ·
          refine ⟨5155163155162698925166819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54988406988402121868446069 5155163155162698925166819)
          ·
            refine ⟨7732744732744048387750229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155163155162698925166819 7732744732744048387750229)
            ·
              refine ⟨22654525584211079260987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7732744732744048387750229 22654525584211079260987)
              ·
                rfl

theorem cell22_1786841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 10].length) (baseStart_1786841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786841 prefixEnd_1786841 := by exact prefixLift 1786841
  have htrace : WordTrace (prefixWord ++ tailWord_1786841) baseStart_1786841 baseEnd_1786841 := by
    simpa [prefixWord, tailWord_1786841, baseEnd_1786841] using wordTrace_append hprefix tailTrace_1786841
  have hstable : (prefixWord ++ tailWord_1786841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786841).length < 2 ^ (prefixWord ++ tailWord_1786841).sum := by decide
  have hdescent : baseEnd_1786841 < baseStart_1786841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786845 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1786845 : Nat := 118140960795 + 1786845 * 2 ^ 59
def prefixEnd_1786845 : Nat := 4983230072969 + 3 ^ 40 * 1786845 * 2
def baseEnd_1786845 : Nat := 611673560055444462946637

theorem tailTrace_1786845 : CollatzResearch.WordTrace tailWord_1786845 prefixEnd_1786845 611673560055444462946637 := by
  unfold tailWord_1786845
  simp only [CollatzResearch.WordTrace]
  refine ⟨65171591211573208675377989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43447727474382139116918659 65171591211573208675377989)
  ·
    refine ⟨12219673352169976626633373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65171591211573208675377989 12219673352169976626633373)
    ·
      refine ⟨4582377507063741234987515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12219673352169976626633373 4582377507063741234987515)
      ·
        refine ⟨6873566260595611852481273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582377507063741234987515 6873566260595611852481273)
        ·
          refine ⟨5155174695446708889360955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6873566260595611852481273 5155174695446708889360955)
          ·
            refine ⟨7732762043170063334041433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155174695446708889360955 7732762043170063334041433)
            ·
              refine ⟨5799571532377547500531075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7732762043170063334041433 5799571532377547500531075)
              ·
                refine ⟨8699357298566321250796613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799571532377547500531075 8699357298566321250796613)
                ·
                  refine ⟨1631129493481185234524365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8699357298566321250796613 1631129493481185234524365)
                  ·
                    refine ⟨611673560055444462946637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631129493481185234524365 611673560055444462946637)
                    ·
                      rfl

theorem cell22_1786845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1786845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786845 prefixEnd_1786845 := by exact prefixLift 1786845
  have htrace : WordTrace (prefixWord ++ tailWord_1786845) baseStart_1786845 baseEnd_1786845 := by
    simpa [prefixWord, tailWord_1786845, baseEnd_1786845] using wordTrace_append hprefix tailTrace_1786845
  have hstable : (prefixWord ++ tailWord_1786845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786845).length < 2 ^ (prefixWord ++ tailWord_1786845).sum := by decide
  have hdescent : baseEnd_1786845 < baseStart_1786845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786847 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 4]
def baseStart_1786847 : Nat := 118140960795 + 1786847 * 2 ^ 59
def prefixEnd_1786847 : Nat := 4983230072969 + 3 ^ 40 * 1786847 * 2
def baseEnd_1786847 : Nat := 203891414898772374798877

theorem tailTrace_1786847 : CollatzResearch.WordTrace tailWord_1786847 prefixEnd_1786847 203891414898772374798877 := by
  unfold tailWord_1786847
  simp only [CollatzResearch.WordTrace]
  refine ⟨65171664157565963016950795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43447776105043975344633863 65171664157565963016950795)
  ·
    refine ⟨97757496236348944525426193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65171664157565963016950795 97757496236348944525426193)
    ·
      refine ⟨73318122177261708394069645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97757496236348944525426193 73318122177261708394069645)
      ·
        refine ⟨27494295816473140647776117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73318122177261708394069645 27494295816473140647776117)
        ·
          refine ⟨2577590232794356935729011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27494295816473140647776117 2577590232794356935729011)
          ·
            refine ⟨3866385349191535403593517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577590232794356935729011 3866385349191535403593517)
            ·
              refine ⟨1449894505946825776347569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866385349191535403593517 1449894505946825776347569)
              ·
                refine ⟨1087420879460119332260677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449894505946825776347569 1087420879460119332260677)
                ·
                  refine ⟨203891414898772374798877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087420879460119332260677 203891414898772374798877)
                  ·
                    rfl

theorem cell22_1786847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 4].length) (baseStart_1786847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786847 prefixEnd_1786847 := by exact prefixLift 1786847
  have htrace : WordTrace (prefixWord ++ tailWord_1786847) baseStart_1786847 baseEnd_1786847 := by
    simpa [prefixWord, tailWord_1786847, baseEnd_1786847] using wordTrace_append hprefix tailTrace_1786847
  have hstable : (prefixWord ++ tailWord_1786847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786847).length < 2 ^ (prefixWord ++ tailWord_1786847).sum := by decide
  have hdescent : baseEnd_1786847 < baseStart_1786847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786858 : List Nat := [3, 1, 3, 1, 2, 3, 2, 7]
def baseStart_1786858 : Nat := 118140960795 + 1786858 * 2 ^ 59
def prefixEnd_1786858 : Nat := 4983230072969 + 3 ^ 40 * 1786858 * 2
def baseEnd_1786858 : Nat := 67964223357901862485733

theorem tailTrace_1786858 : CollatzResearch.WordTrace tailWord_1786858 prefixEnd_1786858 67964223357901862485733 := by
  unfold tailWord_1786858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293016340131527973900307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43448043573684074597067485 16293016340131527973900307)
  ·
    refine ⟨24439524510197291960850461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16293016340131527973900307 24439524510197291960850461)
    ·
      refine ⟨9164821691323984485318923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24439524510197291960850461 9164821691323984485318923)
      ·
        refine ⟨13747232536985976727978385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9164821691323984485318923 13747232536985976727978385)
        ·
          refine ⟨10310424402739482545983789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13747232536985976727978385 10310424402739482545983789)
          ·
            refine ⟨3866409151027305954743921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10310424402739482545983789 3866409151027305954743921)
            ·
              refine ⟨2899806863270479466057941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866409151027305954743921 2899806863270479466057941)
              ·
                refine ⟨67964223357901862485733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2899806863270479466057941 67964223357901862485733)
                ·
                  rfl

theorem cell22_1786858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_1786858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786858 prefixEnd_1786858 := by exact prefixLift 1786858
  have htrace : WordTrace (prefixWord ++ tailWord_1786858) baseStart_1786858 baseEnd_1786858 := by
    simpa [prefixWord, tailWord_1786858, baseEnd_1786858] using wordTrace_append hprefix tailTrace_1786858
  have hstable : (prefixWord ++ tailWord_1786858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786858).length < 2 ^ (prefixWord ++ tailWord_1786858).sum := by decide
  have hdescent : baseEnd_1786858 < baseStart_1786858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786862 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1786862 : Nat := 118140960795 + 1786862 * 2 ^ 59
def prefixEnd_1786862 : Nat := 4983230072969 + 3 ^ 40 * 1786862 * 2
def baseEnd_1786862 : Nat := 611679379502862085271585

theorem tailTrace_1786862 : CollatzResearch.WordTrace tailWord_1786862 prefixEnd_1786862 611679379502862085271585 := by
  unfold tailWord_1786862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146526406563952572343355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43448140835007747052497893 8146526406563952572343355)
  ·
    refine ⟨12219789609845928858515033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8146526406563952572343355 12219789609845928858515033)
    ·
      refine ⟨9164842207384446643886275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12219789609845928858515033 9164842207384446643886275)
      ·
        refine ⟨13747263311076669965829413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9164842207384446643886275 13747263311076669965829413)
        ·
          refine ⟨2577611870826875618593015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13747263311076669965829413 2577611870826875618593015)
          ·
            refine ⟨3866417806240313427889523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577611870826875618593015 3866417806240313427889523)
            ·
              refine ⟨5799626709360470141834285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866417806240313427889523 5799626709360470141834285)
              ·
                refine ⟨2174860016010176303187857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5799626709360470141834285 2174860016010176303187857)
                ·
                  refine ⟨1631145012007632227390893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174860016010176303187857 1631145012007632227390893)
                  ·
                    refine ⟨611679379502862085271585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631145012007632227390893 611679379502862085271585)
                    ·
                      rfl

theorem cell22_1786862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1786862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786862 prefixEnd_1786862 := by exact prefixLift 1786862
  have htrace : WordTrace (prefixWord ++ tailWord_1786862) baseStart_1786862 baseEnd_1786862 := by
    simpa [prefixWord, tailWord_1786862, baseEnd_1786862] using wordTrace_append hprefix tailTrace_1786862
  have hstable : (prefixWord ++ tailWord_1786862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786862).length < 2 ^ (prefixWord ++ tailWord_1786862).sum := by decide
  have hdescent : baseEnd_1786862 < baseStart_1786862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786873 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_1786873 : Nat := 118140960795 + 1786873 * 2 ^ 59
def prefixEnd_1786873 : Nat := 4983230072969 + 3 ^ 40 * 1786873 * 2
def baseEnd_1786873 : Nat := 611683145027661723246551

theorem tailTrace_1786873 : CollatzResearch.WordTrace tailWord_1786873 prefixEnd_1786873 611683145027661723246551 := by
  unfold tailWord_1786873
  simp only [CollatzResearch.WordTrace]
  refine ⟨65172612455471769457397273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43448408303647846304931515 65172612455471769457397273)
  ·
    refine ⟨48879459341603827093047955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65172612455471769457397273 48879459341603827093047955)
    ·
      refine ⟨73319189012405740639571933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48879459341603827093047955 73319189012405740639571933)
      ·
        refine ⟨27494695879652152739839475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73319189012405740639571933 27494695879652152739839475)
        ·
          refine ⟨41242043819478229109759213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27494695879652152739839475 41242043819478229109759213)
          ·
            refine ⟨15465766432304335916159705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41242043819478229109759213 15465766432304335916159705)
            ·
              refine ⟨11599324824228251937119779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15465766432304335916159705 11599324824228251937119779)
              ·
                refine ⟨17398987236342377905679669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11599324824228251937119779 17398987236342377905679669)
                ·
                  refine ⟨1631155053407097928657469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17398987236342377905679669 1631155053407097928657469)
                  ·
                    refine ⟨611683145027661723246551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631155053407097928657469 611683145027661723246551)
                    ·
                      rfl

theorem cell22_1786873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_1786873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786873 prefixEnd_1786873 := by exact prefixLift 1786873
  have htrace : WordTrace (prefixWord ++ tailWord_1786873) baseStart_1786873 baseEnd_1786873 := by
    simpa [prefixWord, tailWord_1786873, baseEnd_1786873] using wordTrace_append hprefix tailTrace_1786873
  have hstable : (prefixWord ++ tailWord_1786873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786873).length < 2 ^ (prefixWord ++ tailWord_1786873).sum := by decide
  have hdescent : baseEnd_1786873 < baseStart_1786873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786898 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1786898 : Nat := 118140960795 + 1786898 * 2 ^ 59
def prefixEnd_1786898 : Nat := 4983230072969 + 3 ^ 40 * 1786898 * 2
def baseEnd_1786898 : Nat := 203897234346189997123825

theorem tailTrace_1786898 : CollatzResearch.WordTrace tailWord_1786898 prefixEnd_1786898 203897234346189997123825 := by
  unfold tailWord_1786898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293381070095299681764337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43449016186920799151371565 16293381070095299681764337)
  ·
    refine ⟨12220035802571474761323253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16293381070095299681764337 12220035802571474761323253)
    ·
      refine ⟨1145628356491075758874055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12220035802571474761323253 1145628356491075758874055)
      ·
        refine ⟨1718442534736613638311083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145628356491075758874055 1718442534736613638311083)
        ·
          refine ⟨2577663802104920457466625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718442534736613638311083 2577663802104920457466625)
          ·
            refine ⟨1933247851578690343099969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577663802104920457466625 1933247851578690343099969)
            ·
              refine ⟨1449935888684017757324977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933247851578690343099969 1449935888684017757324977)
              ·
                refine ⟨1087451916513013317993733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449935888684017757324977 1087451916513013317993733)
                ·
                  refine ⟨203897234346189997123825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087451916513013317993733 203897234346189997123825)
                  ·
                    rfl

theorem cell22_1786898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1786898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786898 prefixEnd_1786898 := by exact prefixLift 1786898
  have htrace : WordTrace (prefixWord ++ tailWord_1786898) baseStart_1786898 baseEnd_1786898 := by
    simpa [prefixWord, tailWord_1786898, baseEnd_1786898] using wordTrace_append hprefix tailTrace_1786898
  have hstable : (prefixWord ++ tailWord_1786898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786898).length < 2 ^ (prefixWord ++ tailWord_1786898).sum := by decide
  have hdescent : baseEnd_1786898 < baseStart_1786898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786965 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 4]
def baseStart_1786965 : Nat := 118140960795 + 1786965 * 2 ^ 59
def prefixEnd_1786965 : Nat := 4983230072969 + 3 ^ 40 * 1786965 * 2
def baseEnd_1786965 : Nat := 203904879502601383315423

theorem tailTrace_1786965 : CollatzResearch.WordTrace tailWord_1786965 prefixEnd_1786965 203904879502601383315423 := by
  unfold tailWord_1786965
  simp only [CollatzResearch.WordTrace]
  refine ⟨65175967971138469169746349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43450645314092312779830899 65175967971138469169746349)
  ·
    refine ⟨24440987989176925938654881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65175967971138469169746349 24440987989176925938654881)
    ·
      refine ⟨18330740991882694453991161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24440987989176925938654881 18330740991882694453991161)
      ·
        refine ⟨13748055743912020840493371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18330740991882694453991161 13748055743912020840493371)
        ·
          refine ⟨20622083615868031260740057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13748055743912020840493371 20622083615868031260740057)
          ·
            refine ⟨15466562711901023445555043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20622083615868031260740057 15466562711901023445555043)
            ·
              refine ⟨23199844067851535168332565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15466562711901023445555043 23199844067851535168332565)
              ·
                refine ⟨1087492690680540711015589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23199844067851535168332565 1087492690680540711015589)
                ·
                  refine ⟨203904879502601383315423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087492690680540711015589 203904879502601383315423)
                  ·
                    rfl

theorem cell22_1786965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_1786965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786965 prefixEnd_1786965 := by exact prefixLift 1786965
  have htrace : WordTrace (prefixWord ++ tailWord_1786965) baseStart_1786965 baseEnd_1786965 := by
    simpa [prefixWord, tailWord_1786965, baseEnd_1786965] using wordTrace_append hprefix tailTrace_1786965
  have hstable : (prefixWord ++ tailWord_1786965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786965).length < 2 ^ (prefixWord ++ tailWord_1786965).sum := by decide
  have hdescent : baseEnd_1786965 < baseStart_1786965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786984 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1786984 : Nat := 118140960795 + 1786984 * 2 ^ 59
def prefixEnd_1786984 : Nat := 4983230072969 + 3 ^ 40 * 1786984 * 2
def baseEnd_1786984 : Nat := 611721142596094433721211

theorem tailTrace_1786984 : CollatzResearch.WordTrace tailWord_1786984 prefixEnd_1786984 611721142596094433721211 := by
  unfold tailWord_1786984
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588330479034817707344003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43451107305379756943125337 32588330479034817707344003)
  ·
    refine ⟨48882495718552226561016005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32588330479034817707344003 48882495718552226561016005)
    ·
      refine ⟨9165467947228542480190501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48882495718552226561016005 9165467947228542480190501)
      ·
        refine ⟨1718525240105351715035719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9165467947228542480190501 1718525240105351715035719)
        ·
          refine ⟨2577787860158027572553579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718525240105351715035719 2577787860158027572553579)
          ·
            refine ⟨3866681790237041358830369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577787860158027572553579 3866681790237041358830369)
            ·
              refine ⟨2900011342677781019122777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866681790237041358830369 2900011342677781019122777)
              ·
                refine ⟨2175008507008335764342083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900011342677781019122777 2175008507008335764342083)
                ·
                  refine ⟨3262512760512503646513125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175008507008335764342083 3262512760512503646513125)
                  ·
                    refine ⟨611721142596094433721211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3262512760512503646513125 611721142596094433721211)
                    ·
                      rfl

theorem cell22_1786984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1786984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1786984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1786984 prefixEnd_1786984 := by exact prefixLift 1786984
  have htrace : WordTrace (prefixWord ++ tailWord_1786984) baseStart_1786984 baseEnd_1786984 := by
    simpa [prefixWord, tailWord_1786984, baseEnd_1786984] using wordTrace_append hprefix tailTrace_1786984
  have hstable : (prefixWord ++ tailWord_1786984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786984).length < 2 ^ (prefixWord ++ tailWord_1786984).sum := by decide
  have hdescent : baseEnd_1786984 < baseStart_1786984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787072 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_1787072 : Nat := 118140960795 + 1787072 * 2 ^ 59
def prefixEnd_1787072 : Nat := 4983230072969 + 3 ^ 40 * 1787072 * 2
def baseEnd_1787072 : Nat := 203917088931497179173647

theorem tailTrace_1787072 : CollatzResearch.WordTrace tailWord_1787072 prefixEnd_1787072 203917088931497179173647 := by
  unfold tailWord_1787072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32589935290875413221945735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43453247054500550962594313 32589935290875413221945735)
  ·
    refine ⟨48884902936313119832918603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32589935290875413221945735 48884902936313119832918603)
    ·
      refine ⟨73327354404469679749377905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48884902936313119832918603 73327354404469679749377905)
      ·
        refine ⟨54995515803352259812033429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73327354404469679749377905 54995515803352259812033429)
        ·
          refine ⟨2577914803282137178689067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54995515803352259812033429 2577914803282137178689067)
          ·
            refine ⟨3866872204923205768033601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577914803282137178689067 3866872204923205768033601)
            ·
              refine ⟨2900154153692404326025201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866872204923205768033601 2900154153692404326025201)
              ·
                refine ⟨2175115615269303244518901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900154153692404326025201 2175115615269303244518901)
                ·
                  refine ⟨203917088931497179173647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175115615269303244518901 203917088931497179173647)
                  ·
                    rfl

theorem cell22_1787072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_1787072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787072 prefixEnd_1787072 := by exact prefixLift 1787072
  have htrace : WordTrace (prefixWord ++ tailWord_1787072) baseStart_1787072 baseEnd_1787072 := by
    simpa [prefixWord, tailWord_1787072, baseEnd_1787072] using wordTrace_append hprefix tailTrace_1787072
  have hstable : (prefixWord ++ tailWord_1787072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787072).length < 2 ^ (prefixWord ++ tailWord_1787072).sum := by decide
  have hdescent : baseEnd_1787072 < baseStart_1787072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787076 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1787076 : Nat := 118140960795 + 1787076 * 2 ^ 59
def prefixEnd_1787076 : Nat := 4983230072969 + 3 ^ 40 * 1787076 * 2
def baseEnd_1787076 : Nat := 611752636076236860420929

theorem tailTrace_1787076 : CollatzResearch.WordTrace tailWord_1787076 prefixEnd_1787076 611752636076236860420929 := by
  unfold tailWord_1787076
  simp only [CollatzResearch.WordTrace]
  refine ⟨32590008236868167563518541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43453344315824223418024721 32590008236868167563518541)
  ·
    refine ⟨12221253088825562836319453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32590008236868167563518541 12221253088825562836319453)
    ·
      refine ⟨4582969908309586063619795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12221253088825562836319453 4582969908309586063619795)
      ·
        refine ⟨6874454862464379095429693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582969908309586063619795 6874454862464379095429693)
        ·
          refine ⟨2577920573424142160786135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6874454862464379095429693 2577920573424142160786135)
          ·
            refine ⟨3866880860136213241179203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577920573424142160786135 3866880860136213241179203)
            ·
              refine ⟨5800321290204319861768805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866880860136213241179203 5800321290204319861768805)
              ·
                refine ⟨1087560241913309974081651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5800321290204319861768805 1087560241913309974081651)
                ·
                  refine ⟨1631340362869964961122477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087560241913309974081651 1631340362869964961122477)
                  ·
                    refine ⟨611752636076236860420929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631340362869964961122477 611752636076236860420929)
                    ·
                      rfl

theorem cell22_1787076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1787076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787076 prefixEnd_1787076 := by exact prefixLift 1787076
  have htrace : WordTrace (prefixWord ++ tailWord_1787076) baseStart_1787076 baseEnd_1787076 := by
    simpa [prefixWord, tailWord_1787076, baseEnd_1787076] using wordTrace_append hprefix tailTrace_1787076
  have hstable : (prefixWord ++ tailWord_1787076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787076).length < 2 ^ (prefixWord ++ tailWord_1787076).sum := by decide
  have hdescent : baseEnd_1787076 < baseStart_1787076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787078 : List Nat := [6, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1787078 : Nat := 118140960795 + 1787078 * 2 ^ 59
def prefixEnd_1787078 : Nat := 4983230072969 + 3 ^ 40 * 1787078 * 2
def baseEnd_1787078 : Nat := 67972591190789946874547

theorem tailTrace_1787078 : CollatzResearch.WordTrace tailWord_1787078 prefixEnd_1787078 67972591190789946874547 := by
  unfold tailWord_1787078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036877794366534045894059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43453392946486059645739925 2036877794366534045894059)
  ·
    refine ⟨3055316691549801068841089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036877794366534045894059 3055316691549801068841089)
    ·
      refine ⟨2291487518662350801630817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3055316691549801068841089 2291487518662350801630817)
      ·
        refine ⟨1718615638996763101223113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2291487518662350801630817 1718615638996763101223113)
        ·
          refine ⟨1288961729247572325917335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718615638996763101223113 1288961729247572325917335)
          ·
            refine ⟨1933442593871358488876003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288961729247572325917335 1933442593871358488876003)
            ·
              refine ⟨2900163890807037733314005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933442593871358488876003 2900163890807037733314005)
              ·
                refine ⟨67972591190789946874547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2900163890807037733314005 67972591190789946874547)
                ·
                  rfl

theorem cell22_1787078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1787078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787078 prefixEnd_1787078 := by exact prefixLift 1787078
  have htrace : WordTrace (prefixWord ++ tailWord_1787078) baseStart_1787078 baseEnd_1787078 := by
    simpa [prefixWord, tailWord_1787078, baseEnd_1787078] using wordTrace_append hprefix tailTrace_1787078
  have hstable : (prefixWord ++ tailWord_1787078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787078).length < 2 ^ (prefixWord ++ tailWord_1787078).sum := by decide
  have hdescent : baseEnd_1787078 < baseStart_1787078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787115 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_1787115 : Nat := 118140960795 + 1787115 * 2 ^ 59
def prefixEnd_1787115 : Nat := 4983230072969 + 3 ^ 40 * 1787115 * 2
def baseEnd_1787115 : Nat := 611765986573253758695809

theorem tailTrace_1787115 : CollatzResearch.WordTrace tailWord_1787115 prefixEnd_1787115 611765986573253758695809 := by
  unfold tailWord_1787115
  simp only [CollatzResearch.WordTrace]
  refine ⟨65181438920595044787706799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43454292613730029858471199 65181438920595044787706799)
  ·
    refine ⟨97772158380892567181560199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65181438920595044787706799 97772158380892567181560199)
    ·
      refine ⟨146658237571338850772340299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97772158380892567181560199 146658237571338850772340299)
      ·
        refine ⟨219987356357008276158510449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146658237571338850772340299 219987356357008276158510449)
        ·
          refine ⟨164990517267756207118882837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219987356357008276158510449 164990517267756207118882837)
          ·
            refine ⟨7733930496926072208697633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164990517267756207118882837 7733930496926072208697633)
            ·
              refine ⟨5800447872694554156523225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733930496926072208697633 5800447872694554156523225)
              ·
                refine ⟨4350335904520915617392419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5800447872694554156523225 4350335904520915617392419)
                ·
                  refine ⟨6525503856781373426088629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350335904520915617392419 6525503856781373426088629)
                  ·
                    refine ⟨611765986573253758695809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6525503856781373426088629 611765986573253758695809)
                    ·
                      rfl

theorem cell22_1787115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_1787115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787115 prefixEnd_1787115 := by exact prefixLift 1787115
  have htrace : WordTrace (prefixWord ++ tailWord_1787115) baseStart_1787115 baseEnd_1787115 := by
    simpa [prefixWord, tailWord_1787115, baseEnd_1787115] using wordTrace_append hprefix tailTrace_1787115
  have hstable : (prefixWord ++ tailWord_1787115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787115).length < 2 ^ (prefixWord ++ tailWord_1787115).sum := by decide
  have hdescent : baseEnd_1787115 < baseStart_1787115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787130 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1787130 : Nat := 118140960795 + 1787130 * 2 ^ 59
def prefixEnd_1787130 : Nat := 4983230072969 + 3 ^ 40 * 1787130 * 2
def baseEnd_1787130 : Nat := 611771121379798719570763

theorem tailTrace_1787130 : CollatzResearch.WordTrace tailWord_1787130 prefixEnd_1787130 611771121379798719570763 := by
  unfold tailWord_1787130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16295496503885175587375711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43454657343693801566335229 16295496503885175587375711)
  ·
    refine ⟨24443244755827763381063567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16295496503885175587375711 24443244755827763381063567)
    ·
      refine ⟨36664867133741645071595351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24443244755827763381063567 36664867133741645071595351)
      ·
        refine ⟨54997300700612467607393027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36664867133741645071595351 54997300700612467607393027)
        ·
          refine ⟨82495951050918701411089541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54997300700612467607393027 82495951050918701411089541)
          ·
            refine ⟨15467990822047256514579289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82495951050918701411089541 15467990822047256514579289)
            ·
              refine ⟨11600993116535442385934467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467990822047256514579289 11600993116535442385934467)
              ·
                refine ⟨17401489674803163578901701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600993116535442385934467 17401489674803163578901701)
                ·
                  refine ⟨3262779314025593171044069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17401489674803163578901701 3262779314025593171044069)
                  ·
                    refine ⟨611771121379798719570763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3262779314025593171044069 611771121379798719570763)
                    ·
                      rfl

theorem cell22_1787130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1787130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787130 prefixEnd_1787130 := by exact prefixLift 1787130
  have htrace : WordTrace (prefixWord ++ tailWord_1787130) baseStart_1787130 baseEnd_1787130 := by
    simpa [prefixWord, tailWord_1787130, baseEnd_1787130] using wordTrace_append hprefix tailTrace_1787130
  have hstable : (prefixWord ++ tailWord_1787130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787130).length < 2 ^ (prefixWord ++ tailWord_1787130).sum := by decide
  have hdescent : baseEnd_1787130 < baseStart_1787130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787134 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1787134 : Nat := 118140960795 + 1787134 * 2 ^ 59
def prefixEnd_1787134 : Nat := 4983230072969 + 3 ^ 40 * 1787134 * 2
def baseEnd_1787134 : Nat := 203924163553848014156917

theorem tailTrace_1787134 : CollatzResearch.WordTrace tailWord_1787134 prefixEnd_1787134 203924163553848014156917 := by
  unfold tailWord_1787134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147766488440776379081057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43454754605017474021765637 8147766488440776379081057)
  ·
    refine ⟨6110824866330582284310793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8147766488440776379081057 6110824866330582284310793)
    ·
      refine ⟨4583118649747936713233095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6110824866330582284310793 4583118649747936713233095)
      ·
        refine ⟨6874677974621905069849643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583118649747936713233095 6874677974621905069849643)
        ·
          refine ⟨10312016961932857604774465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874677974621905069849643 10312016961932857604774465)
          ·
            refine ⟨7734012721449643203580849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312016961932857604774465 7734012721449643203580849)
            ·
              refine ⟨5800509541087232402685637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734012721449643203580849 5800509541087232402685637)
              ·
                refine ⟨1087595538953856075503557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5800509541087232402685637 1087595538953856075503557)
                ·
                  refine ⟨203924163553848014156917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087595538953856075503557 203924163553848014156917)
                  ·
                    rfl

theorem cell22_1787134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1787134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787134 prefixEnd_1787134 := by exact prefixLift 1787134
  have htrace : WordTrace (prefixWord ++ tailWord_1787134) baseStart_1787134 baseEnd_1787134 := by
    simpa [prefixWord, tailWord_1787134, baseEnd_1787134] using wordTrace_append hprefix tailTrace_1787134
  have hstable : (prefixWord ++ tailWord_1787134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787134).length < 2 ^ (prefixWord ++ tailWord_1787134).sum := by decide
  have hdescent : baseEnd_1787134 < baseStart_1787134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787162 : List Nat := [3, 1, 1, 3, 3, 1, 4, 6]
def baseStart_1787162 : Nat := 118140960795 + 1787162 * 2 ^ 59
def prefixEnd_1787162 : Nat := 4983230072969 + 3 ^ 40 * 1787162 * 2
def baseEnd_1787162 : Nat := 67975786181529033641185

theorem tailTrace_1787162 : CollatzResearch.WordTrace tailWord_1787162 prefixEnd_1787162 67975786181529033641185 := by
  unfold tailWord_1787162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16295788287856192953666935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43455435434283181209778493 16295788287856192953666935)
  ·
    refine ⟨24443682431784289430500403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16295788287856192953666935 24443682431784289430500403)
    ·
      refine ⟨36665523647676434145750605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24443682431784289430500403 36665523647676434145750605)
      ·
        refine ⟨13749571367878662804656477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36665523647676434145750605 13749571367878662804656477)
        ·
          refine ⟨5156089262954498551746179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13749571367878662804656477 5156089262954498551746179)
          ·
            refine ⟨7734133894431747827619269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156089262954498551746179 7734133894431747827619269)
            ·
              refine ⟨1450150105205952717678613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7734133894431747827619269 1450150105205952717678613)
              ·
                refine ⟨67975786181529033641185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1450150105205952717678613 67975786181529033641185)
                ·
                  rfl

theorem cell22_1787162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_1787162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787162 prefixEnd_1787162 := by exact prefixLift 1787162
  have htrace : WordTrace (prefixWord ++ tailWord_1787162) baseStart_1787162 baseEnd_1787162 := by
    simpa [prefixWord, tailWord_1787162, baseEnd_1787162] using wordTrace_append hprefix tailTrace_1787162
  have hstable : (prefixWord ++ tailWord_1787162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787162).length < 2 ^ (prefixWord ++ tailWord_1787162).sum := by decide
  have hdescent : baseEnd_1787162 < baseStart_1787162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1787205 : Nat := 118140960795 + 1787205 * 2 ^ 59
def prefixEnd_1787205 : Nat := 4983230072969 + 3 ^ 40 * 1787205 * 2
def baseEnd_1787205 : Nat := 611796795412523523945533

theorem tailTrace_1787205 : CollatzResearch.WordTrace tailWord_1787205 prefixEnd_1787205 611796795412523523945533 := by
  unfold tailWord_1787205
  simp only [CollatzResearch.WordTrace]
  refine ⟨65184721490268990158483069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43456480993512660105655379 65184721490268990158483069)
  ·
    refine ⟨24444270558850871309431151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65184721490268990158483069 24444270558850871309431151)
    ·
      refine ⟨36666405838276306964146727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24444270558850871309431151 36666405838276306964146727)
      ·
        refine ⟨54999608757414460446220091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36666405838276306964146727 54999608757414460446220091)
        ·
          refine ⟨82499413136121690669330137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54999608757414460446220091 82499413136121690669330137)
          ·
            refine ⟨61874559852091268001997603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82499413136121690669330137 61874559852091268001997603)
            ·
              refine ⟨92811839778136902002996405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61874559852091268001997603 92811839778136902002996405)
              ·
                refine ⟨8701109979200334562780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92811839778136902002996405 8701109979200334562780913)
                ·
                  refine ⟨6525832484400250922085685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8701109979200334562780913 6525832484400250922085685)
                  ·
                    refine ⟨611796795412523523945533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6525832484400250922085685 611796795412523523945533)
                    ·
                      rfl

theorem cell22_1787205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1787205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787205 prefixEnd_1787205 := by exact prefixLift 1787205
  have htrace : WordTrace (prefixWord ++ tailWord_1787205) baseStart_1787205 baseEnd_1787205 := by
    simpa [prefixWord, tailWord_1787205, baseEnd_1787205] using wordTrace_append hprefix tailTrace_1787205
  have hstable : (prefixWord ++ tailWord_1787205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787205).length < 2 ^ (prefixWord ++ tailWord_1787205).sum := by decide
  have hdescent : baseEnd_1787205 < baseStart_1787205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787207 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 5]
def baseStart_1787207 : Nat := 118140960795 + 1787207 * 2 ^ 59
def prefixEnd_1787207 : Nat := 4983230072969 + 3 ^ 40 * 1787207 * 2
def baseEnd_1787207 : Nat := 203932493351132061798509

theorem tailTrace_1787207 : CollatzResearch.WordTrace tailWord_1787207 prefixEnd_1787207 203932493351132061798509 := by
  unfold tailWord_1787207
  simp only [CollatzResearch.WordTrace]
  refine ⟨65184794436261744500055875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43456529624174496333370583 65184794436261744500055875)
  ·
    refine ⟨97777191654392616750083813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65184794436261744500055875 97777191654392616750083813)
    ·
      refine ⟨18333223435198615640640715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97777191654392616750083813 18333223435198615640640715)
      ·
        refine ⟨27499835152797923460961073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18333223435198615640640715 27499835152797923460961073)
        ·
          refine ⟨20624876364598442595720805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27499835152797923460961073 20624876364598442595720805)
          ·
            refine ⟨3867164318362207986697651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20624876364598442595720805 3867164318362207986697651)
            ·
              refine ⟨5800746477543311980046477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867164318362207986697651 5800746477543311980046477)
              ·
                refine ⟨2175279929078741992517429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800746477543311980046477 2175279929078741992517429)
                ·
                  refine ⟨203932493351132061798509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175279929078741992517429 203932493351132061798509)
                  ·
                    rfl

theorem cell22_1787207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 5].length) (baseStart_1787207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787207 prefixEnd_1787207 := by exact prefixLift 1787207
  have htrace : WordTrace (prefixWord ++ tailWord_1787207) baseStart_1787207 baseEnd_1787207 := by
    simpa [prefixWord, tailWord_1787207, baseEnd_1787207] using wordTrace_append hprefix tailTrace_1787207
  have hstable : (prefixWord ++ tailWord_1787207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787207).length < 2 ^ (prefixWord ++ tailWord_1787207).sum := by decide
  have hdescent : baseEnd_1787207 < baseStart_1787207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787267 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_1787267 : Nat := 118140960795 + 1787267 * 2 ^ 59
def prefixEnd_1787267 : Nat := 4983230072969 + 3 ^ 40 * 1787267 * 2
def baseEnd_1787267 : Nat := 611818019279576028895343

theorem tailTrace_1787267 : CollatzResearch.WordTrace tailWord_1787267 prefixEnd_1787267 611818019279576028895343 := by
  unfold tailWord_1787267
  simp only [CollatzResearch.WordTrace]
  refine ⟨65186982816044374747240055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43457988544029583164826703 65186982816044374747240055)
  ·
    refine ⟨97780474224066562120860083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65186982816044374747240055 97780474224066562120860083)
    ·
      refine ⟨146670711336099843181290125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97780474224066562120860083 146670711336099843181290125)
      ·
        refine ⟨55001516751037441192983797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146670711336099843181290125 55001516751037441192983797)
        ·
          refine ⟨5156392195409760111842231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55001516751037441192983797 5156392195409760111842231)
          ·
            refine ⟨7734588293114640167763347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156392195409760111842231 7734588293114640167763347)
            ·
              refine ⟨11601882439671960251645021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734588293114640167763347 11601882439671960251645021)
              ·
                refine ⟨4350705914876985094366883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11601882439671960251645021 4350705914876985094366883)
                ·
                  refine ⟨6526058872315477641550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350705914876985094366883 6526058872315477641550325)
                  ·
                    refine ⟨611818019279576028895343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6526058872315477641550325 611818019279576028895343)
                    ·
                      rfl

theorem cell22_1787267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_1787267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787267 prefixEnd_1787267 := by exact prefixLift 1787267
  have htrace : WordTrace (prefixWord ++ tailWord_1787267) baseStart_1787267 baseEnd_1787267 := by
    simpa [prefixWord, tailWord_1787267, baseEnd_1787267] using wordTrace_append hprefix tailTrace_1787267
  have hstable : (prefixWord ++ tailWord_1787267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787267).length < 2 ^ (prefixWord ++ tailWord_1787267).sum := by decide
  have hdescent : baseEnd_1787267 < baseStart_1787267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787284 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1787284 : Nat := 118140960795 + 1787284 * 2 ^ 59
def prefixEnd_1787284 : Nat := 4983230072969 + 3 ^ 40 * 1787284 * 2
def baseEnd_1787284 : Nat := 611823838726993651220291

theorem tailTrace_1787284 : CollatzResearch.WordTrace tailWord_1787284 prefixEnd_1787284 611823838726993651220291 := by
  unfold tailWord_1787284
  simp only [CollatzResearch.WordTrace]
  refine ⟨32593801428491393325304453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43458401904655191100405937 32593801428491393325304453)
  ·
    refine ⟨6111337767842136248494585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32593801428491393325304453 6111337767842136248494585)
    ·
      refine ⟨4583503325881602186370939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6111337767842136248494585 4583503325881602186370939)
      ·
        refine ⟨6875254988822403279556409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583503325881602186370939 6875254988822403279556409)
        ·
          refine ⟨5156441241616802459667307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6875254988822403279556409 5156441241616802459667307)
          ·
            refine ⟨7734661862425203689500961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156441241616802459667307 7734661862425203689500961)
            ·
              refine ⟨5800996396818902767125721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734661862425203689500961 5800996396818902767125721)
              ·
                refine ⟨4350747297614177075344291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5800996396818902767125721 4350747297614177075344291)
                ·
                  refine ⟨6526120946421265613016437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350747297614177075344291 6526120946421265613016437)
                  ·
                    refine ⟨611823838726993651220291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6526120946421265613016437 611823838726993651220291)
                    ·
                      rfl

theorem cell22_1787284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1787284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787284 prefixEnd_1787284 := by exact prefixLift 1787284
  have htrace : WordTrace (prefixWord ++ tailWord_1787284) baseStart_1787284 baseEnd_1787284 := by
    simpa [prefixWord, tailWord_1787284, baseEnd_1787284] using wordTrace_append hprefix tailTrace_1787284
  have hstable : (prefixWord ++ tailWord_1787284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787284).length < 2 ^ (prefixWord ++ tailWord_1787284).sum := by decide
  have hdescent : baseEnd_1787284 < baseStart_1787284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787288 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_1787288 : Nat := 118140960795 + 1787288 * 2 ^ 59
def prefixEnd_1787288 : Nat := 4983230072969 + 3 ^ 40 * 1787288 * 2
def baseEnd_1787288 : Nat := 611825208008738974120279

theorem tailTrace_1787288 : CollatzResearch.WordTrace tailWord_1787288 prefixEnd_1787288 611825208008738974120279 := by
  unfold tailWord_1787288
  simp only [CollatzResearch.WordTrace]
  refine ⟨32593874374484147666877259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43458499165978863555836345 32593874374484147666877259)
  ·
    refine ⟨48890811561726221500315889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32593874374484147666877259 48890811561726221500315889)
    ·
      refine ⟨36668108671294666125236917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48890811561726221500315889 36668108671294666125236917)
      ·
        refine ⟨3437635187933874949240961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36668108671294666125236917 3437635187933874949240961)
        ·
          refine ⟨2578226390950406211930721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3437635187933874949240961 2578226390950406211930721)
          ·
            refine ⟨1933669793212804658948041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2578226390950406211930721 1933669793212804658948041)
            ·
              refine ⟨1450252344909603494211031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933669793212804658948041 1450252344909603494211031)
              ·
                refine ⟨2175378517364405241316547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450252344909603494211031 2175378517364405241316547)
                ·
                  refine ⟨3263067776046607861974821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175378517364405241316547 3263067776046607861974821)
                  ·
                    refine ⟨611825208008738974120279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263067776046607861974821 611825208008738974120279)
                    ·
                      rfl

theorem cell22_1787288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_1787288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787288 prefixEnd_1787288 := by exact prefixLift 1787288
  have htrace : WordTrace (prefixWord ++ tailWord_1787288) baseStart_1787288 baseEnd_1787288 := by
    simpa [prefixWord, tailWord_1787288, baseEnd_1787288] using wordTrace_append hprefix tailTrace_1787288
  have hstable : (prefixWord ++ tailWord_1787288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787288).length < 2 ^ (prefixWord ++ tailWord_1787288).sum := by decide
  have hdescent : baseEnd_1787288 < baseStart_1787288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787342 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1787342 : Nat := 118140960795 + 1787342 * 2 ^ 59
def prefixEnd_1787342 : Nat := 4983230072969 + 3 ^ 40 * 1787342 * 2
def baseEnd_1787342 : Nat := 203947897770766944423371

theorem tailTrace_1787342 : CollatzResearch.WordTrace tailWord_1787342 prefixEnd_1787342 203947897770766944423371 := by
  unfold tailWord_1787342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148714786346582819527535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43459812193848441704146853 8148714786346582819527535)
  ·
    refine ⟨12223072179519874229291303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8148714786346582819527535 12223072179519874229291303)
    ·
      refine ⟨18334608269279811343936955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223072179519874229291303 18334608269279811343936955)
      ·
        refine ⟨27501912403919717015905433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18334608269279811343936955 27501912403919717015905433)
        ·
          refine ⟨20626434302939787761929075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27501912403919717015905433 20626434302939787761929075)
          ·
            refine ⟨30939651454409681642893613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20626434302939787761929075 30939651454409681642893613)
            ·
              refine ⟨11602369295403630616085105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30939651454409681642893613 11602369295403630616085105)
              ·
                refine ⟨8701776971552722962063829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602369295403630616085105 8701776971552722962063829)
                ·
                  refine ⟨203947897770766944423371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8701776971552722962063829 203947897770766944423371)
                  ·
                    rfl

theorem cell22_1787342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1787342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787342 prefixEnd_1787342 := by exact prefixLift 1787342
  have htrace : WordTrace (prefixWord ++ tailWord_1787342) baseStart_1787342 baseEnd_1787342 := by
    simpa [prefixWord, tailWord_1787342, baseEnd_1787342] using wordTrace_append hprefix tailTrace_1787342
  have hstable : (prefixWord ++ tailWord_1787342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787342).length < 2 ^ (prefixWord ++ tailWord_1787342).sum := by decide
  have hdescent : baseEnd_1787342 < baseStart_1787342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787376 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_1787376 : Nat := 118140960795 + 1787376 * 2 ^ 59
def prefixEnd_1787376 : Nat := 4983230072969 + 3 ^ 40 * 1787376 * 2
def baseEnd_1787376 : Nat := 203951777402378692640003

theorem tailTrace_1787376 : CollatzResearch.WordTrace tailWord_1787376 prefixEnd_1787376 203951777402378692640003 := by
  unfold tailWord_1787376
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595479186324743181478991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43460638915099657575305321 32595479186324743181478991)
  ·
    refine ⟨48893218779487114772218487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32595479186324743181478991 48893218779487114772218487)
    ·
      refine ⟨73339828169230672158327731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48893218779487114772218487 73339828169230672158327731)
      ·
        refine ⟨110009742253846008237491597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73339828169230672158327731 110009742253846008237491597)
        ·
          refine ⟨41253653345192253089059349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110009742253846008237491597 41253653345192253089059349)
          ·
            refine ⟨1933765000555886863549657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41253653345192253089059349 1933765000555886863549657)
            ·
              refine ⟨1450323750416915147662243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933765000555886863549657 1450323750416915147662243)
              ·
                refine ⟨2175485625625372721493365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450323750416915147662243 2175485625625372721493365)
                ·
                  refine ⟨203951777402378692640003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175485625625372721493365 203951777402378692640003)
                  ·
                    rfl

theorem cell22_1787376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_1787376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787376 prefixEnd_1787376 := by exact prefixLift 1787376
  have htrace : WordTrace (prefixWord ++ tailWord_1787376) baseStart_1787376 baseEnd_1787376 := by
    simpa [prefixWord, tailWord_1787376, baseEnd_1787376] using wordTrace_append hprefix tailTrace_1787376
  have hstable : (prefixWord ++ tailWord_1787376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787376).length < 2 ^ (prefixWord ++ tailWord_1787376).sum := by decide
  have hdescent : baseEnd_1787376 < baseStart_1787376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787389 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1787389 : Nat := 118140960795 + 1787389 * 2 ^ 59
def prefixEnd_1787389 : Nat := 4983230072969 + 3 ^ 40 * 1787389 * 2
def baseEnd_1787389 : Nat := 611859782372808377344969

theorem tailTrace_1787389 : CollatzResearch.WordTrace tailWord_1787389 prefixEnd_1787389 611859782372808377344969 := by
  unfold tailWord_1787389
  simp only [CollatzResearch.WordTrace]
  refine ⟨65191432521602389583181221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43460955014401593055454147 65191432521602389583181221)
  ·
    refine ⟨12223393597800448046846479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65191432521602389583181221 12223393597800448046846479)
    ·
      refine ⟨18335090396700672070269719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223393597800448046846479 18335090396700672070269719)
      ·
        refine ⟨27502635595051008105404579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18335090396700672070269719 27502635595051008105404579)
        ·
          refine ⟨41253953392576512158106869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27502635595051008105404579 41253953392576512158106869)
          ·
            refine ⟨3867558130554048014822519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41253953392576512158106869 3867558130554048014822519)
            ·
              refine ⟨5801337195831072022233779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867558130554048014822519 5801337195831072022233779)
              ·
                refine ⟨8702005793746608033350669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801337195831072022233779 8702005793746608033350669)
                ·
                  refine ⟨3263252172654978012506501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8702005793746608033350669 3263252172654978012506501)
                  ·
                    refine ⟨611859782372808377344969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263252172654978012506501 611859782372808377344969)
                    ·
                      rfl

theorem cell22_1787389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1787389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787389 prefixEnd_1787389 := by exact prefixLift 1787389
  have htrace : WordTrace (prefixWord ++ tailWord_1787389) baseStart_1787389 baseEnd_1787389 := by
    simpa [prefixWord, tailWord_1787389, baseEnd_1787389] using wordTrace_append hprefix tailTrace_1787389
  have hstable : (prefixWord ++ tailWord_1787389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787389).length < 2 ^ (prefixWord ++ tailWord_1787389).sum := by decide
  have hdescent : baseEnd_1787389 < baseStart_1787389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787421 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 4]
def baseStart_1787421 : Nat := 118140960795 + 1787421 * 2 ^ 59
def prefixEnd_1787421 : Nat := 4983230072969 + 3 ^ 40 * 1787421 * 2
def baseEnd_1787421 : Nat := 203956912208923653514957

theorem tailTrace_1787421 : CollatzResearch.WordTrace tailWord_1787421 prefixEnd_1787421 203956912208923653514957 := by
  unfold tailWord_1787421
  simp only [CollatzResearch.WordTrace]
  refine ⟨65192599657486459048346117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43461733104990972698897411 65192599657486459048346117)
  ·
    refine ⟨12223612435778711071564897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65192599657486459048346117 12223612435778711071564897)
    ·
      refine ⟨9167709326834033303673673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12223612435778711071564897 9167709326834033303673673)
      ·
        refine ⟨6875781995125524977755255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9167709326834033303673673 6875781995125524977755255)
        ·
          refine ⟨10313672992688287466632883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875781995125524977755255 10313672992688287466632883)
          ·
            refine ⟨15470509489032431199949325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313672992688287466632883 15470509489032431199949325)
            ·
              refine ⟨5801441058387161699980997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15470509489032431199949325 5801441058387161699980997)
              ·
                refine ⟨1087770198447592818746437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5801441058387161699980997 1087770198447592818746437)
                ·
                  refine ⟨203956912208923653514957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087770198447592818746437 203956912208923653514957)
                  ·
                    rfl

theorem cell22_1787421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1787421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787421 prefixEnd_1787421 := by exact prefixLift 1787421
  have htrace : WordTrace (prefixWord ++ tailWord_1787421) baseStart_1787421 baseEnd_1787421 := by
    simpa [prefixWord, tailWord_1787421, baseEnd_1787421] using wordTrace_append hprefix tailTrace_1787421
  have hstable : (prefixWord ++ tailWord_1787421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787421).length < 2 ^ (prefixWord ++ tailWord_1787421).sum := by decide
  have hdescent : baseEnd_1787421 < baseStart_1787421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787434 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1787434 : Nat := 118140960795 + 1787434 * 2 ^ 59
def prefixEnd_1787434 : Nat := 4983230072969 + 3 ^ 40 * 1787434 * 2
def baseEnd_1787434 : Nat := 611875186792443259969831

theorem tailTrace_1787434 : CollatzResearch.WordTrace tailWord_1787434 prefixEnd_1787434 611875186792443259969831 := by
  unfold tailWord_1787434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16298268451609840567142339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43462049204292908179046237 16298268451609840567142339)
  ·
    refine ⟨24447402677414760850713509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16298268451609840567142339 24447402677414760850713509)
    ·
      refine ⟨4583888002015267659508783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24447402677414760850713509 4583888002015267659508783)
      ·
        refine ⟨6875832003022901489263175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583888002015267659508783 6875832003022901489263175)
        ·
          refine ⟨10313748004534352233894763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875832003022901489263175 10313748004534352233894763)
          ·
            refine ⟨15470622006801528350842145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313748004534352233894763 15470622006801528350842145)
            ·
              refine ⟨11602966505101146263131609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15470622006801528350842145 11602966505101146263131609)
              ·
                refine ⟨8702224878825859697348707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602966505101146263131609 8702224878825859697348707)
                ·
                  refine ⟨13053337318238789546023061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702224878825859697348707 13053337318238789546023061)
                  ·
                    refine ⟨611875186792443259969831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13053337318238789546023061 611875186792443259969831)
                    ·
                      rfl

theorem cell22_1787434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1787434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787434 prefixEnd_1787434 := by exact prefixLift 1787434
  have htrace : WordTrace (prefixWord ++ tailWord_1787434) baseStart_1787434 baseEnd_1787434 := by
    simpa [prefixWord, tailWord_1787434, baseEnd_1787434] using wordTrace_append hprefix tailTrace_1787434
  have hstable : (prefixWord ++ tailWord_1787434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787434).length < 2 ^ (prefixWord ++ tailWord_1787434).sum := by decide
  have hdescent : baseEnd_1787434 < baseStart_1787434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787601 : List Nat := [1, 2, 2, 1, 2, 6, 1, 7]
def baseStart_1787601 : Nat := 118140960795 + 1787601 * 2 ^ 59
def prefixEnd_1787601 : Nat := 4983230072969 + 3 ^ 40 * 1787601 * 2
def baseEnd_1787601 : Nat := 67992483811701165671591

theorem tailTrace_1787601 : CollatzResearch.WordTrace tailWord_1787601 prefixEnd_1787601 67992483811701165671591 := by
  unfold tailWord_1787601
  simp only [CollatzResearch.WordTrace]
  refine ⟨65199164796834349789898657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43466109864556233193265771 65199164796834349789898657)
  ·
    refine ⟨48899373597625762342423993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65199164796834349789898657 48899373597625762342423993)
    ·
      refine ⟨36674530198219321756817995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48899373597625762342423993 36674530198219321756817995)
      ·
        refine ⟨55011795297328982635226993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36674530198219321756817995 55011795297328982635226993)
        ·
          refine ⟨41258846472996736976420245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55011795297328982635226993 41258846472996736976420245)
          ·
            refine ⟨1934008428421722045769699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41258846472996736976420245 1934008428421722045769699)
            ·
              refine ⟨2901012642632583068654549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934008428421722045769699 2901012642632583068654549)
              ·
                refine ⟨67992483811701165671591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2901012642632583068654549 67992483811701165671591)
                ·
                  rfl

theorem cell22_1787601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 7].length) (baseStart_1787601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787601 prefixEnd_1787601 := by exact prefixLift 1787601
  have htrace : WordTrace (prefixWord ++ tailWord_1787601) baseStart_1787601 baseEnd_1787601 := by
    simpa [prefixWord, tailWord_1787601, baseEnd_1787601] using wordTrace_append hprefix tailTrace_1787601
  have hstable : (prefixWord ++ tailWord_1787601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787601).length < 2 ^ (prefixWord ++ tailWord_1787601).sum := by decide
  have hdescent : baseEnd_1787601 < baseStart_1787601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787616 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_1787616 : Nat := 118140960795 + 1787616 * 2 ^ 59
def prefixEnd_1787616 : Nat := 4983230072969 + 3 ^ 40 * 1787616 * 2
def baseEnd_1787616 : Nat := 611937489111855451919273

theorem tailTrace_1787616 : CollatzResearch.WordTrace tailWord_1787616 prefixEnd_1787616 611937489111855451919273 := by
  unfold tailWord_1787616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32599855945890003675847351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43466474594520004901129801 32599855945890003675847351)
  ·
    refine ⟨48899783918835005513771027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32599855945890003675847351 48899783918835005513771027)
    ·
      refine ⟨73349675878252508270656541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48899783918835005513771027 73349675878252508270656541)
      ·
        refine ⟨27506128454344690601496203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73349675878252508270656541 27506128454344690601496203)
        ·
          refine ⟨41259192681517035902244305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27506128454344690601496203 41259192681517035902244305)
          ·
            refine ⟨30944394511137776926683229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41259192681517035902244305 30944394511137776926683229)
            ·
              refine ⟨11604147941676666347506211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30944394511137776926683229 11604147941676666347506211)
              ·
                refine ⟨17406221912514999521259317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604147941676666347506211 17406221912514999521259317)
                ·
                  refine ⟨1631833304298281205118061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17406221912514999521259317 1631833304298281205118061)
                  ·
                    refine ⟨611937489111855451919273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631833304298281205118061 611937489111855451919273)
                    ·
                      rfl

theorem cell22_1787616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_1787616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787616 prefixEnd_1787616 := by exact prefixLift 1787616
  have htrace : WordTrace (prefixWord ++ tailWord_1787616) baseStart_1787616 baseEnd_1787616 := by
    simpa [prefixWord, tailWord_1787616, baseEnd_1787616] using wordTrace_append hprefix tailTrace_1787616
  have hstable : (prefixWord ++ tailWord_1787616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787616).length < 2 ^ (prefixWord ++ tailWord_1787616).sum := by decide
  have hdescent : baseEnd_1787616 < baseStart_1787616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787650 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1787650 : Nat := 118140960795 + 1787650 * 2 ^ 59
def prefixEnd_1787650 : Nat := 4983230072969 + 3 ^ 40 * 1787650 * 2
def baseEnd_1787650 : Nat := 611949128006690696569169

theorem tailTrace_1787650 : CollatzResearch.WordTrace tailWord_1787650 prefixEnd_1787650 611949128006690696569169 := by
  unfold tailWord_1787650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16300237993414207789608101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43467301315771220772288269 16300237993414207789608101)
  ·
    refine ⟨3056294623765163960551519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16300237993414207789608101 3056294623765163960551519)
    ·
      refine ⟨4584441935647745940827279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056294623765163960551519 4584441935647745940827279)
      ·
        refine ⟨6876662903471618911240919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584441935647745940827279 6876662903471618911240919)
        ·
          refine ⟨10314994355207428366861379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876662903471618911240919 10314994355207428366861379)
          ·
            refine ⟨15472491532811142550292069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10314994355207428366861379 15472491532811142550292069)
            ·
              refine ⟨2901092162402089228179763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15472491532811142550292069 2901092162402089228179763)
              ·
                refine ⟨4351638243603133842269645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901092162402089228179763 4351638243603133842269645)
                ·
                  refine ⟨1631864341351175190851117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4351638243603133842269645 1631864341351175190851117)
                  ·
                    refine ⟨611949128006690696569169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631864341351175190851117 611949128006690696569169)
                    ·
                      rfl

theorem cell22_1787650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1787650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787650 prefixEnd_1787650 := by exact prefixLift 1787650
  have htrace : WordTrace (prefixWord ++ tailWord_1787650) baseStart_1787650 baseEnd_1787650 := by
    simpa [prefixWord, tailWord_1787650, baseEnd_1787650] using wordTrace_append hprefix tailTrace_1787650
  have hstable : (prefixWord ++ tailWord_1787650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787650).length < 2 ^ (prefixWord ++ tailWord_1787650).sum := by decide
  have hdescent : baseEnd_1787650 < baseStart_1787650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787708 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_1787708 : Nat := 118140960795 + 1787708 * 2 ^ 59
def prefixEnd_1787708 : Nat := 4983230072969 + 3 ^ 40 * 1787708 * 2
def baseEnd_1787708 : Nat := 203989660863999292872997

theorem tailTrace_1787708 : CollatzResearch.WordTrace tailWord_1787708 prefixEnd_1787708 203989660863999292872997 := by
  unfold tailWord_1787708
  simp only [CollatzResearch.WordTrace]
  refine ⟨32601533703723353532021889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43468711604964471376029185 32601533703723353532021889)
  ·
    refine ⟨24451150277792515149016417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32601533703723353532021889 24451150277792515149016417)
    ·
      refine ⟨18338362708344386361762313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24451150277792515149016417 18338362708344386361762313)
      ·
        refine ⟨13753772031258289771321735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18338362708344386361762313 13753772031258289771321735)
        ·
          refine ⟨20630658046887434656982603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13753772031258289771321735 20630658046887434656982603)
          ·
            refine ⟨30945987070331151985473905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20630658046887434656982603 30945987070331151985473905)
            ·
              refine ⟨23209490302748363989105429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30945987070331151985473905 23209490302748363989105429)
              ·
                refine ⟨1087944857941329561989317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23209490302748363989105429 1087944857941329561989317)
                ·
                  refine ⟨203989660863999292872997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087944857941329561989317 203989660863999292872997)
                  ·
                    rfl

theorem cell22_1787708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_1787708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787708 prefixEnd_1787708 := by exact prefixLift 1787708
  have htrace : WordTrace (prefixWord ++ tailWord_1787708) baseStart_1787708 baseEnd_1787708 := by
    simpa [prefixWord, tailWord_1787708, baseEnd_1787708] using wordTrace_append hprefix tailTrace_1787708
  have hstable : (prefixWord ++ tailWord_1787708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787708).length < 2 ^ (prefixWord ++ tailWord_1787708).sum := by decide
  have hdescent : baseEnd_1787708 < baseStart_1787708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787721 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_1787721 : Nat := 118140960795 + 1787721 * 2 ^ 59
def prefixEnd_1787721 : Nat := 4983230072969 + 3 ^ 40 * 1787721 * 2
def baseEnd_1787721 : Nat := 611973432757670178043951

theorem tailTrace_1787721 : CollatzResearch.WordTrace tailWord_1787721 prefixEnd_1787721 611973432757670178043951 := by
  unfold tailWord_1787721
  simp only [CollatzResearch.WordTrace]
  refine ⟨65203541556399610284267017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43469027704266406856178011 65203541556399610284267017)
  ·
    refine ⟨48902656167299707713200263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65203541556399610284267017 48902656167299707713200263)
    ·
      refine ⟨73353984250949561569800395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48902656167299707713200263 73353984250949561569800395)
      ·
        refine ⟨110030976376424342354700593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73353984250949561569800395 110030976376424342354700593)
        ·
          refine ⟨82523232282318256766025445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110030976376424342354700593 82523232282318256766025445)
          ·
            refine ⟨15473106052934673143629771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82523232282318256766025445 15473106052934673143629771)
            ·
              refine ⟨23209659079402009715444657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15473106052934673143629771 23209659079402009715444657)
              ·
                refine ⟨17407244309551507286583493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23209659079402009715444657 17407244309551507286583493)
                ·
                  refine ⟨3263858308040907616234405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17407244309551507286583493 3263858308040907616234405)
                  ·
                    refine ⟨611973432757670178043951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263858308040907616234405 611973432757670178043951)
                    ·
                      rfl

theorem cell22_1787721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_1787721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787721 prefixEnd_1787721 := by exact prefixLift 1787721
  have htrace : WordTrace (prefixWord ++ tailWord_1787721) baseStart_1787721 baseEnd_1787721 := by
    simpa [prefixWord, tailWord_1787721, baseEnd_1787721] using wordTrace_append hprefix tailTrace_1787721
  have hstable : (prefixWord ++ tailWord_1787721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787721).length < 2 ^ (prefixWord ++ tailWord_1787721).sum := by decide
  have hdescent : baseEnd_1787721 < baseStart_1787721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787738 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_1787738 : Nat := 118140960795 + 1787738 * 2 ^ 59
def prefixEnd_1787738 : Nat := 4983230072969 + 3 ^ 40 * 1787738 * 2
def baseEnd_1787738 : Nat := 611979252205087800368899

theorem tailTrace_1787738 : CollatzResearch.WordTrace tailWord_1787738 prefixEnd_1787738 611979252205087800368899 := by
  unfold tailWord_1787738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301040399334505546908967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43469441064892014791757245 16301040399334505546908967)
  ·
    refine ⟨24451560599001758320363451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16301040399334505546908967 24451560599001758320363451)
    ·
      refine ⟨36677340898502637480545177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24451560599001758320363451 36677340898502637480545177)
      ·
        refine ⟨27508005673876978110408883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36677340898502637480545177 27508005673876978110408883)
        ·
          refine ⟨41262008510815467165613325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27508005673876978110408883 41262008510815467165613325)
          ·
            refine ⟨15473253191555800187104997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41262008510815467165613325 15473253191555800187104997)
            ·
              refine ⟨2901234973416712535082187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15473253191555800187104997 2901234973416712535082187)
              ·
                refine ⟨4351852460125068802623281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901234973416712535082187 4351852460125068802623281)
                ·
                  refine ⟨3263889345093801601967461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351852460125068802623281 3263889345093801601967461)
                  ·
                    refine ⟨611979252205087800368899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3263889345093801601967461 611979252205087800368899)
                    ·
                      rfl

theorem cell22_1787738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_1787738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787738 prefixEnd_1787738 := by exact prefixLift 1787738
  have htrace : WordTrace (prefixWord ++ tailWord_1787738) baseStart_1787738 baseEnd_1787738 := by
    simpa [prefixWord, tailWord_1787738, baseEnd_1787738] using wordTrace_append hprefix tailTrace_1787738
  have hstable : (prefixWord ++ tailWord_1787738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787738).length < 2 ^ (prefixWord ++ tailWord_1787738).sum := by decide
  have hdescent : baseEnd_1787738 < baseStart_1787738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787740 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1787740 : Nat := 118140960795 + 1787740 * 2 ^ 59
def prefixEnd_1787740 : Nat := 4983230072969 + 3 ^ 40 * 1787740 * 2
def baseEnd_1787740 : Nat := 611979936845960461818893

theorem tailTrace_1787740 : CollatzResearch.WordTrace tailWord_1787740 prefixEnd_1787740 611979936845960461818893 := by
  unfold tailWord_1787740
  simp only [CollatzResearch.WordTrace]
  refine ⟨32602117271665388264604337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43469489695553851019472449 32602117271665388264604337)
  ·
    refine ⟨24451587953749041198453253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32602117271665388264604337 24451587953749041198453253)
    ·
      refine ⟨4584672741327945224709985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24451587953749041198453253 4584672741327945224709985)
      ·
        refine ⟨3438504555995958918532489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4584672741327945224709985 3438504555995958918532489)
        ·
          refine ⟨2578878416996969188899367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3438504555995958918532489 2578878416996969188899367)
          ·
            refine ⟨3868317625495453783349051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578878416996969188899367 3868317625495453783349051)
            ·
              refine ⟨5802476438243180675023577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868317625495453783349051 5802476438243180675023577)
              ·
                refine ⟨4351857328682385506267683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802476438243180675023577 4351857328682385506267683)
                ·
                  refine ⟨6527785993023578259401525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351857328682385506267683 6527785993023578259401525)
                  ·
                    refine ⟨611979936845960461818893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6527785993023578259401525 611979936845960461818893)
                    ·
                      rfl

theorem cell22_1787740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1787740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787740 prefixEnd_1787740 := by exact prefixLift 1787740
  have htrace : WordTrace (prefixWord ++ tailWord_1787740) baseStart_1787740 baseEnd_1787740 := by
    simpa [prefixWord, tailWord_1787740, baseEnd_1787740] using wordTrace_append hprefix tailTrace_1787740
  have hstable : (prefixWord ++ tailWord_1787740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787740).length < 2 ^ (prefixWord ++ tailWord_1787740).sum := by decide
  have hdescent : baseEnd_1787740 < baseStart_1787740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787802 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_1787802 : Nat := 118140960795 + 1787802 * 2 ^ 59
def prefixEnd_1787802 : Nat := 4983230072969 + 3 ^ 40 * 1787802 * 2
def baseEnd_1787802 : Nat := 612001160713012966768703

theorem tailTrace_1787802 : CollatzResearch.WordTrace tailWord_1787802 prefixEnd_1787802 612001160713012966768703 := by
  unfold tailWord_1787802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301623967276540279491415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43470997246070774078643773 16301623967276540279491415)
  ·
    refine ⟨24452435950914810419237123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16301623967276540279491415 24452435950914810419237123)
    ·
      refine ⟨36678653926372215628855685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24452435950914810419237123 36678653926372215628855685)
      ·
        refine ⟨6877247611194790430410441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36678653926372215628855685 6877247611194790430410441)
        ·
          refine ⟨5157935708396092822807831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877247611194790430410441 5157935708396092822807831)
          ·
            refine ⟨7736903562594139234211747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157935708396092822807831 7736903562594139234211747)
            ·
              refine ⟨11605355343891208851317621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736903562594139234211747 11605355343891208851317621)
              ·
                refine ⟨1088002063489800829811027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11605355343891208851317621 1088002063489800829811027)
                ·
                  refine ⟨1632003095234701244716541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088002063489800829811027 1632003095234701244716541)
                  ·
                    refine ⟨612001160713012966768703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632003095234701244716541 612001160713012966768703)
                    ·
                      rfl

theorem cell22_1787802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_1787802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787802 prefixEnd_1787802 := by exact prefixLift 1787802
  have htrace : WordTrace (prefixWord ++ tailWord_1787802) baseStart_1787802 baseEnd_1787802 := by
    simpa [prefixWord, tailWord_1787802, baseEnd_1787802] using wordTrace_append hprefix tailTrace_1787802
  have hstable : (prefixWord ++ tailWord_1787802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787802).length < 2 ^ (prefixWord ++ tailWord_1787802).sum := by decide
  have hdescent : baseEnd_1787802 < baseStart_1787802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787815 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 5]
def baseStart_1787815 : Nat := 118140960795 + 1787815 * 2 ^ 59
def prefixEnd_1787815 : Nat := 4983230072969 + 3 ^ 40 * 1787815 * 2
def baseEnd_1787815 : Nat := 204001870292895088731221

theorem tailTrace_1787815 : CollatzResearch.WordTrace tailWord_1787815 prefixEnd_1787815 204001870292895088731221 := by
  unfold tailWord_1787815
  simp only [CollatzResearch.WordTrace]
  refine ⟨65206970018059064338188899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43471313345372709558792599 65206970018059064338188899)
  ·
    refine ⟨97810455027088596507283349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65206970018059064338188899 97810455027088596507283349)
    ·
      refine ⟨4584865079394777961278907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97810455027088596507283349 4584865079394777961278907)
      ·
        refine ⟨6877297619092166941918361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584865079394777961278907 6877297619092166941918361)
        ·
          refine ⟨5157973214319125206438771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877297619092166941918361 5157973214319125206438771)
          ·
            refine ⟨7736959821478687809658157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157973214319125206438771 7736959821478687809658157)
            ·
              refine ⟨2901359933054507928621809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7736959821478687809658157 2901359933054507928621809)
              ·
                refine ⟨2176019949790880946466357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901359933054507928621809 2176019949790880946466357)
                ·
                  refine ⟨204001870292895088731221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176019949790880946466357 204001870292895088731221)
                  ·
                    rfl

theorem cell22_1787815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 5].length) (baseStart_1787815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787815 prefixEnd_1787815 := by exact prefixLift 1787815
  have htrace : WordTrace (prefixWord ++ tailWord_1787815) baseStart_1787815 baseEnd_1787815 := by
    simpa [prefixWord, tailWord_1787815, baseEnd_1787815] using wordTrace_append hprefix tailTrace_1787815
  have hstable : (prefixWord ++ tailWord_1787815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787815).length < 2 ^ (prefixWord ++ tailWord_1787815).sum := by decide
  have hdescent : baseEnd_1787815 < baseStart_1787815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787873 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1787873 : Nat := 118140960795 + 1787873 * 2 ^ 59
def prefixEnd_1787873 : Nat := 4983230072969 + 3 ^ 40 * 1787873 * 2
def baseEnd_1787873 : Nat := 612025465463992448243485

theorem tailTrace_1787873 : CollatzResearch.WordTrace tailWord_1787873 prefixEnd_1787873 612025465463992448243485 := by
  unfold tailWord_1787873
  simp only [CollatzResearch.WordTrace]
  refine ⟨65209085451848940243800273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43472723634565960162533515 65209085451848940243800273)
  ·
    refine ⟨48906814088886705182850205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65209085451848940243800273 48906814088886705182850205)
    ·
      refine ⟨18340055283332514443568827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48906814088886705182850205 18340055283332514443568827)
      ·
        refine ⟨27510082924998771665353241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18340055283332514443568827 27510082924998771665353241)
        ·
          refine ⟨20632562193749078749014931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27510082924998771665353241 20632562193749078749014931)
          ·
            refine ⟨30948843290623618123522397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20632562193749078749014931 30948843290623618123522397)
            ·
              refine ⟨11605816233983856796320899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30948843290623618123522397 11605816233983856796320899)
              ·
                refine ⟨17408724350975785194481349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11605816233983856796320899 17408724350975785194481349)
                ·
                  refine ⟨3264135815807959723965253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17408724350975785194481349 3264135815807959723965253)
                  ·
                    refine ⟨612025465463992448243485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264135815807959723965253 612025465463992448243485)
                    ·
                      rfl

theorem cell22_1787873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1787873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787873 prefixEnd_1787873 := by exact prefixLift 1787873
  have htrace : WordTrace (prefixWord ++ tailWord_1787873) baseStart_1787873 baseEnd_1787873 := by
    simpa [prefixWord, tailWord_1787873, baseEnd_1787873] using wordTrace_append hprefix tailTrace_1787873
  have hstable : (prefixWord ++ tailWord_1787873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787873).length < 2 ^ (prefixWord ++ tailWord_1787873).sum := by decide
  have hdescent : baseEnd_1787873 < baseStart_1787873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787875 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 4, 3]
def baseStart_1787875 : Nat := 118140960795 + 1787875 * 2 ^ 59
def prefixEnd_1787875 : Nat := 4983230072969 + 3 ^ 40 * 1787875 * 2
def baseEnd_1787875 : Nat := 612026150104865109693479

theorem tailTrace_1787875 : CollatzResearch.WordTrace tailWord_1787875 prefixEnd_1787875 612026150104865109693479 := by
  unfold tailWord_1787875
  simp only [CollatzResearch.WordTrace]
  refine ⟨65209158397841694585373079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43472772265227796390248719 65209158397841694585373079)
  ·
    refine ⟨97813737596762541878059619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65209158397841694585373079 97813737596762541878059619)
    ·
      refine ⟨146720606395143812817089429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97813737596762541878059619 146720606395143812817089429)
      ·
        refine ⟨6877528424772366225801067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146720606395143812817089429 6877528424772366225801067)
        ·
          refine ⟨10316292637158549338701601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877528424772366225801067 10316292637158549338701601)
          ·
            refine ⟨7737219477868912004026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10316292637158549338701601 7737219477868912004026201)
            ·
              refine ⟨5802914608401684003019651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7737219477868912004026201 5802914608401684003019651)
              ·
                refine ⟨8704371912602526004529477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802914608401684003019651 8704371912602526004529477)
                ·
                  refine ⟨1632069733612973625849277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8704371912602526004529477 1632069733612973625849277)
                  ·
                    refine ⟨612026150104865109693479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632069733612973625849277 612026150104865109693479)
                    ·
                      rfl

theorem cell22_1787875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3].length) (baseStart_1787875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787875 prefixEnd_1787875 := by exact prefixLift 1787875
  have htrace : WordTrace (prefixWord ++ tailWord_1787875) baseStart_1787875 baseEnd_1787875 := by
    simpa [prefixWord, tailWord_1787875, baseEnd_1787875] using wordTrace_append hprefix tailTrace_1787875
  have hstable : (prefixWord ++ tailWord_1787875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787875).length < 2 ^ (prefixWord ++ tailWord_1787875).sum := by decide
  have hdescent : baseEnd_1787875 < baseStart_1787875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1787978 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1787978 : Nat := 118140960795 + 1787978 * 2 ^ 59
def prefixEnd_1787978 : Nat := 4983230072969 + 3 ^ 40 * 1787978 * 2
def baseEnd_1787978 : Nat := 204020469703269058122721

theorem tailTrace_1787978 : CollatzResearch.WordTrace tailWord_1787978 prefixEnd_1787978 204020469703269058122721 := by
  unfold tailWord_1787978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303228779117135794093147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43475276744312362117581725 16303228779117135794093147)
  ·
    refine ⟨24454843168675703691139721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16303228779117135794093147 24454843168675703691139721)
    ·
      refine ⟨18341132376506777768354791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24454843168675703691139721 18341132376506777768354791)
      ·
        refine ⟨27511698564760166652532187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18341132376506777768354791 27511698564760166652532187)
        ·
          refine ⟨41267547847140249978798281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27511698564760166652532187 41267547847140249978798281)
          ·
            refine ⟨30950660885355187484098711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41267547847140249978798281 30950660885355187484098711)
            ·
              refine ⟨46425991328032781226148067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30950660885355187484098711 46425991328032781226148067)
              ·
                refine ⟨69638986992049171839222101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46425991328032781226148067 69638986992049171839222101)
                ·
                  refine ⟨204020469703269058122721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69638986992049171839222101 204020469703269058122721)
                  ·
                    rfl

theorem cell22_1787978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1787978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1787978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1787978 prefixEnd_1787978 := by exact prefixLift 1787978
  have htrace : WordTrace (prefixWord ++ tailWord_1787978) baseStart_1787978 baseEnd_1787978 := by
    simpa [prefixWord, tailWord_1787978, baseEnd_1787978] using wordTrace_append hprefix tailTrace_1787978
  have hstable : (prefixWord ++ tailWord_1787978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1787978).length < 2 ^ (prefixWord ++ tailWord_1787978).sum := by decide
  have hdescent : baseEnd_1787978 < baseStart_1787978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1787978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788025 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1788025 : Nat := 118140960795 + 1788025 * 2 ^ 59
def prefixEnd_1788025 : Nat := 4983230072969 + 3 ^ 40 * 1788025 * 2
def baseEnd_1788025 : Nat := 612077498170314718443019

theorem tailTrace_1788025 : CollatzResearch.WordTrace tailWord_1788025 prefixEnd_1788025 612077498170314718443019 := by
  unfold tailWord_1788025
  simp only [CollatzResearch.WordTrace]
  refine ⟨65214629347298270203333529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43476419564865513468889019 65214629347298270203333529)
  ·
    refine ⟨48910972010473702652500147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65214629347298270203333529 48910972010473702652500147)
    ·
      refine ⟨73366458015710553978750221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48910972010473702652500147 73366458015710553978750221)
      ·
        refine ⟨27512421755891457742031333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73366458015710553978750221 27512421755891457742031333)
        ·
          refine ⟨5158579079229648326630875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27512421755891457742031333 5158579079229648326630875)
          ·
            refine ⟨7737868618844472489946313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158579079229648326630875 7737868618844472489946313)
            ·
              refine ⟨5803401464133354367459735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7737868618844472489946313 5803401464133354367459735)
              ·
                refine ⟨8705102196200031551189603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803401464133354367459735 8705102196200031551189603)
                ·
                  refine ⟨13057653294300047326784405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8705102196200031551189603 13057653294300047326784405)
                  ·
                    refine ⟨612077498170314718443019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13057653294300047326784405 612077498170314718443019)
                    ·
                      rfl

theorem cell22_1788025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1788025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788025 prefixEnd_1788025 := by exact prefixLift 1788025
  have htrace : WordTrace (prefixWord ++ tailWord_1788025) baseStart_1788025 baseEnd_1788025 := by
    simpa [prefixWord, tailWord_1788025, baseEnd_1788025] using wordTrace_append hprefix tailTrace_1788025
  have hstable : (prefixWord ++ tailWord_1788025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788025).length < 2 ^ (prefixWord ++ tailWord_1788025).sum := by decide
  have hdescent : baseEnd_1788025 < baseStart_1788025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788029 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 4]
def baseStart_1788029 : Nat := 118140960795 + 1788029 * 2 ^ 59
def prefixEnd_1788029 : Nat := 4983230072969 + 3 ^ 40 * 1788029 * 2
def baseEnd_1788029 : Nat := 204026289150686680447669

theorem tailTrace_1788029 : CollatzResearch.WordTrace tailWord_1788029 prefixEnd_1788029 204026289150686680447669 := by
  unfold tailWord_1788029
  simp only [CollatzResearch.WordTrace]
  refine ⟨65214775239283778886479141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43476516826189185924319427 65214775239283778886479141)
  ·
    refine ⟨12227770357365708541214839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65214775239283778886479141 12227770357365708541214839)
    ·
      refine ⟨18341655536048562811822259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12227770357365708541214839 18341655536048562811822259)
      ·
        refine ⟨27512483304072844217733389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18341655536048562811822259 27512483304072844217733389)
        ·
          refine ⟨10317181239027316581650021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27512483304072844217733389 10317181239027316581650021)
          ·
            refine ⟨1934471482317621859059379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10317181239027316581650021 1934471482317621859059379)
            ·
              refine ⟨2901707223476432788589069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934471482317621859059379 2901707223476432788589069)
              ·
                refine ⟨1088140208803662295720901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2901707223476432788589069 1088140208803662295720901)
                ·
                  refine ⟨204026289150686680447669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088140208803662295720901 204026289150686680447669)
                  ·
                    rfl

theorem cell22_1788029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_1788029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788029 prefixEnd_1788029 := by exact prefixLift 1788029
  have htrace : WordTrace (prefixWord ++ tailWord_1788029) baseStart_1788029 baseEnd_1788029 := by
    simpa [prefixWord, tailWord_1788029, baseEnd_1788029] using wordTrace_append hprefix tailTrace_1788029
  have hstable : (prefixWord ++ tailWord_1788029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788029).length < 2 ^ (prefixWord ++ tailWord_1788029).sum := by decide
  have hdescent : baseEnd_1788029 < baseStart_1788029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788040 : List Nat := [2, 1, 3, 4, 1, 1, 10]
def baseStart_1788040 : Nat := 118140960795 + 1788040 * 2 ^ 59
def prefixEnd_1788040 : Nat := 4983230072969 + 3 ^ 40 * 1788040 * 2
def baseEnd_1788040 : Nat := 22669727147291099233999

theorem tailTrace_1788040 : CollatzResearch.WordTrace tailWord_1788040 prefixEnd_1788040 22669727147291099233999 := by
  unfold tailWord_1788040
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607588221121963882564787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43476784294829285176753049 32607588221121963882564787)
  ·
    refine ⟨48911382331682945823847181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32607588221121963882564787 48911382331682945823847181)
    ·
      refine ⟨18341768374381104683942693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48911382331682945823847181 18341768374381104683942693)
      ·
        refine ⟨3439081570196457128239255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18341768374381104683942693 3439081570196457128239255)
        ·
          refine ⟨5158622355294685692358883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439081570196457128239255 5158622355294685692358883)
          ·
            refine ⟨7737933532942028538538325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158622355294685692358883 7737933532942028538538325)
            ·
              refine ⟨22669727147291099233999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7737933532942028538538325 22669727147291099233999)
              ·
                rfl

theorem cell22_1788040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 10].length) (baseStart_1788040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788040 prefixEnd_1788040 := by exact prefixLift 1788040
  have htrace : WordTrace (prefixWord ++ tailWord_1788040) baseStart_1788040 baseEnd_1788040 := by
    simpa [prefixWord, tailWord_1788040, baseEnd_1788040] using wordTrace_append hprefix tailTrace_1788040
  have hstable : (prefixWord ++ tailWord_1788040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788040).length < 2 ^ (prefixWord ++ tailWord_1788040).sum := by decide
  have hdescent : baseEnd_1788040 < baseStart_1788040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788042 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1788042 : Nat := 118140960795 + 1788042 * 2 ^ 59
def prefixEnd_1788042 : Nat := 4983230072969 + 3 ^ 40 * 1788042 * 2
def baseEnd_1788042 : Nat := 612083317617732340767967

theorem tailTrace_1788042 : CollatzResearch.WordTrace tailWord_1788042 prefixEnd_1788042 612083317617732340767967 := by
  unfold tailWord_1788042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303812347059170526675595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43476832925491121404468253 16303812347059170526675595)
  ·
    refine ⟨24455718520588755790013393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16303812347059170526675595 24455718520588755790013393)
    ·
      refine ⟨18341788890441566842510045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24455718520588755790013393 18341788890441566842510045)
      ·
        refine ⟨6878170833915587565941267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18341788890441566842510045 6878170833915587565941267)
        ·
          refine ⟨10317256250873381348911901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878170833915587565941267 10317256250873381348911901)
          ·
            refine ⟨3868971094077518005841963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10317256250873381348911901 3868971094077518005841963)
            ·
              refine ⟨5803456641116277008762945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868971094077518005841963 5803456641116277008762945)
              ·
                refine ⟨4352592480837207756572209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803456641116277008762945 4352592480837207756572209)
                ·
                  refine ⟨3264444360627905817429157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352592480837207756572209 3264444360627905817429157)
                  ·
                    refine ⟨612083317617732340767967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264444360627905817429157 612083317617732340767967)
                    ·
                      rfl

theorem cell22_1788042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1788042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788042 prefixEnd_1788042 := by exact prefixLift 1788042
  have htrace : WordTrace (prefixWord ++ tailWord_1788042) baseStart_1788042 baseEnd_1788042 := by
    simpa [prefixWord, tailWord_1788042, baseEnd_1788042] using wordTrace_append hprefix tailTrace_1788042
  have hstable : (prefixWord ++ tailWord_1788042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788042).length < 2 ^ (prefixWord ++ tailWord_1788042).sum := by decide
  have hdescent : baseEnd_1788042 < baseStart_1788042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788046 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1788046 : Nat := 118140960795 + 1788046 * 2 ^ 59
def prefixEnd_1788046 : Nat := 4983230072969 + 3 ^ 40 * 1788046 * 2
def baseEnd_1788046 : Nat := 204028228966492554555985

theorem tailTrace_1788046 : CollatzResearch.WordTrace tailWord_1788046 prefixEnd_1788046 204028228966492554555985 := by
  unfold tailWord_1788046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151924410027773848730999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43476930186814793859898661 8151924410027773848730999)
  ·
    refine ⟨12227886615041660773096499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8151924410027773848730999 12227886615041660773096499)
    ·
      refine ⟨18341829922562491159644749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12227886615041660773096499 18341829922562491159644749)
      ·
        refine ⟨6878186220960934184866781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18341829922562491159644749 6878186220960934184866781)
        ·
          refine ⟨2579319832860350319325043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6878186220960934184866781 2579319832860350319325043)
          ·
            refine ⟨3868979749290525478987565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579319832860350319325043 3868979749290525478987565)
            ·
              refine ⟨1450867405983947054620337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3868979749290525478987565 1450867405983947054620337)
              ·
                refine ⟨1088150554487960290965253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450867405983947054620337 1088150554487960290965253)
                ·
                  refine ⟨204028228966492554555985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088150554487960290965253 204028228966492554555985)
                  ·
                    rfl

theorem cell22_1788046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1788046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788046 prefixEnd_1788046 := by exact prefixLift 1788046
  have htrace : WordTrace (prefixWord ++ tailWord_1788046) baseStart_1788046 baseEnd_1788046 := by
    simpa [prefixWord, tailWord_1788046, baseEnd_1788046] using wordTrace_append hprefix tailTrace_1788046
  have hstable : (prefixWord ++ tailWord_1788046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788046).length < 2 ^ (prefixWord ++ tailWord_1788046).sum := by decide
  have hdescent : baseEnd_1788046 < baseStart_1788046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788061 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1788061 : Nat := 118140960795 + 1788061 * 2 ^ 59
def prefixEnd_1788061 : Nat := 4983230072969 + 3 ^ 40 * 1788061 * 2
def baseEnd_1788061 : Nat := 612089821706022624542909

theorem tailTrace_1788061 : CollatzResearch.WordTrace tailWord_1788061 prefixEnd_1788061 612089821706022624542909 := by
  unfold tailWord_1788061
  simp only [CollatzResearch.WordTrace]
  refine ⟨65215942375167848351644037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43477294916778565567762691 65215942375167848351644037)
  ·
    refine ⟨12227989195343971565933257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65215942375167848351644037 12227989195343971565933257)
    ·
      refine ⟨9170991896507978674449943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12227989195343971565933257 9170991896507978674449943)
      ·
        refine ⟨13756487844761968011674915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170991896507978674449943 13756487844761968011674915)
        ·
          refine ⟨20634731767142952017512373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13756487844761968011674915 20634731767142952017512373)
          ·
            refine ⟨1934506103169651751641785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20634731767142952017512373 1934506103169651751641785)
            ·
              refine ⟨1450879577377238813731339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934506103169651751641785 1450879577377238813731339)
              ·
                refine ⟨2176319366065858220597009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450879577377238813731339 2176319366065858220597009)
                ·
                  refine ⟨1632239524549393665447757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176319366065858220597009 1632239524549393665447757)
                  ·
                    refine ⟨612089821706022624542909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632239524549393665447757 612089821706022624542909)
                    ·
                      rfl

theorem cell22_1788061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1788061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788061 prefixEnd_1788061 := by exact prefixLift 1788061
  have htrace : WordTrace (prefixWord ++ tailWord_1788061) baseStart_1788061 baseEnd_1788061 := by
    simpa [prefixWord, tailWord_1788061, baseEnd_1788061] using wordTrace_append hprefix tailTrace_1788061
  have hstable : (prefixWord ++ tailWord_1788061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788061).length < 2 ^ (prefixWord ++ tailWord_1788061).sum := by decide
  have hdescent : baseEnd_1788061 < baseStart_1788061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788089 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 1, 3]
def baseStart_1788089 : Nat := 118140960795 + 1788089 * 2 ^ 59
def prefixEnd_1788089 : Nat := 4983230072969 + 3 ^ 40 * 1788089 * 2
def baseEnd_1788089 : Nat := 612099406678239884842823

theorem tailTrace_1788089 : CollatzResearch.WordTrace tailWord_1788089 prefixEnd_1788089 612099406678239884842823 := by
  unfold tailWord_1788089
  simp only [CollatzResearch.WordTrace]
  refine ⟨65216963619066409133663321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43477975746044272755775547 65216963619066409133663321)
  ·
    refine ⟨48912722714299806850247491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65216963619066409133663321 48912722714299806850247491)
    ·
      refine ⟨73369084071449710275371237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48912722714299806850247491 73369084071449710275371237)
      ·
        refine ⟨13756703263396820676632107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73369084071449710275371237 13756703263396820676632107)
        ·
          refine ⟨20635054895095231014948161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13756703263396820676632107 20635054895095231014948161)
          ·
            refine ⟨15476291171321423261211121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20635054895095231014948161 15476291171321423261211121)
            ·
              refine ⟨11607218378491067445908341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15476291171321423261211121 11607218378491067445908341)
              ·
                refine ⟨1088176722983537573053907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11607218378491067445908341 1088176722983537573053907)
                ·
                  refine ⟨1632265084475306359580861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088176722983537573053907 1632265084475306359580861)
                  ·
                    refine ⟨612099406678239884842823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632265084475306359580861 612099406678239884842823)
                    ·
                      rfl

theorem cell22_1788089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_1788089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788089 prefixEnd_1788089 := by exact prefixLift 1788089
  have htrace : WordTrace (prefixWord ++ tailWord_1788089) baseStart_1788089 baseEnd_1788089 := by
    simpa [prefixWord, tailWord_1788089, baseEnd_1788089] using wordTrace_append hprefix tailTrace_1788089
  have hstable : (prefixWord ++ tailWord_1788089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788089).length < 2 ^ (prefixWord ++ tailWord_1788089).sum := by decide
  have hdescent : baseEnd_1788089 < baseStart_1788089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788132 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1788132 : Nat := 118140960795 + 1788132 * 2 ^ 59
def prefixEnd_1788132 : Nat := 4983230072969 + 3 ^ 40 * 1788132 * 2
def baseEnd_1788132 : Nat := 612114126457002106017691

theorem tailTrace_1788132 : CollatzResearch.WordTrace tailWord_1788132 prefixEnd_1788132 612114126457002106017691 := by
  unfold tailWord_1788132
  simp only [CollatzResearch.WordTrace]
  refine ⟨32609265978955313738739325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43479021305273751651652433 32609265978955313738739325)
  ·
    refine ⟨12228474742108242652027247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32609265978955313738739325 12228474742108242652027247)
    ·
      refine ⟨18342712113162363978040871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228474742108242652027247 18342712113162363978040871)
      ·
        refine ⟨27514068169743545967061307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18342712113162363978040871 27514068169743545967061307)
        ·
          refine ⟨41271102254615318950591961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27514068169743545967061307 41271102254615318950591961)
          ·
            refine ⟨30953326690961489212943971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41271102254615318950591961 30953326690961489212943971)
            ·
              refine ⟨46429990036442233819415957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30953326690961489212943971 46429990036442233819415957)
              ·
                refine ⟨2176405782958229710285123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46429990036442233819415957 2176405782958229710285123)
                ·
                  refine ⟨3264608674437344565427685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176405782958229710285123 3264608674437344565427685)
                  ·
                    refine ⟨612114126457002106017691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264608674437344565427685 612114126457002106017691)
                    ·
                      rfl

theorem cell22_1788132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1788132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788132 prefixEnd_1788132 := by exact prefixLift 1788132
  have htrace : WordTrace (prefixWord ++ tailWord_1788132) baseStart_1788132 baseEnd_1788132 := by
    simpa [prefixWord, tailWord_1788132, baseEnd_1788132] using wordTrace_append hprefix tailTrace_1788132
  have hstable : (prefixWord ++ tailWord_1788132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788132).length < 2 ^ (prefixWord ++ tailWord_1788132).sum := by decide
  have hdescent : baseEnd_1788132 < baseStart_1788132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788164 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1788164 : Nat := 118140960795 + 1788164 * 2 ^ 59
def prefixEnd_1788164 : Nat := 4983230072969 + 3 ^ 40 * 1788164 * 2
def baseEnd_1788164 : Nat := 204041693570321563072531

theorem tailTrace_1788164 : CollatzResearch.WordTrace tailWord_1788164 prefixEnd_1788164 204041693570321563072531 := by
  unfold tailWord_1788164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32609849546897348471321773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43479799395863131295095697 32609849546897348471321773)
  ·
    refine ⟨12228693580086505676745665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32609849546897348471321773 12228693580086505676745665)
    ·
      refine ⟨9171520185064879257559249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12228693580086505676745665 9171520185064879257559249)
      ·
        refine ⟨6878640138798659443169437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9171520185064879257559249 6878640138798659443169437)
        ·
          refine ⟨2579490052049497291188539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6878640138798659443169437 2579490052049497291188539)
          ·
            refine ⟨3869235078074245936782809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579490052049497291188539 3869235078074245936782809)
            ·
              refine ⟨2901926308555684452587107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869235078074245936782809 2901926308555684452587107)
              ·
                refine ⟨4352889462833526678880661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901926308555684452587107 4352889462833526678880661)
                ·
                  refine ⟨204041693570321563072531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4352889462833526678880661 204041693570321563072531)
                  ·
                    rfl

theorem cell22_1788164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1788164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788164 prefixEnd_1788164 := by exact prefixLift 1788164
  have htrace : WordTrace (prefixWord ++ tailWord_1788164) baseStart_1788164 baseEnd_1788164 := by
    simpa [prefixWord, tailWord_1788164, baseEnd_1788164] using wordTrace_append hprefix tailTrace_1788164
  have hstable : (prefixWord ++ tailWord_1788164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788164).length < 2 ^ (prefixWord ++ tailWord_1788164).sum := by decide
  have hdescent : baseEnd_1788164 < baseStart_1788164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788192 : List Nat := [2, 1, 1, 5, 2, 2, 1, 8]
def baseStart_1788192 : Nat := 118140960795 + 1788192 * 2 ^ 59
def prefixEnd_1788192 : Nat := 4983230072969 + 3 ^ 40 * 1788192 * 2
def baseEnd_1788192 : Nat := 68014962853686883279723

theorem tailTrace_1788192 : CollatzResearch.WordTrace tailWord_1788192 prefixEnd_1788192 68014962853686883279723 := by
  unfold tailWord_1788192
  simp only [CollatzResearch.WordTrace]
  refine ⟨32610360168846628862331415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43480480225128838483108553 32610360168846628862331415)
  ·
    refine ⟨48915540253269943293497123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32610360168846628862331415 48915540253269943293497123)
    ·
      refine ⟨73373310379904914940245685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48915540253269943293497123 73373310379904914940245685)
      ·
        refine ⟨6878747848116085775648033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73373310379904914940245685 6878747848116085775648033)
        ·
          refine ⟨5159060886087064331736025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6878747848116085775648033 5159060886087064331736025)
          ·
            refine ⟨3869295664565298248802019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5159060886087064331736025 3869295664565298248802019)
            ·
              refine ⟨5803943496847947373203029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869295664565298248802019 5803943496847947373203029)
              ·
                refine ⟨68014962853686883279723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5803943496847947373203029 68014962853686883279723)
                ·
                  rfl

theorem cell22_1788192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_1788192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788192 prefixEnd_1788192 := by exact prefixLift 1788192
  have htrace : WordTrace (prefixWord ++ tailWord_1788192) baseStart_1788192 baseEnd_1788192 := by
    simpa [prefixWord, tailWord_1788192, baseEnd_1788192] using wordTrace_append hprefix tailTrace_1788192
  have hstable : (prefixWord ++ tailWord_1788192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788192).length < 2 ^ (prefixWord ++ tailWord_1788192).sum := by decide
  have hdescent : baseEnd_1788192 < baseStart_1788192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788207 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 5, 3]
def baseStart_1788207 : Nat := 118140960795 + 1788207 * 2 ^ 59
def prefixEnd_1788207 : Nat := 4983230072969 + 3 ^ 40 * 1788207 * 2
def baseEnd_1788207 : Nat := 612139800489726910392461

theorem tailTrace_1788207 : CollatzResearch.WordTrace tailWord_1788207 prefixEnd_1788207 612139800489726910392461 := by
  unfold tailWord_1788207
  simp only [CollatzResearch.WordTrace]
  refine ⟨65221267432638915286458875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43480844955092610190972583 65221267432638915286458875)
  ·
    refine ⟨97831901148958372929688313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65221267432638915286458875 97831901148958372929688313)
    ·
      refine ⟨73373925861718779697266235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97831901148958372929688313 73373925861718779697266235)
      ·
        refine ⟨110060888792578169545899353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73373925861718779697266235 110060888792578169545899353)
        ·
          refine ⟨82545666594433627159424515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110060888792578169545899353 82545666594433627159424515)
          ·
            refine ⟨123818499891650440739136773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82545666594433627159424515 123818499891650440739136773)
            ·
              refine ⟨23215968729684457638588145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123818499891650440739136773 23215968729684457638588145)
              ·
                refine ⟨17411976547263343228941109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23215968729684457638588145 17411976547263343228941109)
                ·
                  refine ⟨1632372801305938427713229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17411976547263343228941109 1632372801305938427713229)
                  ·
                    refine ⟨612139800489726910392461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632372801305938427713229 612139800489726910392461)
                    ·
                      rfl

theorem cell22_1788207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_1788207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788207 prefixEnd_1788207 := by exact prefixLift 1788207
  have htrace : WordTrace (prefixWord ++ tailWord_1788207) baseStart_1788207 baseEnd_1788207 := by
    simpa [prefixWord, tailWord_1788207, baseEnd_1788207] using wordTrace_append hprefix tailTrace_1788207
  have hstable : (prefixWord ++ tailWord_1788207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788207).length < 2 ^ (prefixWord ++ tailWord_1788207).sum := by decide
  have hdescent : baseEnd_1788207 < baseStart_1788207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788209 : List Nat := [1, 2, 2, 3, 5, 1, 8]
def baseStart_1788209 : Nat := 118140960795 + 1788209 * 2 ^ 59
def prefixEnd_1788209 : Nat := 4983230072969 + 3 ^ 40 * 1788209 * 2
def baseEnd_1788209 : Nat := 22671869819651835994165

theorem tailTrace_1788209 : CollatzResearch.WordTrace tailWord_1788209 prefixEnd_1788209 22671869819651835994165 := by
  unfold tailWord_1788209
  simp only [CollatzResearch.WordTrace]
  refine ⟨65221340378631669628031681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43480893585754446418687787 65221340378631669628031681)
  ·
    refine ⟨48916005283973752221023761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65221340378631669628031681 48916005283973752221023761)
    ·
      refine ⟨36687003962980314165767821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48916005283973752221023761 36687003962980314165767821)
      ·
        refine ⟨13757626486117617812162933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36687003962980314165767821 13757626486117617812162933)
        ·
          refine ⟨1289777483073526669890275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13757626486117617812162933 1289777483073526669890275)
          ·
            refine ⟨1934666224610290004835413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289777483073526669890275 1934666224610290004835413)
            ·
              refine ⟨22671869819651835994165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1934666224610290004835413 22671869819651835994165)
              ·
                rfl

theorem cell22_1788209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 8].length) (baseStart_1788209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788209 prefixEnd_1788209 := by exact prefixLift 1788209
  have htrace : WordTrace (prefixWord ++ tailWord_1788209) baseStart_1788209 baseEnd_1788209 := by
    simpa [prefixWord, tailWord_1788209, baseEnd_1788209] using wordTrace_append hprefix tailTrace_1788209
  have hstable : (prefixWord ++ tailWord_1788209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788209).length < 2 ^ (prefixWord ++ tailWord_1788209).sum := by decide
  have hdescent : baseEnd_1788209 < baseStart_1788209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788314 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1788314 : Nat := 118140960795 + 1788314 * 2 ^ 59
def prefixEnd_1788314 : Nat := 4983230072969 + 3 ^ 40 * 1788314 * 2
def baseEnd_1788314 : Nat := 612176428776414297967133

theorem tailTrace_1788314 : CollatzResearch.WordTrace tailWord_1788314 prefixEnd_1788314 612176428776414297967133 := by
  unfold tailWord_1788314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16306292510812818140150999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43483446695500848373735997 16306292510812818140150999)
  ·
    refine ⟨24459438766219227210226499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16306292510812818140150999 24459438766219227210226499)
    ·
      refine ⟨36689158149328840815339749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24459438766219227210226499 36689158149328840815339749)
      ·
        refine ⟨6879217152999157652876203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36689158149328840815339749 6879217152999157652876203)
        ·
          refine ⟨10318825729498736479314305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879217152999157652876203 10318825729498736479314305)
          ·
            refine ⟨7739119297124052359485729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10318825729498736479314305 7739119297124052359485729)
            ·
              refine ⟨5804339472843039269614297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7739119297124052359485729 5804339472843039269614297)
              ·
                refine ⟨4353254604632279452210723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5804339472843039269614297 4353254604632279452210723)
                ·
                  refine ⟨6529881906948419178316085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353254604632279452210723 6529881906948419178316085)
                  ·
                    refine ⟨612176428776414297967133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6529881906948419178316085 612176428776414297967133)
                    ·
                      rfl

theorem cell22_1788314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1788314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788314 prefixEnd_1788314 := by exact prefixLift 1788314
  have htrace : WordTrace (prefixWord ++ tailWord_1788314) baseStart_1788314 baseEnd_1788314 := by
    simpa [prefixWord, tailWord_1788314, baseEnd_1788314] using wordTrace_append hprefix tailTrace_1788314
  have hstable : (prefixWord ++ tailWord_1788314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788314).length < 2 ^ (prefixWord ++ tailWord_1788314).sum := by decide
  have hdescent : baseEnd_1788314 < baseStart_1788314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788318 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1788318 : Nat := 118140960795 + 1788318 * 2 ^ 59
def prefixEnd_1788318 : Nat := 4983230072969 + 3 ^ 40 * 1788318 * 2
def baseEnd_1788318 : Nat := 612177798058159620867121

theorem tailTrace_1788318 : CollatzResearch.WordTrace tailWord_1788318 prefixEnd_1788318 612177798058159620867121 := by
  unfold tailWord_1788318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153164491904597655468701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43483543956824520829166405 8153164491904597655468701)
  ·
    refine ⟨3057436684464224120800763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8153164491904597655468701 3057436684464224120800763)
    ·
      refine ⟨4586155026696336181201145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057436684464224120800763 4586155026696336181201145)
      ·
        refine ⟨3439616270022252135900859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4586155026696336181201145 3439616270022252135900859)
        ·
          refine ⟨5159424405033378203851289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439616270022252135900859 5159424405033378203851289)
          ·
            refine ⟨3869568303775033652888467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5159424405033378203851289 3869568303775033652888467)
            ·
              refine ⟨5804352455662550479332701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869568303775033652888467 5804352455662550479332701)
              ·
                refine ⟨2176632170873456429749763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5804352455662550479332701 2176632170873456429749763)
                ·
                  refine ⟨3264948256310184644624645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176632170873456429749763 3264948256310184644624645)
                  ·
                    refine ⟨612177798058159620867121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264948256310184644624645 612177798058159620867121)
                    ·
                      rfl

theorem cell22_1788318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1788318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788318 prefixEnd_1788318 := by exact prefixLift 1788318
  have htrace : WordTrace (prefixWord ++ tailWord_1788318) baseStart_1788318 baseEnd_1788318 := by
    simpa [prefixWord, tailWord_1788318, baseEnd_1788318] using wordTrace_append hprefix tailTrace_1788318
  have hstable : (prefixWord ++ tailWord_1788318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788318).length < 2 ^ (prefixWord ++ tailWord_1788318).sum := by decide
  have hdescent : baseEnd_1788318 < baseStart_1788318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788406 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1788406 : Nat := 118140960795 + 1788406 * 2 ^ 59
def prefixEnd_1788406 : Nat := 4983230072969 + 3 ^ 40 * 1788406 * 2
def baseEnd_1788406 : Nat := 204069307418852241555617

theorem tailTrace_1788406 : CollatzResearch.WordTrace tailWord_1788406 prefixEnd_1788406 204069307418852241555617 := by
  unfold tailWord_1788406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076782847432373267059567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43485683705945314848635381 4076782847432373267059567)
  ·
    refine ⟨6115174271148559900589351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4076782847432373267059567 6115174271148559900589351)
    ·
      refine ⟨9172761406722839850884027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6115174271148559900589351 9172761406722839850884027)
      ·
        refine ⟨13759142110084259776326041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172761406722839850884027 13759142110084259776326041)
        ·
          refine ⟨10319356582563194832244531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13759142110084259776326041 10319356582563194832244531)
          ·
            refine ⟨15479034873844792248366797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319356582563194832244531 15479034873844792248366797)
            ·
              refine ⟨5804638077691797093137549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15479034873844792248366797 5804638077691797093137549)
              ·
                refine ⟨2176739279134423909926581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5804638077691797093137549 2176739279134423909926581)
                ·
                  refine ⟨204069307418852241555617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176739279134423909926581 204069307418852241555617)
                  ·
                    rfl

theorem cell22_1788406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1788406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788406 prefixEnd_1788406 := by exact prefixLift 1788406
  have htrace : WordTrace (prefixWord ++ tailWord_1788406) baseStart_1788406 baseEnd_1788406 := by
    simpa [prefixWord, tailWord_1788406, baseEnd_1788406] using wordTrace_append hprefix tailTrace_1788406
  have hstable : (prefixWord ++ tailWord_1788406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788406).length < 2 ^ (prefixWord ++ tailWord_1788406).sum := by decide
  have hdescent : baseEnd_1788406 < baseStart_1788406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788419 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_1788419 : Nat := 118140960795 + 1788419 * 2 ^ 59
def prefixEnd_1788419 : Nat := 4983230072969 + 3 ^ 40 * 1788419 * 2
def baseEnd_1788419 : Nat := 612212372422229024091811

theorem tailTrace_1788419 : CollatzResearch.WordTrace tailWord_1788419 prefixEnd_1788419 612212372422229024091811 := by
  unfold tailWord_1788419
  simp only [CollatzResearch.WordTrace]
  refine ⟨65228999707870875493176311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43485999805247250328784207 65228999707870875493176311)
  ·
    refine ⟨97843499561806313239764467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65228999707870875493176311 97843499561806313239764467)
    ·
      refine ⟨146765249342709469859646701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97843499561806313239764467 146765249342709469859646701)
      ·
        refine ⟨55036968503516051197367513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146765249342709469859646701 55036968503516051197367513)
        ·
          refine ⟨41277726377637038398025635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55036968503516051197367513 41277726377637038398025635)
          ·
            refine ⟨61916589566455557597038453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41277726377637038398025635 61916589566455557597038453)
            ·
              refine ⟨5804680271855208524722355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61916589566455557597038453 5804680271855208524722355)
              ·
                refine ⟨8707020407782812787083533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804680271855208524722355 8707020407782812787083533)
                ·
                  refine ⟨3265132652918554795156325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8707020407782812787083533 3265132652918554795156325)
                  ·
                    refine ⟨612212372422229024091811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265132652918554795156325 612212372422229024091811)
                    ·
                      rfl

theorem cell22_1788419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_1788419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788419 prefixEnd_1788419 := by exact prefixLift 1788419
  have htrace : WordTrace (prefixWord ++ tailWord_1788419) baseStart_1788419 baseEnd_1788419 := by
    simpa [prefixWord, tailWord_1788419, baseEnd_1788419] using wordTrace_append hprefix tailTrace_1788419
  have hstable : (prefixWord ++ tailWord_1788419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788419).length < 2 ^ (prefixWord ++ tailWord_1788419).sum := by decide
  have hdescent : baseEnd_1788419 < baseStart_1788419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788449 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1788449 : Nat := 118140960795 + 1788449 * 2 ^ 59
def prefixEnd_1788449 : Nat := 4983230072969 + 3 ^ 40 * 1788449 * 2
def baseEnd_1788449 : Nat := 612222642035318945841719

theorem tailTrace_1788449 : CollatzResearch.WordTrace tailWord_1788449 prefixEnd_1788449 612222642035318945841719 := by
  unfold tailWord_1788449
  simp only [CollatzResearch.WordTrace]
  refine ⟨65230093897762190616768401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43486729265174793744512267 65230093897762190616768401)
  ·
    refine ⟨48922570423321642962576301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65230093897762190616768401 48922570423321642962576301)
    ·
      refine ⟨18345963908745616110966113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48922570423321642962576301 18345963908745616110966113)
      ·
        refine ⟨13759472931559212083224585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18345963908745616110966113 13759472931559212083224585)
        ·
          refine ⟨10319604698669409062418439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13759472931559212083224585 10319604698669409062418439)
          ·
            refine ⟨15479407048004113593627659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319604698669409062418439 15479407048004113593627659)
            ·
              refine ⟨23219110572006170390441489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15479407048004113593627659 23219110572006170390441489)
              ·
                refine ⟨17414332929004627792831117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23219110572006170390441489 17414332929004627792831117)
                ·
                  refine ⟨6530374848376735422311669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17414332929004627792831117 6530374848376735422311669)
                  ·
                    refine ⟨612222642035318945841719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6530374848376735422311669 612222642035318945841719)
                    ·
                      rfl

theorem cell22_1788449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1788449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788449 prefixEnd_1788449 := by exact prefixLift 1788449
  have htrace : WordTrace (prefixWord ++ tailWord_1788449) baseStart_1788449 baseEnd_1788449 := by
    simpa [prefixWord, tailWord_1788449, baseEnd_1788449] using wordTrace_append hprefix tailTrace_1788449
  have hstable : (prefixWord ++ tailWord_1788449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788449).length < 2 ^ (prefixWord ++ tailWord_1788449).sum := by decide
  have hdescent : baseEnd_1788449 < baseStart_1788449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788464 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_1788464 : Nat := 118140960795 + 1788464 * 2 ^ 59
def prefixEnd_1788464 : Nat := 4983230072969 + 3 ^ 40 * 1788464 * 2
def baseEnd_1788464 : Nat := 612227776841863906716673

theorem tailTrace_1788464 : CollatzResearch.WordTrace tailWord_1788464 prefixEnd_1788464 612227776841863906716673 := by
  unfold tailWord_1788464
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615320496353924089282223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43487093995138565452376297 32615320496353924089282223)
  ·
    refine ⟨48922980744530886133923335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32615320496353924089282223 48922980744530886133923335)
    ·
      refine ⟨73384471116796329200885003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48922980744530886133923335 73384471116796329200885003)
      ·
        refine ⟨110076706675194493801327505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73384471116796329200885003 110076706675194493801327505)
        ·
          refine ⟨82557530006395870350995629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110076706675194493801327505 82557530006395870350995629)
          ·
            refine ⟨30959073752398451381623361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82557530006395870350995629 30959073752398451381623361)
            ·
              refine ⟨23219305314298838536217521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30959073752398451381623361 23219305314298838536217521)
              ·
                refine ⟨17414478985724128902163141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23219305314298838536217521 17414478985724128902163141)
                ·
                  refine ⟨3265214809823274169155589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17414478985724128902163141 3265214809823274169155589)
                  ·
                    refine ⟨612227776841863906716673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265214809823274169155589 612227776841863906716673)
                    ·
                      rfl

theorem cell22_1788464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_1788464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788464 prefixEnd_1788464 := by exact prefixLift 1788464
  have htrace : WordTrace (prefixWord ++ tailWord_1788464) baseStart_1788464 baseEnd_1788464 := by
    simpa [prefixWord, tailWord_1788464, baseEnd_1788464] using wordTrace_append hprefix tailTrace_1788464
  have hstable : (prefixWord ++ tailWord_1788464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788464).length < 2 ^ (prefixWord ++ tailWord_1788464).sum := by decide
  have hdescent : baseEnd_1788464 < baseStart_1788464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788481 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1788481 : Nat := 118140960795 + 1788481 * 2 ^ 59
def prefixEnd_1788481 : Nat := 4983230072969 + 3 ^ 40 * 1788481 * 2
def baseEnd_1788481 : Nat := 612233596289281529041621

theorem tailTrace_1788481 : CollatzResearch.WordTrace tailWord_1788481 prefixEnd_1788481 612233596289281529041621 := by
  unfold tailWord_1788481
  simp only [CollatzResearch.WordTrace]
  refine ⟨65231261033646260081933297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43487507355764173387955531 65231261033646260081933297)
  ·
    refine ⟨48923445775234695061449973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65231261033646260081933297 48923445775234695061449973)
    ·
      refine ⟨4586573041428252662010935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48923445775234695061449973 4586573041428252662010935)
      ·
        refine ⟨6879859562142378993016403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586573041428252662010935 6879859562142378993016403)
        ·
          refine ⟨10319789343213568489524605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879859562142378993016403 10319789343213568489524605)
          ·
            refine ⟨3869921003705088183571727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10319789343213568489524605 3869921003705088183571727)
            ·
              refine ⟨5804881505557632275357591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869921003705088183571727 5804881505557632275357591)
              ·
                refine ⟨8707322258336448413036387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804881505557632275357591 8707322258336448413036387)
                ·
                  refine ⟨13060983387504672619554581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707322258336448413036387 13060983387504672619554581)
                  ·
                    refine ⟨612233596289281529041621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13060983387504672619554581 612233596289281529041621)
                    ·
                      rfl

theorem cell22_1788481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1788481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788481 prefixEnd_1788481 := by exact prefixLift 1788481
  have htrace : WordTrace (prefixWord ++ tailWord_1788481) baseStart_1788481 baseEnd_1788481 := by
    simpa [prefixWord, tailWord_1788481, baseEnd_1788481] using wordTrace_append hprefix tailTrace_1788481
  have hstable : (prefixWord ++ tailWord_1788481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788481).length < 2 ^ (prefixWord ++ tailWord_1788481).sum := by decide
  have hdescent : baseEnd_1788481 < baseStart_1788481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788500 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1788500 : Nat := 118140960795 + 1788500 * 2 ^ 59
def prefixEnd_1788500 : Nat := 4983230072969 + 3 ^ 40 * 1788500 * 2
def baseEnd_1788500 : Nat := 612240100377571812816563

theorem tailTrace_1788500 : CollatzResearch.WordTrace tailWord_1788500 prefixEnd_1788500 612240100377571812816563 := by
  unfold tailWord_1788500
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615977010288713163437477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43487969347051617551249969 32615977010288713163437477)
  ·
    refine ⟨6115495689429133718144527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32615977010288713163437477 6115495689429133718144527)
    ·
      refine ⟨9173243534143700577216791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6115495689429133718144527 9173243534143700577216791)
      ·
        refine ⟨13759865301215550865825187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9173243534143700577216791 13759865301215550865825187)
        ·
          refine ⟨20639797951823326298737781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13759865301215550865825187 20639797951823326298737781)
          ·
            refine ⟨1934981057983436840506667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20639797951823326298737781 1934981057983436840506667)
            ·
              refine ⟨2902471586975155260760001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934981057983436840506667 2902471586975155260760001)
              ·
                refine ⟨2176853690231366445570001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902471586975155260760001 2176853690231366445570001)
                ·
                  refine ⟨1632640267673524834177501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176853690231366445570001 1632640267673524834177501)
                  ·
                    refine ⟨612240100377571812816563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632640267673524834177501 612240100377571812816563)
                    ·
                      rfl

theorem cell22_1788500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1788500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788500 prefixEnd_1788500 := by exact prefixLift 1788500
  have htrace : WordTrace (prefixWord ++ tailWord_1788500) baseStart_1788500 baseEnd_1788500 := by
    simpa [prefixWord, tailWord_1788500, baseEnd_1788500] using wordTrace_append hprefix tailTrace_1788500
  have hstable : (prefixWord ++ tailWord_1788500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788500).length < 2 ^ (prefixWord ++ tailWord_1788500).sum := by decide
  have hdescent : baseEnd_1788500 < baseStart_1788500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788530 : List Nat := [3, 2, 1, 2, 5, 1, 2, 6]
def baseStart_1788530 : Nat := 118140960795 + 1788530 * 2 ^ 59
def prefixEnd_1788530 : Nat := 4983230072969 + 3 ^ 40 * 1788530 * 2
def baseEnd_1788530 : Nat := 68027818887851303840719

theorem tailTrace_1788530 : CollatzResearch.WordTrace tailWord_1788530 prefixEnd_1788530 68027818887851303840719 := by
  unfold tailWord_1788530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308262052617185362616761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43488698806979160966978029 16308262052617185362616761)
  ·
    refine ⟨12231196539462889021962571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16308262052617185362616761 12231196539462889021962571)
    ·
      refine ⟨18346794809194333532943857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231196539462889021962571 18346794809194333532943857)
      ·
        refine ⟨13760096106895750149707893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18346794809194333532943857 13760096106895750149707893)
        ·
          refine ⟨1290009010021476576535115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13760096106895750149707893 1290009010021476576535115)
          ·
            refine ⟨1935013515032214864802673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290009010021476576535115 1935013515032214864802673)
            ·
              refine ⟨1451260136274161148602005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935013515032214864802673 1451260136274161148602005)
              ·
                refine ⟨68027818887851303840719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1451260136274161148602005 68027818887851303840719)
                ·
                  rfl

theorem cell22_1788530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_1788530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788530 prefixEnd_1788530 := by exact prefixLift 1788530
  have htrace : WordTrace (prefixWord ++ tailWord_1788530) baseStart_1788530 baseEnd_1788530 := by
    simpa [prefixWord, tailWord_1788530, baseEnd_1788530] using wordTrace_append hprefix tailTrace_1788530
  have hstable : (prefixWord ++ tailWord_1788530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788530).length < 2 ^ (prefixWord ++ tailWord_1788530).sum := by decide
  have hdescent : baseEnd_1788530 < baseStart_1788530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788539 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_1788539 : Nat := 118140960795 + 1788539 * 2 ^ 59
def prefixEnd_1788539 : Nat := 4983230072969 + 3 ^ 40 * 1788539 * 2
def baseEnd_1788539 : Nat := 612253450874588711091443

theorem tailTrace_1788539 : CollatzResearch.WordTrace tailWord_1788539 prefixEnd_1788539 612253450874588711091443 := by
  unfold tailWord_1788539
  simp only [CollatzResearch.WordTrace]
  refine ⟨65233376467436135987544671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43488917644957423991696447 65233376467436135987544671)
  ·
    refine ⟨97850064701154203981317007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65233376467436135987544671 97850064701154203981317007)
    ·
      refine ⟨146775097051731305971975511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97850064701154203981317007 146775097051731305971975511)
      ·
        refine ⟨220162645577596958957963267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146775097051731305971975511 220162645577596958957963267)
        ·
          refine ⟨330243968366395438436944901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220162645577596958957963267 330243968366395438436944901)
          ·
            refine ⟨61920744068699144706927169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330243968366395438436944901 61920744068699144706927169)
            ·
              refine ⟨46440558051524358530195377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61920744068699144706927169 46440558051524358530195377)
              ·
                refine ⟨34830418538643268897646533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46440558051524358530195377 34830418538643268897646533)
                ·
                  refine ⟨6530703475995612918308725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34830418538643268897646533 6530703475995612918308725)
                  ·
                    refine ⟨612253450874588711091443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6530703475995612918308725 612253450874588711091443)
                    ·
                      rfl

theorem cell22_1788539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_1788539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788539 prefixEnd_1788539 := by exact prefixLift 1788539
  have htrace : WordTrace (prefixWord ++ tailWord_1788539) baseStart_1788539 baseEnd_1788539 := by
    simpa [prefixWord, tailWord_1788539, baseEnd_1788539] using wordTrace_append hprefix tailTrace_1788539
  have hstable : (prefixWord ++ tailWord_1788539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788539).length < 2 ^ (prefixWord ++ tailWord_1788539).sum := by decide
  have hdescent : baseEnd_1788539 < baseStart_1788539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788605 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_1788605 : Nat := 118140960795 + 1788605 * 2 ^ 59
def prefixEnd_1788605 : Nat := 4983230072969 + 3 ^ 40 * 1788605 * 2
def baseEnd_1788605 : Nat := 612276044023386538941241

theorem tailTrace_1788605 : CollatzResearch.WordTrace tailWord_1788605 prefixEnd_1788605 612276044023386538941241 := by
  unfold tailWord_1788605
  simp only [CollatzResearch.WordTrace]
  refine ⟨65235783685197029259447269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43490522456798019506298179 65235783685197029259447269)
  ·
    refine ⟨12231709440974442986146363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65235783685197029259447269 12231709440974442986146363)
    ·
      refine ⟨18347564161461664479219545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231709440974442986146363 18347564161461664479219545)
      ·
        refine ⟨13760673121096248359414659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18347564161461664479219545 13760673121096248359414659)
        ·
          refine ⟨20641009681644372539121989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760673121096248359414659 20641009681644372539121989)
          ·
            refine ⟨3870189315308319851085373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20641009681644372539121989 3870189315308319851085373)
            ·
              refine ⟨1451320993240619944157015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3870189315308319851085373 1451320993240619944157015)
              ·
                refine ⟨2176981489860929916235523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451320993240619944157015 2176981489860929916235523)
                ·
                  refine ⟨3265472234791394874353285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176981489860929916235523 3265472234791394874353285)
                  ·
                    refine ⟨612276044023386538941241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265472234791394874353285 612276044023386538941241)
                    ·
                      rfl

theorem cell22_1788605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_1788605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788605 prefixEnd_1788605 := by exact prefixLift 1788605
  have htrace : WordTrace (prefixWord ++ tailWord_1788605) baseStart_1788605 baseEnd_1788605 := by
    simpa [prefixWord, tailWord_1788605, baseEnd_1788605] using wordTrace_append hprefix tailTrace_1788605
  have hstable : (prefixWord ++ tailWord_1788605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788605).length < 2 ^ (prefixWord ++ tailWord_1788605).sum := by decide
  have hdescent : baseEnd_1788605 < baseStart_1788605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788620 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_1788620 : Nat := 118140960795 + 1788620 * 2 ^ 59
def prefixEnd_1788620 : Nat := 4983230072969 + 3 ^ 40 * 1788620 * 2
def baseEnd_1788620 : Nat := 204093726276643833272065

theorem tailTrace_1788620 : CollatzResearch.WordTrace tailWord_1788620 prefixEnd_1788620 204093726276643833272065 := by
  unfold tailWord_1788620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618165390071343410621657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43490887186761791214162209 32618165390071343410621657)
  ·
    refine ⟨24463624042553507557966243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32618165390071343410621657 24463624042553507557966243)
    ·
      refine ⟨36695436063830261336949365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24463624042553507557966243 36695436063830261336949365)
      ·
        refine ⟨3440197130984087000339003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36695436063830261336949365 3440197130984087000339003)
        ·
          refine ⟨5160295696476130500508505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440197130984087000339003 5160295696476130500508505)
          ·
            refine ⟨3870221772357097875381379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160295696476130500508505 3870221772357097875381379)
            ·
              refine ⟨5805332658535646813072069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870221772357097875381379 5805332658535646813072069)
              ·
                refine ⟨1088499873475433777451013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5805332658535646813072069 1088499873475433777451013)
                ·
                  refine ⟨204093726276643833272065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088499873475433777451013 204093726276643833272065)
                  ·
                    rfl

theorem cell22_1788620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_1788620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788620 prefixEnd_1788620 := by exact prefixLift 1788620
  have htrace : WordTrace (prefixWord ++ tailWord_1788620) baseStart_1788620 baseEnd_1788620 := by
    simpa [prefixWord, tailWord_1788620, baseEnd_1788620] using wordTrace_append hprefix tailTrace_1788620
  have hstable : (prefixWord ++ tailWord_1788620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788620).length < 2 ^ (prefixWord ++ tailWord_1788620).sum := by decide
  have hdescent : baseEnd_1788620 < baseStart_1788620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788631 : List Nat := [1, 1, 3, 2, 1, 4, 3, 7]
def baseStart_1788631 : Nat := 118140960795 + 1788631 * 2 ^ 59
def prefixEnd_1788631 : Nat := 4983230072969 + 3 ^ 40 * 1788631 * 2
def baseEnd_1788631 : Nat := 68031660483859015310129

theorem tailTrace_1788631 : CollatzResearch.WordTrace tailWord_1788631 prefixEnd_1788631 68031660483859015310129 := by
  unfold tailWord_1788631
  simp only [CollatzResearch.WordTrace]
  refine ⟨65236731983102835699893747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43491154655401890466595831 65236731983102835699893747)
  ·
    refine ⟨97855097974654253549840621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65236731983102835699893747 97855097974654253549840621)
    ·
      refine ⟨36695661740495345081190233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97855097974654253549840621 36695661740495345081190233)
      ·
        refine ⟨27521746305371508810892675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36695661740495345081190233 27521746305371508810892675)
        ·
          refine ⟨41282619458057263216339013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27521746305371508810892675 41282619458057263216339013)
          ·
            refine ⟨7740491148385736853063565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41282619458057263216339013 7740491148385736853063565)
            ·
              refine ⟨2902684180644651319898837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7740491148385736853063565 2902684180644651319898837)
              ·
                refine ⟨68031660483859015310129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2902684180644651319898837 68031660483859015310129)
                ·
                  rfl

theorem cell22_1788631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 7].length) (baseStart_1788631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788631 prefixEnd_1788631 := by exact prefixLift 1788631
  have htrace : WordTrace (prefixWord ++ tailWord_1788631) baseStart_1788631 baseEnd_1788631 := by
    simpa [prefixWord, tailWord_1788631, baseEnd_1788631] using wordTrace_append hprefix tailTrace_1788631
  have hstable : (prefixWord ++ tailWord_1788631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788631).length < 2 ^ (prefixWord ++ tailWord_1788631).sum := by decide
  have hdescent : baseEnd_1788631 < baseStart_1788631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788680 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_1788680 : Nat := 118140960795 + 1788680 * 2 ^ 59
def prefixEnd_1788680 : Nat := 4983230072969 + 3 ^ 40 * 1788680 * 2
def baseEnd_1788680 : Nat := 612301718056111343316011

theorem tailTrace_1788680 : CollatzResearch.WordTrace tailWord_1788680 prefixEnd_1788680 612301718056111343316011 := by
  unfold tailWord_1788680
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619259579962658534213747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43492346106616878045618329 32619259579962658534213747)
  ·
    refine ⟨48928889369943987801320621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32619259579962658534213747 48928889369943987801320621)
    ·
      refine ⟨18348333513728995425495233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48928889369943987801320621 18348333513728995425495233)
      ·
        refine ⟨13761250135296746569121425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18348333513728995425495233 13761250135296746569121425)
        ·
          refine ⟨10320937601472559926841069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13761250135296746569121425 10320937601472559926841069)
          ·
            refine ⟨3870351600552209972565401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10320937601472559926841069 3870351600552209972565401)
            ·
              refine ⟨2902763700414157479424051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870351600552209972565401 2902763700414157479424051)
              ·
                refine ⟨4354145550621236219136077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902763700414157479424051 4354145550621236219136077)
                ·
                  refine ⟨1632804581482963582176029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4354145550621236219136077 1632804581482963582176029)
                  ·
                    refine ⟨612301718056111343316011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632804581482963582176029 612301718056111343316011)
                    ·
                      rfl

theorem cell22_1788680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_1788680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788680 prefixEnd_1788680 := by exact prefixLift 1788680
  have htrace : WordTrace (prefixWord ++ tailWord_1788680) baseStart_1788680 baseEnd_1788680 := by
    simpa [prefixWord, tailWord_1788680, baseEnd_1788680] using wordTrace_append hprefix tailTrace_1788680
  have hstable : (prefixWord ++ tailWord_1788680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788680).length < 2 ^ (prefixWord ++ tailWord_1788680).sum := by decide
  have hdescent : baseEnd_1788680 < baseStart_1788680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788691 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_1788691 : Nat := 118140960795 + 1788691 * 2 ^ 59
def prefixEnd_1788691 : Nat := 4983230072969 + 3 ^ 40 * 1788691 * 2
def baseEnd_1788691 : Nat := 612305483580910981290977

theorem tailTrace_1788691 : CollatzResearch.WordTrace tailWord_1788691 prefixEnd_1788691 612305483580910981290977 := by
  unfold tailWord_1788691
  simp only [CollatzResearch.WordTrace]
  refine ⟨65238920362885465947077927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43492613575256977298051951 65238920362885465947077927)
  ·
    refine ⟨97858380544328198920616891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65238920362885465947077927 97858380544328198920616891)
    ·
      refine ⟨146787570816492298380925337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97858380544328198920616891 146787570816492298380925337)
      ·
        refine ⟨110090678112369223785694003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146787570816492298380925337 110090678112369223785694003)
        ·
          refine ⟨165136017168553835678541005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110090678112369223785694003 165136017168553835678541005)
          ·
            refine ⟨61926006438207688379452877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165136017168553835678541005 61926006438207688379452877)
            ·
              refine ⟨23222252414327883142294829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61926006438207688379452877 23222252414327883142294829)
              ·
                refine ⟨8708344655372956178360561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23222252414327883142294829 8708344655372956178360561)
                ·
                  refine ⟨6531258491529717133770421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8708344655372956178360561 6531258491529717133770421)
                  ·
                    refine ⟨612305483580910981290977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6531258491529717133770421 612305483580910981290977)
                    ·
                      rfl

theorem cell22_1788691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_1788691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788691 prefixEnd_1788691 := by exact prefixLift 1788691
  have htrace : WordTrace (prefixWord ++ tailWord_1788691) baseStart_1788691 baseEnd_1788691 := by
    simpa [prefixWord, tailWord_1788691, baseEnd_1788691] using wordTrace_append hprefix tailTrace_1788691
  have hstable : (prefixWord ++ tailWord_1788691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788691).length < 2 ^ (prefixWord ++ tailWord_1788691).sum := by decide
  have hdescent : baseEnd_1788691 < baseStart_1788691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788789 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 4]
def baseStart_1788789 : Nat := 118140960795 + 1788789 * 2 ^ 59
def prefixEnd_1788789 : Nat := 4983230072969 + 3 ^ 40 * 1788789 * 2
def baseEnd_1788789 : Nat := 204113010327890464113559

theorem tailTrace_1788789 : CollatzResearch.WordTrace tailWord_1788789 prefixEnd_1788789 204113010327890464113559 := by
  unfold tailWord_1788789
  simp only [CollatzResearch.WordTrace]
  refine ⟨65242494716530428684145421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43494996477686952456096947 65242494716530428684145421)
  ·
    refine ⟨24465935518698910756554533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65242494716530428684145421 24465935518698910756554533)
    ·
      refine ⟨4587362909756045766853975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24465935518698910756554533 4587362909756045766853975)
      ·
        refine ⟨6881044364634068650280963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587362909756045766853975 6881044364634068650280963)
        ·
          refine ⟨10321566546951102975421445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881044364634068650280963 10321566546951102975421445)
          ·
            refine ⟨1935293727553331807891521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10321566546951102975421445 1935293727553331807891521)
            ·
              refine ⟨1451470295664998855918641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935293727553331807891521 1451470295664998855918641)
              ·
                refine ⟨1088602721748749141938981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451470295664998855918641 1088602721748749141938981)
                ·
                  refine ⟨204113010327890464113559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088602721748749141938981 204113010327890464113559)
                  ·
                    rfl

theorem cell22_1788789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_1788789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788789 prefixEnd_1788789 := by exact prefixLift 1788789
  have htrace : WordTrace (prefixWord ++ tailWord_1788789) baseStart_1788789 baseEnd_1788789 := by
    simpa [prefixWord, tailWord_1788789, baseEnd_1788789] using wordTrace_append hprefix tailTrace_1788789
  have hstable : (prefixWord ++ tailWord_1788789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788789).length < 2 ^ (prefixWord ++ tailWord_1788789).sum := by decide
  have hdescent : baseEnd_1788789 < baseStart_1788789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788832 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 1, 3]
def baseStart_1788832 : Nat := 118140960795 + 1788832 * 2 ^ 59
def prefixEnd_1788832 : Nat := 4983230072969 + 3 ^ 40 * 1788832 * 2
def baseEnd_1788832 : Nat := 612353750762433613515545

theorem tailTrace_1788832 : CollatzResearch.WordTrace tailWord_1788832 prefixEnd_1788832 612353750762433613515545 := by
  unfold tailWord_1788832
  simp only [CollatzResearch.WordTrace]
  refine ⟨32622031527687323513980375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43496042036916431351973833 32622031527687323513980375)
  ·
    refine ⟨48933047291530985270970563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32622031527687323513980375 48933047291530985270970563)
    ·
      refine ⟨73399570937296477906455845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48933047291530985270970563 73399570937296477906455845)
      ·
        refine ⟨13762419550743089607460471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73399570937296477906455845 13762419550743089607460471)
        ·
          refine ⟨20643629326114634411190707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762419550743089607460471 20643629326114634411190707)
          ·
            refine ⟨30965443989171951616786061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643629326114634411190707 30965443989171951616786061)
            ·
              refine ⟨11612041495939481856294773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30965443989171951616786061 11612041495939481856294773)
              ·
                refine ⟨1088628890244326424027635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11612041495939481856294773 1088628890244326424027635)
                ·
                  refine ⟨1632943335366489636041453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088628890244326424027635 1632943335366489636041453)
                  ·
                    refine ⟨612353750762433613515545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1632943335366489636041453 612353750762433613515545)
                    ·
                      rfl

theorem cell22_1788832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_1788832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788832 prefixEnd_1788832 := by exact prefixLift 1788832
  have htrace : WordTrace (prefixWord ++ tailWord_1788832) baseStart_1788832 baseEnd_1788832 := by
    simpa [prefixWord, tailWord_1788832, baseEnd_1788832] using wordTrace_append hprefix tailTrace_1788832
  have hstable : (prefixWord ++ tailWord_1788832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788832).length < 2 ^ (prefixWord ++ tailWord_1788832).sum := by decide
  have hdescent : baseEnd_1788832 < baseStart_1788832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788862 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1788862 : Nat := 118140960795 + 1788862 * 2 ^ 59
def prefixEnd_1788862 : Nat := 4983230072969 + 3 ^ 40 * 1788862 * 2
def baseEnd_1788862 : Nat := 204121340125174511755151

theorem tailTrace_1788862 : CollatzResearch.WordTrace tailWord_1788862 prefixEnd_1788862 204121340125174511755151 := by
  unfold tailWord_1788862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155644655658245268944105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43496771496843974767701893 8155644655658245268944105)
  ·
    refine ⟨6116733491743683951708079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8155644655658245268944105 6116733491743683951708079)
    ·
      refine ⟨9175100237615525927562119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116733491743683951708079 9175100237615525927562119)
      ·
        refine ⟨13762650356423288891343179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175100237615525927562119 13762650356423288891343179)
        ·
          refine ⟨20643975534634933337014769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762650356423288891343179 20643975534634933337014769)
          ·
            refine ⟨15482981650976200002761077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20643975534634933337014769 15482981650976200002761077)
            ·
              refine ⟨1451529529779018750258851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15482981650976200002761077 1451529529779018750258851)
              ·
                refine ⟨2177294294668528125388277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451529529779018750258851 2177294294668528125388277)
                ·
                  refine ⟨204121340125174511755151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2177294294668528125388277 204121340125174511755151)
                  ·
                    rfl

theorem cell22_1788862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1788862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788862 prefixEnd_1788862 := by exact prefixLift 1788862
  have htrace : WordTrace (prefixWord ++ tailWord_1788862) baseStart_1788862 baseEnd_1788862 := by
    simpa [prefixWord, tailWord_1788862, baseEnd_1788862] using wordTrace_append hprefix tailTrace_1788862
  have hstable : (prefixWord ++ tailWord_1788862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788862).length < 2 ^ (prefixWord ++ tailWord_1788862).sum := by decide
  have hdescent : baseEnd_1788862 < baseStart_1788862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788875 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 1, 4]
def baseStart_1788875 : Nat := 118140960795 + 1788875 * 2 ^ 59
def prefixEnd_1788875 : Nat := 4983230072969 + 3 ^ 40 * 1788875 * 2
def baseEnd_1788875 : Nat := 612368470541195834690413

theorem tailTrace_1788875 : CollatzResearch.WordTrace tailWord_1788875 prefixEnd_1788875 612368470541195834690413 := by
  unfold tailWord_1788875
  simp only [CollatzResearch.WordTrace]
  refine ⟨65245631394218865371776079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43497087596145910247850719 65245631394218865371776079)
  ·
    refine ⟨97868447091328298057664119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65245631394218865371776079 97868447091328298057664119)
    ·
      refine ⟨146802670636992447086496179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97868447091328298057664119 146802670636992447086496179)
      ·
        refine ⟨220204005955488670629744269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146802670636992447086496179 220204005955488670629744269)
        ·
          refine ⟨82576502233308251486154101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220204005955488670629744269 82576502233308251486154101)
          ·
            refine ⟨7741547084372648576826947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82576502233308251486154101 7741547084372648576826947)
            ·
              refine ⟨11612320626558972865240421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741547084372648576826947 11612320626558972865240421)
              ·
                refine ⟨2177310117479807412232579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11612320626558972865240421 2177310117479807412232579)
                ·
                  refine ⟨3265965176219711118348869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177310117479807412232579 3265965176219711118348869)
                  ·
                    refine ⟨612368470541195834690413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3265965176219711118348869 612368470541195834690413)
                    ·
                      rfl

theorem cell22_1788875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4].length) (baseStart_1788875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788875 prefixEnd_1788875 := by exact prefixLift 1788875
  have htrace : WordTrace (prefixWord ++ tailWord_1788875) baseStart_1788875 baseEnd_1788875 := by
    simpa [prefixWord, tailWord_1788875, baseEnd_1788875] using wordTrace_append hprefix tailTrace_1788875
  have hstable : (prefixWord ++ tailWord_1788875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788875).length < 2 ^ (prefixWord ++ tailWord_1788875).sum := by decide
  have hdescent : baseEnd_1788875 < baseStart_1788875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1788926 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1788926 : Nat := 118140960795 + 1788926 * 2 ^ 59
def prefixEnd_1788926 : Nat := 4983230072969 + 3 ^ 40 * 1788926 * 2
def baseEnd_1788926 : Nat := 612385928883448701665257

theorem tailTrace_1788926 : CollatzResearch.WordTrace tailWord_1788926 prefixEnd_1788926 612385928883448701665257 := by
  unfold tailWord_1788926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155936439629262635235329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43498327678022734054588421 8155936439629262635235329)
  ·
    refine ⟨6116952329721946976426497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8155936439629262635235329 6116952329721946976426497)
    ·
      refine ⟨4587714247291460232319873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6116952329721946976426497 4587714247291460232319873)
      ·
        refine ⟨3440785685468595174239905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4587714247291460232319873 3440785685468595174239905)
        ·
          refine ⟨2580589264101446380679929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3440785685468595174239905 2580589264101446380679929)
          ·
            refine ⟨1935441948076084785509947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580589264101446380679929 1935441948076084785509947)
            ·
              refine ⟨2903162922114127178264921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935441948076084785509947 2903162922114127178264921)
              ·
                refine ⟨2177372191585595383698691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903162922114127178264921 2177372191585595383698691)
                ·
                  refine ⟨3266058287378393075548037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177372191585595383698691 3266058287378393075548037)
                  ·
                    refine ⟨612385928883448701665257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266058287378393075548037 612385928883448701665257)
                    ·
                      rfl

theorem cell22_1788926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1788926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1788926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1788926 prefixEnd_1788926 := by exact prefixLift 1788926
  have htrace : WordTrace (prefixWord ++ tailWord_1788926) baseStart_1788926 baseEnd_1788926 := by
    simpa [prefixWord, tailWord_1788926, baseEnd_1788926] using wordTrace_append hprefix tailTrace_1788926
  have hstable : (prefixWord ++ tailWord_1788926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1788926).length < 2 ^ (prefixWord ++ tailWord_1788926).sum := by decide
  have hdescent : baseEnd_1788926 < baseStart_1788926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1788926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789025 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 6]
def baseStart_1789025 : Nat := 118140960795 + 1789025 * 2 ^ 59
def prefixEnd_1789025 : Nat := 4983230072969 + 3 ^ 40 * 1789025 * 2
def baseEnd_1789025 : Nat := 204139939535548481146651

theorem tailTrace_1789025 : CollatzResearch.WordTrace tailWord_1789025 prefixEnd_1789025 204139939535548481146651 := by
  unfold tailWord_1789025
  simp only [CollatzResearch.WordTrace]
  refine ⟨65251102343675440989736529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43500734895783627326491019 65251102343675440989736529)
  ·
    refine ⟨48938326757756580742302397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65251102343675440989736529 48938326757756580742302397)
    ·
      refine ⟨18351872534158717778363399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48938326757756580742302397 18351872534158717778363399)
      ·
        refine ⟨27527808801238076667545099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18351872534158717778363399 27527808801238076667545099)
        ·
          refine ⟨41291713201857115001317649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27527808801238076667545099 41291713201857115001317649)
          ·
            refine ⟨30968784901392836250988237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41291713201857115001317649 30968784901392836250988237)
            ·
              refine ⟨11613294338022313594120589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30968784901392836250988237 11613294338022313594120589)
              ·
                refine ⟨4354985376758367597795221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11613294338022313594120589 4354985376758367597795221)
                ·
                  refine ⟨204139939535548481146651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4354985376758367597795221 204139939535548481146651)
                  ·
                    rfl

theorem cell22_1789025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_1789025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789025 prefixEnd_1789025 := by exact prefixLift 1789025
  have htrace : WordTrace (prefixWord ++ tailWord_1789025) baseStart_1789025 baseEnd_1789025 := by
    simpa [prefixWord, tailWord_1789025, baseEnd_1789025] using wordTrace_append hprefix tailTrace_1789025
  have hstable : (prefixWord ++ tailWord_1789025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789025).length < 2 ^ (prefixWord ++ tailWord_1789025).sum := by decide
  have hdescent : baseEnd_1789025 < baseStart_1789025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789055 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_1789055 : Nat := 118140960795 + 1789055 * 2 ^ 59
def prefixEnd_1789055 : Nat := 4983230072969 + 3 ^ 40 * 1789055 * 2
def baseEnd_1789055 : Nat := 612430088219735365189861

theorem tailTrace_1789055 : CollatzResearch.WordTrace tailWord_1789055 prefixEnd_1789055 612430088219735365189861 := by
  unfold tailWord_1789055
  simp only [CollatzResearch.WordTrace]
  refine ⟨65252196533566756113328619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43501464355711170742219079 65252196533566756113328619)
  ·
    refine ⟨97878294800350134169992929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65252196533566756113328619 97878294800350134169992929)
    ·
      refine ⟨73408721100262600627494697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97878294800350134169992929 73408721100262600627494697)
      ·
        refine ⟨55056540825196950470621023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73408721100262600627494697 55056540825196950470621023)
        ·
          refine ⟨82584811237795425705931535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55056540825196950470621023 82584811237795425705931535)
          ·
            refine ⟨123877216856693138558897303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82584811237795425705931535 123877216856693138558897303)
            ·
              refine ⟨185815825285039707838345955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123877216856693138558897303 185815825285039707838345955)
              ·
                refine ⟨278723737927559561757518933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185815825285039707838345955 278723737927559561757518933)
                ·
                  refine ⟨3266293803838588614345925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 278723737927559561757518933 3266293803838588614345925)
                  ·
                    refine ⟨612430088219735365189861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266293803838588614345925 612430088219735365189861)
                    ·
                      rfl

theorem cell22_1789055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_1789055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789055 prefixEnd_1789055 := by exact prefixLift 1789055
  have htrace : WordTrace (prefixWord ++ tailWord_1789055) baseStart_1789055 baseEnd_1789055 := by
    simpa [prefixWord, tailWord_1789055, baseEnd_1789055] using wordTrace_append hprefix tailTrace_1789055
  have hstable : (prefixWord ++ tailWord_1789055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789055).length < 2 ^ (prefixWord ++ tailWord_1789055).sum := by decide
  have hdescent : baseEnd_1789055 < baseStart_1789055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789074 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1789074 : Nat := 118140960795 + 1789074 * 2 ^ 59
def prefixEnd_1789074 : Nat := 4983230072969 + 3 ^ 40 * 1789074 * 2
def baseEnd_1789074 : Nat := 612436592308025648964803

theorem tailTrace_1789074 : CollatzResearch.WordTrace tailWord_1789074 prefixEnd_1789074 612436592308025648964803 := by
  unfold tailWord_1789074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313222380124480589567569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43501926346998614905513517 16313222380124480589567569)
  ·
    refine ⟨12234916785093360442175677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16313222380124480589567569 12234916785093360442175677)
    ·
      refine ⟨4588093794410010165815879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12234916785093360442175677 4588093794410010165815879)
      ·
        refine ⟨6882140691615015248723819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588093794410010165815879 6882140691615015248723819)
        ·
          refine ⟨10323211037422522873085729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882140691615015248723819 10323211037422522873085729)
          ·
            refine ⟨7742408278066892154814297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10323211037422522873085729 7742408278066892154814297)
            ·
              refine ⟨5806806208550169116110723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7742408278066892154814297 5806806208550169116110723)
              ·
                refine ⟨8710209312825253674166085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806806208550169116110723 8710209312825253674166085)
                ·
                  refine ⟨1633164246154735063906141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8710209312825253674166085 1633164246154735063906141)
                  ·
                    refine ⟨612436592308025648964803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633164246154735063906141 612436592308025648964803)
                    ·
                      rfl

theorem cell22_1789074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1789074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789074 prefixEnd_1789074 := by exact prefixLift 1789074
  have htrace : WordTrace (prefixWord ++ tailWord_1789074) baseStart_1789074 baseEnd_1789074 := by
    simpa [prefixWord, tailWord_1789074, baseEnd_1789074] using wordTrace_append hprefix tailTrace_1789074
  have hstable : (prefixWord ++ tailWord_1789074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789074).length < 2 ^ (prefixWord ++ tailWord_1789074).sum := by decide
  have hdescent : baseEnd_1789074 < baseStart_1789074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789100 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_1789100 : Nat := 118140960795 + 1789100 * 2 ^ 59
def prefixEnd_1789100 : Nat := 4983230072969 + 3 ^ 40 * 1789100 * 2
def baseEnd_1789100 : Nat := 612445492639370247814723

theorem tailTrace_1789100 : CollatzResearch.WordTrace tailWord_1789100 prefixEnd_1789100 612445492639370247814723 := by
  unfold tailWord_1789100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32626918909201864399358377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43502558545602485865811169 32626918909201864399358377)
  ·
    refine ⟨24470189181901398299518783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32626918909201864399358377 24470189181901398299518783)
    ·
      refine ⟨36705283772852097449278175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24470189181901398299518783 36705283772852097449278175)
      ·
        refine ⟨55057925659278146173917263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36705283772852097449278175 55057925659278146173917263)
        ·
          refine ⟨82586888488917219260875895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55057925659278146173917263 82586888488917219260875895)
          ·
            refine ⟨123880332733375828891313843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82586888488917219260875895 123880332733375828891313843)
            ·
              refine ⟨185820499100063743336970765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123880332733375828891313843 185820499100063743336970765)
              ·
                refine ⟨69682687162523903751364037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185820499100063743336970765 69682687162523903751364037)
                ·
                  refine ⟨13065503842973231953380757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69682687162523903751364037 13065503842973231953380757)
                  ·
                    refine ⟨612445492639370247814723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13065503842973231953380757 612445492639370247814723)
                    ·
                      rfl

theorem cell22_1789100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_1789100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789100 prefixEnd_1789100 := by exact prefixLift 1789100
  have htrace : WordTrace (prefixWord ++ tailWord_1789100) baseStart_1789100 baseEnd_1789100 := by
    simpa [prefixWord, tailWord_1789100, baseEnd_1789100] using wordTrace_append hprefix tailTrace_1789100
  have hstable : (prefixWord ++ tailWord_1789100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789100).length < 2 ^ (prefixWord ++ tailWord_1789100).sum := by decide
  have hdescent : baseEnd_1789100 < baseStart_1789100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789115 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 7]
def baseStart_1789115 : Nat := 118140960795 + 1789115 * 2 ^ 59
def prefixEnd_1789115 : Nat := 4983230072969 + 3 ^ 40 * 1789115 * 2
def baseEnd_1789115 : Nat := 204150209148638402896559

theorem tailTrace_1789115 : CollatzResearch.WordTrace tailWord_1789115 prefixEnd_1789115 204150209148638402896559 := by
  unfold tailWord_1789115
  simp only [CollatzResearch.WordTrace]
  refine ⟨65254384913349386360512799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43502923275566257573675199 65254384913349386360512799)
  ·
    refine ⟨97881577370024079540769199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65254384913349386360512799 97881577370024079540769199)
    ·
      refine ⟨146822366055036119311153799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97881577370024079540769199 146822366055036119311153799)
      ·
        refine ⟨220233549082554178966730699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146822366055036119311153799 220233549082554178966730699)
        ·
          refine ⟨330350323623831268450096049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220233549082554178966730699 330350323623831268450096049)
          ·
            refine ⟨247762742717873451337572037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330350323623831268450096049 247762742717873451337572037)
            ·
              refine ⟨46455514259601272125794757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247762742717873451337572037 46455514259601272125794757)
              ·
                refine ⟨8710408923675238523586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46455514259601272125794757 8710408923675238523586517)
                ·
                  refine ⟨204150209148638402896559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8710408923675238523586517 204150209148638402896559)
                  ·
                    rfl

theorem cell22_1789115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_1789115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789115 prefixEnd_1789115 := by exact prefixLift 1789115
  have htrace : WordTrace (prefixWord ++ tailWord_1789115) baseStart_1789115 baseEnd_1789115 := by
    simpa [prefixWord, tailWord_1789115, baseEnd_1789115] using wordTrace_append hprefix tailTrace_1789115
  have hstable : (prefixWord ++ tailWord_1789115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789115).length < 2 ^ (prefixWord ++ tailWord_1789115).sum := by decide
  have hdescent : baseEnd_1789115 < baseStart_1789115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789207 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1789207 : Nat := 118140960795 + 1789207 * 2 ^ 59
def prefixEnd_1789207 : Nat := 4983230072969 + 3 ^ 40 * 1789207 * 2
def baseEnd_1789207 : Nat := 612482120926057635389395

theorem tailTrace_1789207 : CollatzResearch.WordTrace tailWord_1789207 prefixEnd_1789207 612482120926057635389395 := by
  unfold tailWord_1789207
  simp only [CollatzResearch.WordTrace]
  refine ⟨65257740429016086072861875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43505160286010724048574583 65257740429016086072861875)
  ·
    refine ⟨97886610643524129109292813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65257740429016086072861875 97886610643524129109292813)
    ·
      refine ⟨36707478991321548415984805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97886610643524129109292813 36707478991321548415984805)
      ·
        refine ⟨6882652310872790327997151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36707478991321548415984805 6882652310872790327997151)
        ·
          refine ⟨10323978466309185491995727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882652310872790327997151 10323978466309185491995727)
          ·
            refine ⟨15485967699463778237993591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323978466309185491995727 15485967699463778237993591)
            ·
              refine ⟨23228951549195667356990387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485967699463778237993591 23228951549195667356990387)
              ·
                refine ⟨34843427323793501035485581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23228951549195667356990387 34843427323793501035485581)
                ·
                  refine ⟨13066285246422562888307093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34843427323793501035485581 13066285246422562888307093)
                  ·
                    refine ⟨612482120926057635389395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13066285246422562888307093 612482120926057635389395)
                    ·
                      rfl

theorem cell22_1789207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1789207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789207 prefixEnd_1789207 := by exact prefixLift 1789207
  have htrace : WordTrace (prefixWord ++ tailWord_1789207) baseStart_1789207 baseEnd_1789207 := by
    simpa [prefixWord, tailWord_1789207, baseEnd_1789207] using wordTrace_append hprefix tailTrace_1789207
  have hstable : (prefixWord ++ tailWord_1789207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789207).length < 2 ^ (prefixWord ++ tailWord_1789207).sum := by decide
  have hdescent : baseEnd_1789207 < baseStart_1789207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789224 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1789224 : Nat := 118140960795 + 1789224 * 2 ^ 59
def prefixEnd_1789224 : Nat := 4983230072969 + 3 ^ 40 * 1789224 * 2
def baseEnd_1789224 : Nat := 612487940373475257714343

theorem tailTrace_1789224 : CollatzResearch.WordTrace tailWord_1789224 prefixEnd_1789224 612487940373475257714343 := by
  unfold tailWord_1789224
  simp only [CollatzResearch.WordTrace]
  refine ⟨32629180234977248988115363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43505573646636331984153817 32629180234977248988115363)
  ·
    refine ⟨48943770352465873482173045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32629180234977248988115363 48943770352465873482173045)
    ·
      refine ⟨4588478470543675638953723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48943770352465873482173045 4588478470543675638953723)
      ·
        refine ⟨6882717705815513458430585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588478470543675638953723 6882717705815513458430585)
        ·
          refine ⟨5162038279361635093822939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882717705815513458430585 5162038279361635093822939)
          ·
            refine ⟨7743057419042452640734409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162038279361635093822939 7743057419042452640734409)
            ·
              refine ⟨5807293064281839480550807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743057419042452640734409 5807293064281839480550807)
              ·
                refine ⟨8710939596422759220826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807293064281839480550807 8710939596422759220826211)
                ·
                  refine ⟨13066409394634138831239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710939596422759220826211 13066409394634138831239317)
                  ·
                    refine ⟨612487940373475257714343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13066409394634138831239317 612487940373475257714343)
                    ·
                      rfl

theorem cell22_1789224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1789224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789224 prefixEnd_1789224 := by exact prefixLift 1789224
  have htrace : WordTrace (prefixWord ++ tailWord_1789224) baseStart_1789224 baseEnd_1789224 := by
    simpa [prefixWord, tailWord_1789224, baseEnd_1789224] using wordTrace_append hprefix tailTrace_1789224
  have hstable : (prefixWord ++ tailWord_1789224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789224).length < 2 ^ (prefixWord ++ tailWord_1789224).sum := by decide
  have hdescent : baseEnd_1789224 < baseStart_1789224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789226 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1789226 : Nat := 118140960795 + 1789226 * 2 ^ 59
def prefixEnd_1789226 : Nat := 4983230072969 + 3 ^ 40 * 1789226 * 2
def baseEnd_1789226 : Nat := 612488625014347919164337

theorem tailTrace_1789226 : CollatzResearch.WordTrace tailWord_1789226 prefixEnd_1789226 612488625014347919164337 := by
  unfold tailWord_1789226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314608353986813079450883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43505622277298168211869021 16314608353986813079450883)
  ·
    refine ⟨24471912530980219619176325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16314608353986813079450883 24471912530980219619176325)
    ·
      refine ⟨4588483599558791178595561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24471912530980219619176325 4588483599558791178595561)
      ·
        refine ⟨3441362699669093383946671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4588483599558791178595561 3441362699669093383946671)
        ·
          refine ⟨5162044049503640075920007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441362699669093383946671 5162044049503640075920007)
          ·
            refine ⟨7743066074255460113880011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162044049503640075920007 7743066074255460113880011)
            ·
              refine ⟨11614599111383190170820017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743066074255460113880011 11614599111383190170820017)
              ·
                refine ⟨8710949333537392628115013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614599111383190170820017 8710949333537392628115013)
                ·
                  refine ⟨1633303000038261117771565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8710949333537392628115013 1633303000038261117771565)
                  ·
                    refine ⟨612488625014347919164337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633303000038261117771565 612488625014347919164337)
                    ·
                      rfl

theorem cell22_1789226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1789226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789226 prefixEnd_1789226 := by exact prefixLift 1789226
  have htrace : WordTrace (prefixWord ++ tailWord_1789226) baseStart_1789226 baseEnd_1789226 := by
    simpa [prefixWord, tailWord_1789226, baseEnd_1789226] using wordTrace_append hprefix tailTrace_1789226
  have hstable : (prefixWord ++ tailWord_1789226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789226).length < 2 ^ (prefixWord ++ tailWord_1789226).sum := by decide
  have hdescent : baseEnd_1789226 < baseStart_1789226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789241 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_1789241 : Nat := 118140960795 + 1789241 * 2 ^ 59
def prefixEnd_1789241 : Nat := 4983230072969 + 3 ^ 40 * 1789241 * 2
def baseEnd_1789241 : Nat := 612493759820892880039291

theorem tailTrace_1789241 : CollatzResearch.WordTrace tailWord_1789241 prefixEnd_1789241 612493759820892880039291 := by
  unfold tailWord_1789241
  simp only [CollatzResearch.WordTrace]
  refine ⟨65258980510892909879599577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43505987007261939919733051 65258980510892909879599577)
  ·
    refine ⟨48944235383169682409699683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65258980510892909879599577 48944235383169682409699683)
    ·
      refine ⟨73416353074754523614549525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48944235383169682409699683 73416353074754523614549525)
      ·
        refine ⟨3441391550379118294432009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73416353074754523614549525 3441391550379118294432009)
        ·
          refine ⟨2581043662784338720824007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441391550379118294432009 2581043662784338720824007)
          ·
            refine ⟨3871565494176508081236011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581043662784338720824007 3871565494176508081236011)
            ·
              refine ⟨5807348241264762121854017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871565494176508081236011 5807348241264762121854017)
              ·
                refine ⟨4355511180948571591390513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807348241264762121854017 4355511180948571591390513)
                ·
                  refine ⟨3266633385711428693542885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355511180948571591390513 3266633385711428693542885)
                  ·
                    refine ⟨612493759820892880039291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266633385711428693542885 612493759820892880039291)
                    ·
                      rfl

theorem cell22_1789241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_1789241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789241 prefixEnd_1789241 := by exact prefixLift 1789241
  have htrace : WordTrace (prefixWord ++ tailWord_1789241) baseStart_1789241 baseEnd_1789241 := by
    simpa [prefixWord, tailWord_1789241, baseEnd_1789241] using wordTrace_append hprefix tailTrace_1789241
  have hstable : (prefixWord ++ tailWord_1789241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789241).length < 2 ^ (prefixWord ++ tailWord_1789241).sum := by decide
  have hdescent : baseEnd_1789241 < baseStart_1789241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789245 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 4]
def baseStart_1789245 : Nat := 118140960795 + 1789245 * 2 ^ 59
def prefixEnd_1789245 : Nat := 4983230072969 + 3 ^ 40 * 1789245 * 2
def baseEnd_1789245 : Nat := 204165043034212734313093

theorem tailTrace_1789245 : CollatzResearch.WordTrace tailWord_1789245 prefixEnd_1789245 204165043034212734313093 := by
  unfold tailWord_1789245
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259126402878418562745189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43506084268585612375163459 65259126402878418562745189)
  ·
    refine ⟨12236086200539703480514723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65259126402878418562745189 12236086200539703480514723)
    ·
      refine ⟨18354129300809555220772085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12236086200539703480514723 18354129300809555220772085)
      ·
        refine ⟨1720699621950895801947383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18354129300809555220772085 1720699621950895801947383)
        ·
          refine ⟨2581049432926343702921075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720699621950895801947383 2581049432926343702921075)
          ·
            refine ⟨3871574149389515554381613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581049432926343702921075 3871574149389515554381613)
            ·
              refine ⟨1451840306021068332893105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3871574149389515554381613 1451840306021068332893105)
              ·
                refine ⟨1088880229515801249669829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451840306021068332893105 1088880229515801249669829)
                ·
                  refine ⟨204165043034212734313093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088880229515801249669829 204165043034212734313093)
                  ·
                    rfl

theorem cell22_1789245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_1789245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789245 prefixEnd_1789245 := by exact prefixLift 1789245
  have htrace : WordTrace (prefixWord ++ tailWord_1789245) baseStart_1789245 baseEnd_1789245 := by
    simpa [prefixWord, tailWord_1789245, baseEnd_1789245] using wordTrace_append hprefix tailTrace_1789245
  have hstable : (prefixWord ++ tailWord_1789245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789245).length < 2 ^ (prefixWord ++ tailWord_1789245).sum := by decide
  have hdescent : baseEnd_1789245 < baseStart_1789245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789312 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_1789312 : Nat := 118140960795 + 1789312 * 2 ^ 59
def prefixEnd_1789312 : Nat := 4983230072969 + 3 ^ 40 * 1789312 * 2
def baseEnd_1789312 : Nat := 204172688190624120504691

theorem tailTrace_1789312 : CollatzResearch.WordTrace tailWord_1789312 prefixEnd_1789312 204172688190624120504691 := by
  unfold tailWord_1789312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32630785046817844502717095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43507713395757126003622793 32630785046817844502717095)
  ·
    refine ⟨48946177570226766754075643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32630785046817844502717095 48946177570226766754075643)
    ·
      refine ⟨73419266355340150131113465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48946177570226766754075643 73419266355340150131113465)
      ·
        refine ⟨55064449766505112598335099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73419266355340150131113465 55064449766505112598335099)
        ·
          refine ⟨82596674649757668897502649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55064449766505112598335099 82596674649757668897502649)
          ·
            refine ⟨61947505987318251673126987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82596674649757668897502649 61947505987318251673126987)
            ·
              refine ⟨92921258980977377509690481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61947505987318251673126987 92921258980977377509690481)
              ·
                refine ⟨69690944235733033132267861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92921258980977377509690481 69690944235733033132267861)
                ·
                  refine ⟨204172688190624120504691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69690944235733033132267861 204172688190624120504691)
                  ·
                    rfl

theorem cell22_1789312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_1789312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789312 prefixEnd_1789312 := by exact prefixLift 1789312
  have htrace : WordTrace (prefixWord ++ tailWord_1789312) baseStart_1789312 baseEnd_1789312 := by
    simpa [prefixWord, tailWord_1789312, baseEnd_1789312] using wordTrace_append hprefix tailTrace_1789312
  have hstable : (prefixWord ++ tailWord_1789312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789312).length < 2 ^ (prefixWord ++ tailWord_1789312).sum := by decide
  have hdescent : baseEnd_1789312 < baseStart_1789312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789344 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_1789344 : Nat := 118140960795 + 1789344 * 2 ^ 59
def prefixEnd_1789344 : Nat := 4983230072969 + 3 ^ 40 * 1789344 * 2
def baseEnd_1789344 : Nat := 612529018825834944713975

theorem tailTrace_1789344 : CollatzResearch.WordTrace tailWord_1789344 prefixEnd_1789344 612529018825834944713975 := by
  unfold tailWord_1789344
  simp only [CollatzResearch.WordTrace]
  refine ⟨32631368614759879235299543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43508491486346505647066057 32631368614759879235299543)
  ·
    refine ⟨48947052922139818852949315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32631368614759879235299543 48947052922139818852949315)
    ·
      refine ⟨73420579383209728279423973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48947052922139818852949315 73420579383209728279423973)
      ·
        refine ⟨13766358634351824052391995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73420579383209728279423973 13766358634351824052391995)
        ·
          refine ⟨20649537951527736078587993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13766358634351824052391995 20649537951527736078587993)
          ·
            refine ⟨15487153463645802058940995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20649537951527736078587993 15487153463645802058940995)
            ·
              refine ⟨23230730195468703088411493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15487153463645802058940995 23230730195468703088411493)
              ·
                refine ⟨4355761911650381829077155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23230730195468703088411493 4355761911650381829077155)
                ·
                  refine ⟨6533642867475572743615733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355761911650381829077155 6533642867475572743615733)
                  ·
                    refine ⟨612529018825834944713975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6533642867475572743615733 612529018825834944713975)
                    ·
                      rfl

theorem cell22_1789344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_1789344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789344 prefixEnd_1789344 := by exact prefixLift 1789344
  have htrace : WordTrace (prefixWord ++ tailWord_1789344) baseStart_1789344 baseEnd_1789344 := by
    simpa [prefixWord, tailWord_1789344, baseEnd_1789344] using wordTrace_append hprefix tailTrace_1789344
  have hstable : (prefixWord ++ tailWord_1789344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789344).length < 2 ^ (prefixWord ++ tailWord_1789344).sum := by decide
  have hdescent : baseEnd_1789344 < baseStart_1789344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789359 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_1789359 : Nat := 118140960795 + 1789359 * 2 ^ 59
def prefixEnd_1789359 : Nat := 4983230072969 + 3 ^ 40 * 1789359 * 2
def baseEnd_1789359 : Nat := 612534153632379905588929

theorem tailTrace_1789359 : CollatzResearch.WordTrace tailWord_1789359 prefixEnd_1789359 612534153632379905588929 := by
  unfold tailWord_1789359
  simp only [CollatzResearch.WordTrace]
  refine ⟨65263284324465416032395131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43508856216310277354930087 65263284324465416032395131)
  ·
    refine ⟨97894926486698124048592697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65263284324465416032395131 97894926486698124048592697)
    ·
      refine ⟨73421194865023593036444523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97894926486698124048592697 73421194865023593036444523)
      ·
        refine ⟨110131792297535389554666785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73421194865023593036444523 110131792297535389554666785)
        ·
          refine ⟨82598844223151542166000089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110131792297535389554666785 82598844223151542166000089)
          ·
            refine ⟨61949133167363656624500067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82598844223151542166000089 61949133167363656624500067)
            ·
              refine ⟨92923699751045484936750101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61949133167363656624500067 92923699751045484936750101)
              ·
                refine ⟨4355798425830257106410161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92923699751045484936750101 4355798425830257106410161)
                ·
                  refine ⟨3266848819372692829807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355798425830257106410161 3266848819372692829807621)
                  ·
                    refine ⟨612534153632379905588929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3266848819372692829807621 612534153632379905588929)
                    ·
                      rfl

theorem cell22_1789359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_1789359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789359 prefixEnd_1789359 := by exact prefixLift 1789359
  have htrace : WordTrace (prefixWord ++ tailWord_1789359) baseStart_1789359 baseEnd_1789359 := by
    simpa [prefixWord, tailWord_1789359, baseEnd_1789359] using wordTrace_append hprefix tailTrace_1789359
  have hstable : (prefixWord ++ tailWord_1789359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789359).length < 2 ^ (prefixWord ++ tailWord_1789359).sum := by decide
  have hdescent : baseEnd_1789359 < baseStart_1789359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789361 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_1789361 : Nat := 118140960795 + 1789361 * 2 ^ 59
def prefixEnd_1789361 : Nat := 4983230072969 + 3 ^ 40 * 1789361 * 2
def baseEnd_1789361 : Nat := 612534838273252567038923

theorem tailTrace_1789361 : CollatzResearch.WordTrace tailWord_1789361 prefixEnd_1789361 612534838273252567038923 := by
  unfold tailWord_1789361
  simp only [CollatzResearch.WordTrace]
  refine ⟨65263357270458170373967937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43508904846972113582645291 65263357270458170373967937)
  ·
    refine ⟨48947517952843627780475953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65263357270458170373967937 48947517952843627780475953)
    ·
      refine ⟨36710638464632720835356965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48947517952843627780475953 36710638464632720835356965)
      ·
        refine ⟨6883244712118635156629431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36710638464632720835356965 6883244712118635156629431)
        ·
          refine ⟨10324867068177952734944147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883244712118635156629431 10324867068177952734944147)
          ·
            refine ⟨15487300602266929102416221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324867068177952734944147 15487300602266929102416221)
            ·
              refine ⟨5807737725850098413406083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15487300602266929102416221 5807737725850098413406083)
              ·
                refine ⟨8711606588775147620109125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807737725850098413406083 8711606588775147620109125)
                ·
                  refine ⟨1633426235395340178770461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8711606588775147620109125 1633426235395340178770461)
                  ·
                    refine ⟨612534838273252567038923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633426235395340178770461 612534838273252567038923)
                    ·
                      rfl

theorem cell22_1789361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_1789361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789361 prefixEnd_1789361 := by exact prefixLift 1789361
  have htrace : WordTrace (prefixWord ++ tailWord_1789361) baseStart_1789361 baseEnd_1789361 := by
    simpa [prefixWord, tailWord_1789361, baseEnd_1789361] using wordTrace_append hprefix tailTrace_1789361
  have hstable : (prefixWord ++ tailWord_1789361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789361).length < 2 ^ (prefixWord ++ tailWord_1789361).sum := by decide
  have hdescent : baseEnd_1789361 < baseStart_1789361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789374 : List Nat := [4, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1789374 : Nat := 118140960795 + 1789374 * 2 ^ 59
def prefixEnd_1789374 : Nat := 4983230072969 + 3 ^ 40 * 1789374 * 2
def baseEnd_1789374 : Nat := 68059920937658318495987

theorem tailTrace_1789374 : CollatzResearch.WordTrace tailWord_1789374 prefixEnd_1789374 68059920937658318495987 := by
  unfold tailWord_1789374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157978927426384199273897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43509220946274049062794117 8157978927426384199273897)
  ·
    refine ⟨6118484195569788149455423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8157978927426384199273897 6118484195569788149455423)
    ·
      refine ⟨9177726293354682224183135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118484195569788149455423 9177726293354682224183135)
      ·
        refine ⟨13766589440032023336274703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9177726293354682224183135 13766589440032023336274703)
        ·
          refine ⟨20649884160048035004412055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13766589440032023336274703 20649884160048035004412055)
          ·
            refine ⟨30974826240072052506618083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20649884160048035004412055 30974826240072052506618083)
            ·
              refine ⟨46462239360108078759927125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30974826240072052506618083 46462239360108078759927125)
              ·
                refine ⟨68059920937658318495987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46462239360108078759927125 68059920937658318495987)
                ·
                  rfl

theorem cell22_1789374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1789374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789374 prefixEnd_1789374 := by exact prefixLift 1789374
  have htrace : WordTrace (prefixWord ++ tailWord_1789374) baseStart_1789374 baseEnd_1789374 := by
    simpa [prefixWord, tailWord_1789374, baseEnd_1789374] using wordTrace_append hprefix tailTrace_1789374
  have hstable : (prefixWord ++ tailWord_1789374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789374).length < 2 ^ (prefixWord ++ tailWord_1789374).sum := by decide
  have hdescent : baseEnd_1789374 < baseStart_1789374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789423 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 1, 3]
def baseStart_1789423 : Nat := 118140960795 + 1789423 * 2 ^ 59
def prefixEnd_1789423 : Nat := 4983230072969 + 3 ^ 40 * 1789423 * 2
def baseEnd_1789423 : Nat := 612556062140305071988733

theorem tailTrace_1789423 : CollatzResearch.WordTrace tailWord_1789423 prefixEnd_1789423 612556062140305071988733 := by
  unfold tailWord_1789423
  simp only [CollatzResearch.WordTrace]
  refine ⟨65265618596233554962724923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43510412397489036641816615 65265618596233554962724923)
  ·
    refine ⟨97898427894350332444087385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65265618596233554962724923 97898427894350332444087385)
    ·
      refine ⟨73423820920762749333065539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97898427894350332444087385 73423820920762749333065539)
      ·
        refine ⟨110135731381144123999598309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73423820920762749333065539 110135731381144123999598309)
        ·
          refine ⟨20650449633964523249924683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110135731381144123999598309 20650449633964523249924683)
          ·
            refine ⟨30975674450946784874887025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20650449633964523249924683 30975674450946784874887025)
            ·
              refine ⟨23231755838210088656165269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30975674450946784874887025 23231755838210088656165269)
              ·
                refine ⟨1088988554916097905757747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23231755838210088656165269 1088988554916097905757747)
                ·
                  refine ⟨1633482832374146858636621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088988554916097905757747 1633482832374146858636621)
                  ·
                    refine ⟨612556062140305071988733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633482832374146858636621 612556062140305071988733)
                    ·
                      rfl

theorem cell22_1789423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_1789423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789423 prefixEnd_1789423 := by exact prefixLift 1789423
  have htrace : WordTrace (prefixWord ++ tailWord_1789423) baseStart_1789423 baseEnd_1789423 := by
    simpa [prefixWord, tailWord_1789423, baseEnd_1789423] using wordTrace_append hprefix tailTrace_1789423
  have hstable : (prefixWord ++ tailWord_1789423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789423).length < 2 ^ (prefixWord ++ tailWord_1789423).sum := by decide
  have hdescent : baseEnd_1789423 < baseStart_1789423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789434 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1789434 : Nat := 118140960795 + 1789434 * 2 ^ 59
def prefixEnd_1789434 : Nat := 4983230072969 + 3 ^ 40 * 1789434 * 2
def baseEnd_1789434 : Nat := 612559827665104709963699

theorem tailTrace_1789434 : CollatzResearch.WordTrace tailWord_1789434 prefixEnd_1789434 612559827665104709963699 := by
  unfold tailWord_1789434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316504949798425960343839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43510679866129135894250237 16316504949798425960343839)
  ·
    refine ⟨24474757424697638940515759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16316504949798425960343839 24474757424697638940515759)
    ·
      refine ⟨36712136137046458410773639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24474757424697638940515759 36712136137046458410773639)
      ·
        refine ⟨55068204205569687616160459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36712136137046458410773639 55068204205569687616160459)
        ·
          refine ⟨82602306308354531424240689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55068204205569687616160459 82602306308354531424240689)
          ·
            refine ⟨61951729731265898568180517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82602306308354531424240689 61951729731265898568180517)
            ·
              refine ⟨11615949324612355981533847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61951729731265898568180517 11615949324612355981533847)
              ·
                refine ⟨17423923986918533972300771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11615949324612355981533847 17423923986918533972300771)
                ·
                  refine ⟨26135885980377800958451157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17423923986918533972300771 26135885980377800958451157)
                  ·
                    refine ⟨612559827665104709963699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26135885980377800958451157 612559827665104709963699)
                    ·
                      rfl

theorem cell22_1789434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1789434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789434 prefixEnd_1789434 := by exact prefixLift 1789434
  have htrace : WordTrace (prefixWord ++ tailWord_1789434) baseStart_1789434 baseEnd_1789434 := by
    simpa [prefixWord, tailWord_1789434, baseEnd_1789434] using wordTrace_append hprefix tailTrace_1789434
  have hstable : (prefixWord ++ tailWord_1789434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789434).length < 2 ^ (prefixWord ++ tailWord_1789434).sum := by decide
  have hdescent : baseEnd_1789434 < baseStart_1789434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789496 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_1789496 : Nat := 118140960795 + 1789496 * 2 ^ 59
def prefixEnd_1789496 : Nat := 4983230072969 + 3 ^ 40 * 1789496 * 2
def baseEnd_1789496 : Nat := 612581051532157214913509

theorem tailTrace_1789496 : CollatzResearch.WordTrace tailWord_1789496 prefixEnd_1789496 612581051532157214913509 := by
  unfold tailWord_1789496
  simp only [CollatzResearch.WordTrace]
  refine ⟨32634140562484544215066171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43512187416646058953421561 32634140562484544215066171)
  ·
    refine ⟨48951210843726816322599257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32634140562484544215066171 48951210843726816322599257)
    ·
      refine ⟨36713408132795112241949443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48951210843726816322599257 36713408132795112241949443)
      ·
        refine ⟨55070112199192668362924165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36713408132795112241949443 55070112199192668362924165)
        ·
          refine ⟨10325646037348625318048281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55070112199192668362924165 10325646037348625318048281)
          ·
            refine ⟨7744234528011468988536211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10325646037348625318048281 7744234528011468988536211)
            ·
              refine ⟨11616351792017203482804317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7744234528011468988536211 11616351792017203482804317)
              ·
                refine ⟨4356131922006451306051619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11616351792017203482804317 4356131922006451306051619)
                ·
                  refine ⟨6534197883009676959077429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356131922006451306051619 6534197883009676959077429)
                  ·
                    refine ⟨612581051532157214913509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6534197883009676959077429 612581051532157214913509)
                    ·
                      rfl

theorem cell22_1789496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_1789496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789496 prefixEnd_1789496 := by exact prefixLift 1789496
  have htrace : WordTrace (prefixWord ++ tailWord_1789496) baseStart_1789496 baseEnd_1789496 := by
    simpa [prefixWord, tailWord_1789496, baseEnd_1789496] using wordTrace_append hprefix tailTrace_1789496
  have hstable : (prefixWord ++ tailWord_1789496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789496).length < 2 ^ (prefixWord ++ tailWord_1789496).sum := by decide
  have hdescent : baseEnd_1789496 < baseStart_1789496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789616 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_1789616 : Nat := 118140960795 + 1789616 * 2 ^ 59
def prefixEnd_1789616 : Nat := 4983230072969 + 3 ^ 40 * 1789616 * 2
def baseEnd_1789616 : Nat := 204207376661505633971047

theorem tailTrace_1789616 : CollatzResearch.WordTrace tailWord_1789616 prefixEnd_1789616 204207376661505633971047 := by
  unfold tailWord_1789616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32636328942267174462250351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43515105256356232616333801 32636328942267174462250351)
  ·
    refine ⟨48954493413400761693375527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32636328942267174462250351 48954493413400761693375527)
    ·
      refine ⟨73431740120101142540063291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48954493413400761693375527 73431740120101142540063291)
      ·
        refine ⟨110147610180151713810094937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73431740120101142540063291 110147610180151713810094937)
        ·
          refine ⟨82610707635113785357571203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110147610180151713810094937 82610707635113785357571203)
          ·
            refine ⟨123916061452670678036356805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82610707635113785357571203 123916061452670678036356805)
            ·
              refine ⟨23234261522375752131816901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123916061452670678036356805 23234261522375752131816901)
              ·
                refine ⟨4356424035445453524715669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23234261522375752131816901 4356424035445453524715669)
                ·
                  refine ⟨204207376661505633971047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4356424035445453524715669 204207376661505633971047)
                  ·
                    rfl

theorem cell22_1789616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_1789616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789616 prefixEnd_1789616 := by exact prefixLift 1789616
  have htrace : WordTrace (prefixWord ++ tailWord_1789616) baseStart_1789616 baseEnd_1789616 := by
    simpa [prefixWord, tailWord_1789616, baseEnd_1789616] using wordTrace_append hprefix tailTrace_1789616
  have hstable : (prefixWord ++ tailWord_1789616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789616).length < 2 ^ (prefixWord ++ tailWord_1789616).sum := by decide
  have hdescent : baseEnd_1789616 < baseStart_1789616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789665 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1789665 : Nat := 118140960795 + 1789665 * 2 ^ 59
def prefixEnd_1789665 : Nat := 4983230072969 + 3 ^ 40 * 1789665 * 2
def baseEnd_1789665 : Nat := 612638903685897107437991

theorem tailTrace_1789665 : CollatzResearch.WordTrace tailWord_1789665 prefixEnd_1789665 612638903685897107437991 := by
  unfold tailWord_1789665
  simp only [CollatzResearch.WordTrace]
  refine ⟨65274445061356830293034449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43516296707571220195356299 65274445061356830293034449)
  ·
    refine ⟨48955833796017622719775837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65274445061356830293034449 48955833796017622719775837)
    ·
      refine ⟨18358437673506608519915939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48955833796017622719775837 18358437673506608519915939)
      ·
        refine ⟨27537656510259912779873909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18358437673506608519915939 27537656510259912779873909)
        ·
          refine ⟨2581655297836866823113179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27537656510259912779873909 2581655297836866823113179)
          ·
            refine ⟨3872482946755300234669769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581655297836866823113179 3872482946755300234669769)
            ·
              refine ⟨2904362210066475176002327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872482946755300234669769 2904362210066475176002327)
              ·
                refine ⟨4356543315099712764003491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904362210066475176002327 4356543315099712764003491)
                ·
                  refine ⟨6534814972649569146005237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356543315099712764003491 6534814972649569146005237)
                  ·
                    refine ⟨612638903685897107437991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6534814972649569146005237 612638903685897107437991)
                    ·
                      rfl

theorem cell22_1789665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1789665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789665 prefixEnd_1789665 := by exact prefixLift 1789665
  have htrace : WordTrace (prefixWord ++ tailWord_1789665) baseStart_1789665 baseEnd_1789665 := by
    simpa [prefixWord, tailWord_1789665, baseEnd_1789665] using wordTrace_append hprefix tailTrace_1789665
  have hstable : (prefixWord ++ tailWord_1789665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789665).length < 2 ^ (prefixWord ++ tailWord_1789665).sum := by decide
  have hdescent : baseEnd_1789665 < baseStart_1789665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789684 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1789684 : Nat := 118140960795 + 1789684 * 2 ^ 59
def prefixEnd_1789684 : Nat := 4983230072969 + 3 ^ 40 * 1789684 * 2
def baseEnd_1789684 : Nat := 204215135924729130404311

theorem tailTrace_1789684 : CollatzResearch.WordTrace tailWord_1789684 prefixEnd_1789684 204215135924729130404311 := by
  unfold tailWord_1789684
  simp only [CollatzResearch.WordTrace]
  refine ⟨32637569024143998268988053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43516758698858664358650737 32637569024143998268988053)
  ·
    refine ⟨1529886048006749918858815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32637569024143998268988053 1529886048006749918858815)
    ·
      refine ⟨2294829072010124878288223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529886048006749918858815 2294829072010124878288223)
      ·
        refine ⟨3442243608015187317432335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294829072010124878288223 3442243608015187317432335)
        ·
          refine ⟨5163365412022780976148503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442243608015187317432335 5163365412022780976148503)
          ·
            refine ⟨7745048118034171464222755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163365412022780976148503 7745048118034171464222755)
            ·
              refine ⟨11617572177051257196334133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745048118034171464222755 11617572177051257196334133)
              ·
                refine ⟨1089147391598555362156325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11617572177051257196334133 1089147391598555362156325)
                ·
                  refine ⟨204215135924729130404311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089147391598555362156325 204215135924729130404311)
                  ·
                    rfl

theorem cell22_1789684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1789684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789684 prefixEnd_1789684 := by exact prefixLift 1789684
  have htrace : WordTrace (prefixWord ++ tailWord_1789684) baseStart_1789684 baseEnd_1789684 := by
    simpa [prefixWord, tailWord_1789684, baseEnd_1789684] using wordTrace_append hprefix tailTrace_1789684
  have hstable : (prefixWord ++ tailWord_1789684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789684).length < 2 ^ (prefixWord ++ tailWord_1789684).sum := by decide
  have hdescent : baseEnd_1789684 < baseStart_1789684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789691 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_1789691 : Nat := 118140960795 + 1789691 * 2 ^ 59
def prefixEnd_1789691 : Nat := 4983230072969 + 3 ^ 40 * 1789691 * 2
def baseEnd_1789691 : Nat := 612647804017241706287911

theorem tailTrace_1789691 : CollatzResearch.WordTrace tailWord_1789691 prefixEnd_1789691 612647804017241706287911 := by
  unfold tailWord_1789691
  simp only [CollatzResearch.WordTrace]
  refine ⟨65275393359262636733480927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43516928906175091155653951 65275393359262636733480927)
  ·
    refine ⟨97913090038893955100221391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65275393359262636733480927 97913090038893955100221391)
    ·
      refine ⟨146869635058340932650332087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97913090038893955100221391 146869635058340932650332087)
      ·
        refine ⟨220304452587511398975498131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146869635058340932650332087 220304452587511398975498131)
        ·
          refine ⟨330456678881267098463247197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220304452587511398975498131 330456678881267098463247197)
          ·
            refine ⟨123921254580475161923717699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330456678881267098463247197 123921254580475161923717699)
            ·
              refine ⟨185881881870712742885576549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123921254580475161923717699 185881881870712742885576549)
              ·
                refine ⟨34852852850758639291045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185881881870712742885576549 34852852850758639291045603)
                ·
                  refine ⟨52279279276137958936568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34852852850758639291045603 52279279276137958936568405)
                  ·
                    refine ⟨612647804017241706287911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52279279276137958936568405 612647804017241706287911)
                    ·
                      rfl

theorem cell22_1789691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_1789691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789691 prefixEnd_1789691 := by exact prefixLift 1789691
  have htrace : WordTrace (prefixWord ++ tailWord_1789691) baseStart_1789691 baseEnd_1789691 := by
    simpa [prefixWord, tailWord_1789691, baseEnd_1789691] using wordTrace_append hprefix tailTrace_1789691
  have hstable : (prefixWord ++ tailWord_1789691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789691).length < 2 ^ (prefixWord ++ tailWord_1789691).sum := by decide
  have hdescent : baseEnd_1789691 < baseStart_1789691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789710 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1789710 : Nat := 118140960795 + 1789710 * 2 ^ 59
def prefixEnd_1789710 : Nat := 4983230072969 + 3 ^ 40 * 1789710 * 2
def baseEnd_1789710 : Nat := 612654308105531990062853

theorem tailTrace_1789710 : CollatzResearch.WordTrace tailWord_1789710 prefixEnd_1789710 612654308105531990062853 := by
  unfold tailWord_1789710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159510793274225372302823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43517390897462535318948389 8159510793274225372302823)
  ·
    refine ⟨12239266189911338058454235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8159510793274225372302823 12239266189911338058454235)
    ·
      refine ⟨18358899284867007087681353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12239266189911338058454235 18358899284867007087681353)
      ·
        refine ⟨13769174463650255315761015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18358899284867007087681353 13769174463650255315761015)
        ·
          refine ⟨20653761695475382973641523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13769174463650255315761015 20653761695475382973641523)
          ·
            refine ⟨30980642543213074460462285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653761695475382973641523 30980642543213074460462285)
            ·
              refine ⟨11617740953704902922673357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30980642543213074460462285 11617740953704902922673357)
              ·
                refine ⟨4356652857639338596002509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11617740953704902922673357 4356652857639338596002509)
                ·
                  refine ⟨1633744821614751973500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4356652857639338596002509 1633744821614751973500941)
                  ·
                    refine ⟨612654308105531990062853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633744821614751973500941 612654308105531990062853)
                    ·
                      rfl

theorem cell22_1789710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1789710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789710 prefixEnd_1789710 := by exact prefixLift 1789710
  have htrace : WordTrace (prefixWord ++ tailWord_1789710) baseStart_1789710 baseEnd_1789710 := by
    simpa [prefixWord, tailWord_1789710, baseEnd_1789710] using wordTrace_append hprefix tailTrace_1789710
  have hstable : (prefixWord ++ tailWord_1789710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789710).length < 2 ^ (prefixWord ++ tailWord_1789710).sum := by decide
  have hdescent : baseEnd_1789710 < baseStart_1789710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789716 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1789716 : Nat := 118140960795 + 1789716 * 2 ^ 59
def prefixEnd_1789716 : Nat := 4983230072969 + 3 ^ 40 * 1789716 * 2
def baseEnd_1789716 : Nat := 612656362028149974412835

theorem tailTrace_1789716 : CollatzResearch.WordTrace tailWord_1789716 prefixEnd_1789716 612656362028149974412835 := by
  unfold tailWord_1789716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638152592086033001570501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43517536789448044002094001 32638152592086033001570501)
  ·
    refine ⟨6119653611016131187794469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32638152592086033001570501 6119653611016131187794469)
    ·
      refine ⟨1147435052065524597711463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6119653611016131187794469 1147435052065524597711463)
      ·
        refine ⟨1721152578098286896567195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147435052065524597711463 1721152578098286896567195)
        ·
          refine ⟨2581728867147430344850793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721152578098286896567195 2581728867147430344850793)
          ·
            refine ⟨1936296650360572758638095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2581728867147430344850793 1936296650360572758638095)
            ·
              refine ⟨2904444975540859137957143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936296650360572758638095 2904444975540859137957143)
              ·
                refine ⟨4356667463311288706935715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904444975540859137957143 4356667463311288706935715)
                ·
                  refine ⟨6535001194966933060403573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356667463311288706935715 6535001194966933060403573)
                  ·
                    refine ⟨612656362028149974412835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6535001194966933060403573 612656362028149974412835)
                    ·
                      rfl

theorem cell22_1789716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1789716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789716 prefixEnd_1789716 := by exact prefixLift 1789716
  have htrace : WordTrace (prefixWord ++ tailWord_1789716) baseStart_1789716 baseEnd_1789716 := by
    simpa [prefixWord, tailWord_1789716, baseEnd_1789716] using wordTrace_append hprefix tailTrace_1789716
  have hstable : (prefixWord ++ tailWord_1789716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789716).length < 2 ^ (prefixWord ++ tailWord_1789716).sum := by decide
  have hdescent : baseEnd_1789716 < baseStart_1789716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789800 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1789800 : Nat := 118140960795 + 1789800 * 2 ^ 59
def prefixEnd_1789800 : Nat := 4983230072969 + 3 ^ 40 * 1789800 * 2
def baseEnd_1789800 : Nat := 612685116944801755312577

theorem tailTrace_1789800 : CollatzResearch.WordTrace tailWord_1789800 prefixEnd_1789800 612685116944801755312577 := by
  unfold tailWord_1789800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32639684457933874174599427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43519579277245165566132569 32639684457933874174599427)
  ·
    refine ⟨48959526686900811261899141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32639684457933874174599427 48959526686900811261899141)
    ·
      refine ⟨9179911253793902111606089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48959526686900811261899141 9179911253793902111606089)
      ·
        refine ⟨6884933440345426583704567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9179911253793902111606089 6884933440345426583704567)
        ·
          refine ⟨10327400160518139875556851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884933440345426583704567 10327400160518139875556851)
          ·
            refine ⟨15491100240777209813335277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10327400160518139875556851 15491100240777209813335277)
            ·
              refine ⟨5809162590291453680000729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15491100240777209813335277 5809162590291453680000729)
              ·
                refine ⟨4356871942718590260000547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809162590291453680000729 4356871942718590260000547)
                ·
                  refine ⟨6535307914077885390000821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356871942718590260000547 6535307914077885390000821)
                  ·
                    refine ⟨612685116944801755312577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6535307914077885390000821 612685116944801755312577)
                    ·
                      rfl

theorem cell22_1789800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1789800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789800 prefixEnd_1789800 := by exact prefixLift 1789800
  have htrace : WordTrace (prefixWord ++ tailWord_1789800) baseStart_1789800 baseEnd_1789800 := by
    simpa [prefixWord, tailWord_1789800, baseEnd_1789800] using wordTrace_append hprefix tailTrace_1789800
  have hstable : (prefixWord ++ tailWord_1789800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789800).length < 2 ^ (prefixWord ++ tailWord_1789800).sum := by decide
  have hdescent : baseEnd_1789800 < baseStart_1789800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789817 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_1789817 : Nat := 118140960795 + 1789817 * 2 ^ 59
def prefixEnd_1789817 : Nat := 4983230072969 + 3 ^ 40 * 1789817 * 2
def baseEnd_1789817 : Nat := 612690936392219377637525

theorem tailTrace_1789817 : CollatzResearch.WordTrace tailWord_1789817 prefixEnd_1789817 612690936392219377637525 := by
  unfold tailWord_1789817
  simp only [CollatzResearch.WordTrace]
  refine ⟨65279988956806160252567705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43519992637870773501711803 65279988956806160252567705)
  ·
    refine ⟨48959991717604620189425779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65279988956806160252567705 48959991717604620189425779)
    ·
      refine ⟨73439987576406930284138669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48959991717604620189425779 73439987576406930284138669)
      ·
        refine ⟨27539995341152598856552001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73439987576406930284138669 27539995341152598856552001)
        ·
          refine ⟨20654996505864449142414001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27539995341152598856552001 20654996505864449142414001)
          ·
            refine ⟨15491247379398336856810501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20654996505864449142414001 15491247379398336856810501)
            ·
              refine ⟨2904608883637188160651969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15491247379398336856810501 2904608883637188160651969)
              ·
                refine ⟨2178456662727891120488977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904608883637188160651969 2178456662727891120488977)
                ·
                  refine ⟨1633842497045918340366733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2178456662727891120488977 1633842497045918340366733)
                  ·
                    refine ⟨612690936392219377637525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633842497045918340366733 612690936392219377637525)
                    ·
                      rfl

theorem cell22_1789817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_1789817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789817 prefixEnd_1789817 := by exact prefixLift 1789817
  have htrace : WordTrace (prefixWord ++ tailWord_1789817) baseStart_1789817 baseEnd_1789817 := by
    simpa [prefixWord, tailWord_1789817, baseEnd_1789817] using wordTrace_append hprefix tailTrace_1789817
  have hstable : (prefixWord ++ tailWord_1789817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789817).length < 2 ^ (prefixWord ++ tailWord_1789817).sum := by decide
  have hdescent : baseEnd_1789817 < baseStart_1789817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789913 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 1, 3]
def baseStart_1789913 : Nat := 118140960795 + 1789913 * 2 ^ 59
def prefixEnd_1789913 : Nat := 4983230072969 + 3 ^ 40 * 1789913 * 2
def baseEnd_1789913 : Nat := 612723799154107127237231

theorem tailTrace_1789913 : CollatzResearch.WordTrace tailWord_1789913 prefixEnd_1789913 612723799154107127237231 := by
  unfold tailWord_1789913
  simp only [CollatzResearch.WordTrace]
  refine ⟨65283490364458368648062393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43522326909638912432041595 65283490364458368648062393)
  ·
    refine ⟨48962617773343776486046795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65283490364458368648062393 48962617773343776486046795)
    ·
      refine ⟨73443926660015664729070193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48962617773343776486046795 73443926660015664729070193)
      ·
        refine ⟨55082944995011748546802645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73443926660015664729070193 55082944995011748546802645)
        ·
          refine ⟨1291006523320587856565687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 55082944995011748546802645 1291006523320587856565687)
          ·
            refine ⟨1936509784980881784848531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291006523320587856565687 1936509784980881784848531)
            ·
              refine ⟨2904764677471322677272797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936509784980881784848531 2904764677471322677272797)
              ·
                refine ⟨1089286754051746003977299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904764677471322677272797 1089286754051746003977299)
                ·
                  refine ⟨1633930131077619005965949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089286754051746003977299 1633930131077619005965949)
                  ·
                    refine ⟨612723799154107127237231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633930131077619005965949 612723799154107127237231)
                    ·
                      rfl

theorem cell22_1789913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_1789913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789913 prefixEnd_1789913 := by exact prefixLift 1789913
  have htrace : WordTrace (prefixWord ++ tailWord_1789913) baseStart_1789913 baseEnd_1789913 := by
    simpa [prefixWord, tailWord_1789913, baseEnd_1789913] using wordTrace_append hprefix tailTrace_1789913
  have hstable : (prefixWord ++ tailWord_1789913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789913).length < 2 ^ (prefixWord ++ tailWord_1789913).sum := by decide
  have hdescent : baseEnd_1789913 < baseStart_1789913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1789988 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1789988 : Nat := 118140960795 + 1789988 * 2 ^ 59
def prefixEnd_1789988 : Nat := 4983230072969 + 3 ^ 40 * 1789988 * 2
def baseEnd_1789988 : Nat := 204249824395610643870667

theorem tailTrace_1789988 : CollatzResearch.WordTrace tailWord_1789988 prefixEnd_1789988 204249824395610643870667 := by
  unfold tailWord_1789988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32643112919593328228521309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43524150559457770971361745 32643112919593328228521309)
  ·
    refine ⟨12241167344847498085695491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32643112919593328228521309 12241167344847498085695491)
    ·
      refine ⟨18361751017271247128543237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12241167344847498085695491 18361751017271247128543237)
      ·
        refine ⟨3442828315738358836601857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18361751017271247128543237 3442828315738358836601857)
        ·
          refine ⟨2582121236803769127451393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442828315738358836601857 2582121236803769127451393)
          ·
            refine ⟨1936590927602826845588545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582121236803769127451393 1936590927602826845588545)
            ·
              refine ⟨1452443195702120134191409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936590927602826845588545 1452443195702120134191409)
              ·
                refine ⟨1089332396776590100643557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452443195702120134191409 1089332396776590100643557)
                ·
                  refine ⟨204249824395610643870667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089332396776590100643557 204249824395610643870667)
                  ·
                    rfl

theorem cell22_1789988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1789988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1789988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1789988 prefixEnd_1789988 := by exact prefixLift 1789988
  have htrace : WordTrace (prefixWord ++ tailWord_1789988) baseStart_1789988 baseEnd_1789988 := by
    simpa [prefixWord, tailWord_1789988, baseEnd_1789988] using wordTrace_append hprefix tailTrace_1789988
  have hstable : (prefixWord ++ tailWord_1789988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1789988).length < 2 ^ (prefixWord ++ tailWord_1789988).sum := by decide
  have hdescent : baseEnd_1789988 < baseStart_1789988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1789988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790010 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_1790010 : Nat := 118140960795 + 1790010 * 2 ^ 59
def prefixEnd_1790010 : Nat := 4983230072969 + 3 ^ 40 * 1790010 * 2
def baseEnd_1790010 : Nat := 204252334745477069187311

theorem tailTrace_1790010 : CollatzResearch.WordTrace tailWord_1790010 prefixEnd_1790010 204252334745477069187311 := by
  unfold tailWord_1790010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321757061276738553585871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43524685496737969476228989 16321757061276738553585871)
  ·
    refine ⟨24482635591915107830378807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16321757061276738553585871 24482635591915107830378807)
    ·
      refine ⟨36723953387872661745568211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24482635591915107830378807 36723953387872661745568211)
      ·
        refine ⟨55085930081808992618352317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36723953387872661745568211 55085930081808992618352317)
        ·
          refine ⟨20657223780678372231882119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55085930081808992618352317 20657223780678372231882119)
          ·
            refine ⟨30985835671017558347823179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20657223780678372231882119 30985835671017558347823179)
            ·
              refine ⟨46478753506526337521734769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30985835671017558347823179 46478753506526337521734769)
              ·
                refine ⟨34859065129894753141301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46478753506526337521734769 34859065129894753141301077)
                ·
                  refine ⟨204252334745477069187311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34859065129894753141301077 204252334745477069187311)
                  ·
                    rfl

theorem cell22_1790010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_1790010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790010 prefixEnd_1790010 := by exact prefixLift 1790010
  have htrace : WordTrace (prefixWord ++ tailWord_1790010) baseStart_1790010 baseEnd_1790010 := by
    simpa [prefixWord, tailWord_1790010, baseEnd_1790010] using wordTrace_append hprefix tailTrace_1790010
  have hstable : (prefixWord ++ tailWord_1790010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790010).length < 2 ^ (prefixWord ++ tailWord_1790010).sum := by decide
  have hdescent : baseEnd_1790010 < baseStart_1790010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790025 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_1790025 : Nat := 118140960795 + 1790025 * 2 ^ 59
def prefixEnd_1790025 : Nat := 4983230072969 + 3 ^ 40 * 1790025 * 2
def baseEnd_1790025 : Nat := 612762139042976168436887

theorem tailTrace_1790025 : CollatzResearch.WordTrace tailWord_1790025 prefixEnd_1790025 612762139042976168436887 := by
  unfold tailWord_1790025
  simp only [CollatzResearch.WordTrace]
  refine ⟨65287575340052611776139529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43525050226701741184093019 65287575340052611776139529)
  ·
    refine ⟨48965681505039458832104647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65287575340052611776139529 48965681505039458832104647)
    ·
      refine ⟨73448522257559188248156971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48965681505039458832104647 73448522257559188248156971)
      ·
        refine ⟨110172783386338782372235457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73448522257559188248156971 110172783386338782372235457)
        ·
          refine ⟨82629587539754086779176593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110172783386338782372235457 82629587539754086779176593)
          ·
            refine ⟨61972190654815565084382445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82629587539754086779176593 61972190654815565084382445)
            ·
              refine ⟨23239571495555836906643417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61972190654815565084382445 23239571495555836906643417)
              ·
                refine ⟨17429678621666877679982563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23239571495555836906643417 17429678621666877679982563)
                ·
                  refine ⟨26144517932500316519973845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17429678621666877679982563 26144517932500316519973845)
                  ·
                    refine ⟨612762139042976168436887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26144517932500316519973845 612762139042976168436887)
                    ·
                      rfl

theorem cell22_1790025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_1790025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790025 prefixEnd_1790025 := by exact prefixLift 1790025
  have htrace : WordTrace (prefixWord ++ tailWord_1790025) baseStart_1790025 baseEnd_1790025 := by
    simpa [prefixWord, tailWord_1790025, baseEnd_1790025] using wordTrace_append hprefix tailTrace_1790025
  have hstable : (prefixWord ++ tailWord_1790025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790025).length < 2 ^ (prefixWord ++ tailWord_1790025).sum := by decide
  have hdescent : baseEnd_1790025 < baseStart_1790025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790044 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_1790044 : Nat := 118140960795 + 1790044 * 2 ^ 59
def prefixEnd_1790044 : Nat := 4983230072969 + 3 ^ 40 * 1790044 * 2
def baseEnd_1790044 : Nat := 204256214377088817403943

theorem tailTrace_1790044 : CollatzResearch.WordTrace tailWord_1790044 prefixEnd_1790044 204256214377088817403943 := by
  unfold tailWord_1790044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32644134163491889010540593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43525512217989185347387457 32644134163491889010540593)
  ·
    refine ⟨24483100622618916757905445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32644134163491889010540593 24483100622618916757905445)
    ·
      refine ⟨4590581366741046892107271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24483100622618916757905445 4590581366741046892107271)
      ·
        refine ⟨6885872050111570338160907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590581366741046892107271 6885872050111570338160907)
        ·
          refine ⟨10328808075167355507241361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885872050111570338160907 10328808075167355507241361)
          ·
            refine ⟨7746606056375516630431021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10328808075167355507241361 7746606056375516630431021)
            ·
              refine ⟨2904977271140818736411633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7746606056375516630431021 2904977271140818736411633)
              ·
                refine ⟨2178732953355614052308725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904977271140818736411633 2178732953355614052308725)
                ·
                  refine ⟨204256214377088817403943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178732953355614052308725 204256214377088817403943)
                  ·
                    rfl

theorem cell22_1790044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_1790044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790044 prefixEnd_1790044 := by exact prefixLift 1790044
  have htrace : WordTrace (prefixWord ++ tailWord_1790044) baseStart_1790044 baseEnd_1790044 := by
    simpa [prefixWord, tailWord_1790044, baseEnd_1790044] using wordTrace_append hprefix tailTrace_1790044
  have hstable : (prefixWord ++ tailWord_1790044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790044).length < 2 ^ (prefixWord ++ tailWord_1790044).sum := by decide
  have hdescent : baseEnd_1790044 < baseStart_1790044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790087 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1790087 : Nat := 118140960795 + 1790087 * 2 ^ 59
def prefixEnd_1790087 : Nat := 4983230072969 + 3 ^ 40 * 1790087 * 2
def baseEnd_1790087 : Nat := 612783362910028673386697

theorem tailTrace_1790087 : CollatzResearch.WordTrace tailWord_1790087 prefixEnd_1790087 612783362910028673386697 := by
  unfold tailWord_1790087
  simp only [CollatzResearch.WordTrace]
  refine ⟨65289836665827996364896515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43526557777218664243264343 65289836665827996364896515)
  ·
    refine ⟨97934754998741994547344773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65289836665827996364896515 97934754998741994547344773)
    ·
      refine ⟨18362766562264123977627145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97934754998741994547344773 18362766562264123977627145)
      ·
        refine ⟨13772074921698092983220359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18362766562264123977627145 13772074921698092983220359)
        ·
          refine ⟨20658112382547139474830539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13772074921698092983220359 20658112382547139474830539)
          ·
            refine ⟨30987168573820709212245809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20658112382547139474830539 30987168573820709212245809)
            ·
              refine ⟨23240376430365531909184357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30987168573820709212245809 23240376430365531909184357)
              ·
                refine ⟨4357570580693537232972067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23240376430365531909184357 4357570580693537232972067)
                ·
                  refine ⟨6536355871040305849458101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357570580693537232972067 6536355871040305849458101)
                  ·
                    refine ⟨612783362910028673386697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6536355871040305849458101 612783362910028673386697)
                    ·
                      rfl

theorem cell22_1790087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1790087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790087 prefixEnd_1790087 := by exact prefixLift 1790087
  have htrace : WordTrace (prefixWord ++ tailWord_1790087) baseStart_1790087 baseEnd_1790087 := by
    simpa [prefixWord, tailWord_1790087, baseEnd_1790087] using wordTrace_append hprefix tailTrace_1790087
  have hstable : (prefixWord ++ tailWord_1790087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790087).length < 2 ^ (prefixWord ++ tailWord_1790087).sum := by decide
  have hdescent : baseEnd_1790087 < baseStart_1790087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790106 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_1790106 : Nat := 118140960795 + 1790106 * 2 ^ 59
def prefixEnd_1790106 : Nat := 4983230072969 + 3 ^ 40 * 1790106 * 2
def baseEnd_1790106 : Nat := 204263288999439652387213

theorem tailTrace_1790106 : CollatzResearch.WordTrace tailWord_1790106 prefixEnd_1790106 204263288999439652387213 := by
  unfold tailWord_1790106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322632413189790652459543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43527019768506108406558781 16322632413189790652459543)
  ·
    refine ⟨24483948619784685978689315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16322632413189790652459543 24483948619784685978689315)
    ·
      refine ⟨36725922929677028968033973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483948619784685978689315 36725922929677028968033973)
      ·
        refine ⟨3443055274657221465753185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36725922929677028968033973 3443055274657221465753185)
        ·
          refine ⟨2582291455992916099314889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443055274657221465753185 2582291455992916099314889)
          ·
            refine ⟨1936718591994687074486167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582291455992916099314889 1936718591994687074486167)
            ·
              refine ⟨2905077887992030611729251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936718591994687074486167 2905077887992030611729251)
              ·
                refine ⟨4357616831988045917593877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905077887992030611729251 4357616831988045917593877)
                ·
                  refine ⟨204263288999439652387213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4357616831988045917593877 204263288999439652387213)
                  ·
                    rfl

theorem cell22_1790106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_1790106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790106 prefixEnd_1790106 := by exact prefixLift 1790106
  have htrace : WordTrace (prefixWord ++ tailWord_1790106) baseStart_1790106 baseEnd_1790106 := by
    simpa [prefixWord, tailWord_1790106, baseEnd_1790106] using wordTrace_append hprefix tailTrace_1790106
  have hstable : (prefixWord ++ tailWord_1790106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790106).length < 2 ^ (prefixWord ++ tailWord_1790106).sum := by decide
  have hdescent : baseEnd_1790106 < baseStart_1790106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790117 : List Nat := [1, 3, 1, 2, 1, 3, 4, 7]
def baseStart_1790117 : Nat := 118140960795 + 1790117 * 2 ^ 59
def prefixEnd_1790117 : Nat := 4983230072969 + 3 ^ 40 * 1790117 * 2
def baseEnd_1790117 : Nat := 68088181391457621681845

theorem tailTrace_1790117 : CollatzResearch.WordTrace tailWord_1790117 prefixEnd_1790117 68088181391457621681845 := by
  unfold tailWord_1790117
  simp only [CollatzResearch.WordTrace]
  refine ⟨65290930855719311488488605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43527287237146207658992403 65290930855719311488488605)
  ·
    refine ⟨24484099070894741808183227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65290930855719311488488605 24484099070894741808183227)
    ·
      refine ⟨36726148606342112712274841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24484099070894741808183227 36726148606342112712274841)
      ·
        refine ⟨27544611454756584534206131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36726148606342112712274841 27544611454756584534206131)
        ·
          refine ⟨41316917182134876801309197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27544611454756584534206131 41316917182134876801309197)
          ·
            refine ⟨15493843943300578800490949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41316917182134876801309197 15493843943300578800490949)
            ·
              refine ⟨2905095739368858525092053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15493843943300578800490949 2905095739368858525092053)
              ·
                refine ⟨68088181391457621681845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2905095739368858525092053 68088181391457621681845)
                ·
                  rfl

theorem cell22_1790117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 7].length) (baseStart_1790117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790117 prefixEnd_1790117 := by exact prefixLift 1790117
  have htrace : WordTrace (prefixWord ++ tailWord_1790117) baseStart_1790117 baseEnd_1790117 := by
    simpa [prefixWord, tailWord_1790117, baseEnd_1790117] using wordTrace_append hprefix tailTrace_1790117
  have hstable : (prefixWord ++ tailWord_1790117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790117).length < 2 ^ (prefixWord ++ tailWord_1790117).sum := by decide
  have hdescent : baseEnd_1790117 < baseStart_1790117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790207 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 8]
def baseStart_1790207 : Nat := 118140960795 + 1790207 * 2 ^ 59
def prefixEnd_1790207 : Nat := 4983230072969 + 3 ^ 40 * 1790207 * 2
def baseEnd_1790207 : Nat := 204274813787462786795443

theorem tailTrace_1790207 : CollatzResearch.WordTrace tailWord_1790207 prefixEnd_1790207 204274813787462786795443 := by
  unfold tailWord_1790207
  simp only [CollatzResearch.WordTrace]
  refine ⟨65294213425393256859264875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43529475616928837906176583 65294213425393256859264875)
  ·
    refine ⟨97941320138089885288897313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65294213425393256859264875 97941320138089885288897313)
    ·
      refine ⟨73455990103567413966672985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97941320138089885288897313 73455990103567413966672985)
      ·
        refine ⟨55091992577675560475004739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73455990103567413966672985 55091992577675560475004739)
        ·
          refine ⟨82637988866513340712507109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55091992577675560475004739 82637988866513340712507109)
          ·
            refine ⟨15494622912471251383595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82637988866513340712507109 15494622912471251383595083)
            ·
              refine ⟨23241934368706877075392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15494622912471251383595083 23241934368706877075392625)
              ·
                refine ⟨17431450776530157806544469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23241934368706877075392625 17431450776530157806544469)
                ·
                  refine ⟨204274813787462786795443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17431450776530157806544469 204274813787462786795443)
                  ·
                    rfl

theorem cell22_1790207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_1790207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790207 prefixEnd_1790207 := by exact prefixLift 1790207
  have htrace : WordTrace (prefixWord ++ tailWord_1790207) baseStart_1790207 baseEnd_1790207 := by
    simpa [prefixWord, tailWord_1790207, baseEnd_1790207] using wordTrace_append hprefix tailTrace_1790207
  have hstable : (prefixWord ++ tailWord_1790207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790207).length < 2 ^ (prefixWord ++ tailWord_1790207).sum := by decide
  have hdescent : baseEnd_1790207 < baseStart_1790207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790329 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1790329 : Nat := 118140960795 + 1790329 * 2 ^ 59
def prefixEnd_1790329 : Nat := 4983230072969 + 3 ^ 40 * 1790329 * 2
def baseEnd_1790329 : Nat := 612866204455620708835955

theorem tailTrace_1790329 : CollatzResearch.WordTrace tailWord_1790329 prefixEnd_1790329 612866204455620708835955 := by
  unfold tailWord_1790329
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298663130951271695206041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43532442087300847796804027 65298663130951271695206041)
  ·
    refine ⟨48973997348213453771404531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65298663130951271695206041 48973997348213453771404531)
    ·
      refine ⟨73460996022320180657106797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48973997348213453771404531 73460996022320180657106797)
      ·
        refine ⟨27547873508370067746415049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73460996022320180657106797 27547873508370067746415049)
        ·
          refine ⟨20660905131277550809811287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27547873508370067746415049 20660905131277550809811287)
          ·
            refine ⟨30991357696916326214716931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20660905131277550809811287 30991357696916326214716931)
            ·
              refine ⟨46487036545374489322075397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30991357696916326214716931 46487036545374489322075397)
              ·
                refine ⟨8716319352257716747889137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46487036545374489322075397 8716319352257716747889137)
                ·
                  refine ⟨6537239514193287560916853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716319352257716747889137 6537239514193287560916853)
                  ·
                    refine ⟨612866204455620708835955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6537239514193287560916853 612866204455620708835955)
                    ·
                      rfl

theorem cell22_1790329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1790329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790329 prefixEnd_1790329 := by exact prefixLift 1790329
  have htrace : WordTrace (prefixWord ++ tailWord_1790329) baseStart_1790329 baseEnd_1790329 := by
    simpa [prefixWord, tailWord_1790329, baseEnd_1790329] using wordTrace_append hprefix tailTrace_1790329
  have hstable : (prefixWord ++ tailWord_1790329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790329).length < 2 ^ (prefixWord ++ tailWord_1790329).sum := by decide
  have hdescent : baseEnd_1790329 < baseStart_1790329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790331 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 5]
def baseStart_1790331 : Nat := 118140960795 + 1790331 * 2 ^ 59
def prefixEnd_1790331 : Nat := 4983230072969 + 3 ^ 40 * 1790331 * 2
def baseEnd_1790331 : Nat := 204288963032164456761983

theorem tailTrace_1790331 : CollatzResearch.WordTrace tailWord_1790331 prefixEnd_1790331 204288963032164456761983 := by
  unfold tailWord_1790331
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298736076944026036778847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43532490717962684024519231 65298736076944026036778847)
  ·
    refine ⟨97948104115416039055168271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65298736076944026036778847 97948104115416039055168271)
    ·
      refine ⟨146922156173124058582752407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97948104115416039055168271 146922156173124058582752407)
      ·
        refine ⟨220383234259686087874128611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146922156173124058582752407 220383234259686087874128611)
        ·
          refine ⟨330574851389529131811192917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220383234259686087874128611 330574851389529131811192917)
          ·
            refine ⟨3873924039721044513412417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 330574851389529131811192917 3873924039721044513412417)
            ·
              refine ⟨2905443029790783385059313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873924039721044513412417 2905443029790783385059313)
              ·
                refine ⟨2179082272343087538794485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905443029790783385059313 2179082272343087538794485)
                ·
                  refine ⟨204288963032164456761983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179082272343087538794485 204288963032164456761983)
                  ·
                    rfl

theorem cell22_1790331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 5].length) (baseStart_1790331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790331 prefixEnd_1790331 := by exact prefixLift 1790331
  have htrace : WordTrace (prefixWord ++ tailWord_1790331) baseStart_1790331 baseEnd_1790331 := by
    simpa [prefixWord, tailWord_1790331, baseEnd_1790331] using wordTrace_append hprefix tailTrace_1790331
  have hstable : (prefixWord ++ tailWord_1790331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790331).length < 2 ^ (prefixWord ++ tailWord_1790331).sum := by decide
  have hdescent : baseEnd_1790331 < baseStart_1790331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790359 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 8]
def baseStart_1790359 : Nat := 118140960795 + 1790359 * 2 ^ 59
def prefixEnd_1790359 : Nat := 4983230072969 + 3 ^ 40 * 1790359 * 2
def baseEnd_1790359 : Nat := 204292158022903543528621

theorem tailTrace_1790359 : CollatzResearch.WordTrace tailWord_1790359 prefixEnd_1790359 204292158022903543528621 := by
  unfold tailWord_1790359
  simp only [CollatzResearch.WordTrace]
  refine ⟨65299757320842586818798131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43533171547228391212532087 65299757320842586818798131)
  ·
    refine ⟨97949635981263880228197197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65299757320842586818798131 97949635981263880228197197)
    ·
      refine ⟨36731113492973955085573949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97949635981263880228197197 36731113492973955085573949)
      ·
        refine ⟨13774167559865233157090231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36731113492973955085573949 13774167559865233157090231)
        ·
          refine ⟨20661251339797849735635347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13774167559865233157090231 20661251339797849735635347)
          ·
            refine ⟨30991877009696774603453021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20661251339797849735635347 30991877009696774603453021)
            ·
              refine ⟨11621953878636290476294883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30991877009696774603453021 11621953878636290476294883)
              ·
                refine ⟨17432930817954435714442325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621953878636290476294883 17432930817954435714442325)
                ·
                  refine ⟨204292158022903543528621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17432930817954435714442325 204292158022903543528621)
                  ·
                    rfl

theorem cell22_1790359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_1790359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790359 prefixEnd_1790359 := by exact prefixLift 1790359
  have htrace : WordTrace (prefixWord ++ tailWord_1790359) baseStart_1790359 baseEnd_1790359 := by
    simpa [prefixWord, tailWord_1790359, baseEnd_1790359] using wordTrace_append hprefix tailTrace_1790359
  have hstable : (prefixWord ++ tailWord_1790359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790359).length < 2 ^ (prefixWord ++ tailWord_1790359).sum := by decide
  have hdescent : baseEnd_1790359 < baseStart_1790359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790361 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_1790361 : Nat := 118140960795 + 1790361 * 2 ^ 59
def prefixEnd_1790361 : Nat := 4983230072969 + 3 ^ 40 * 1790361 * 2
def baseEnd_1790361 : Nat := 612877158709583292035857

theorem tailTrace_1790361 : CollatzResearch.WordTrace tailWord_1790361 prefixEnd_1790361 612877158709583292035857 := by
  unfold tailWord_1790361
  simp only [CollatzResearch.WordTrace]
  refine ⟨65299830266835341160370937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43533220177890227440247291 65299830266835341160370937)
  ·
    refine ⟨48974872700126505870278203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65299830266835341160370937 48974872700126505870278203)
    ·
      refine ⟨73462309050189758805417305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48974872700126505870278203 73462309050189758805417305)
      ·
        refine ⟨55096731787642319104062979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73462309050189758805417305 55096731787642319104062979)
        ·
          refine ⟨82645097681463478656094469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55096731787642319104062979 82645097681463478656094469)
          ·
            refine ⟨15495955815274402248017713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82645097681463478656094469 15495955815274402248017713)
            ·
              refine ⟨11621966861455801686013285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15495955815274402248017713 11621966861455801686013285)
              ·
                refine ⟨2179118786522962816127491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11621966861455801686013285 2179118786522962816127491)
                ·
                  refine ⟨3268678179784444224191237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179118786522962816127491 3268678179784444224191237)
                  ·
                    refine ⟨612877158709583292035857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3268678179784444224191237 612877158709583292035857)
                    ·
                      rfl

theorem cell22_1790361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_1790361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790361 prefixEnd_1790361 := by exact prefixLift 1790361
  have htrace : WordTrace (prefixWord ++ tailWord_1790361) baseStart_1790361 baseEnd_1790361 := by
    simpa [prefixWord, tailWord_1790361, baseEnd_1790361] using wordTrace_append hprefix tailTrace_1790361
  have hstable : (prefixWord ++ tailWord_1790361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790361).length < 2 ^ (prefixWord ++ tailWord_1790361).sum := by decide
  have hdescent : baseEnd_1790361 < baseStart_1790361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790393 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 4]
def baseStart_1790393 : Nat := 118140960795 + 1790393 * 2 ^ 59
def prefixEnd_1790393 : Nat := 4983230072969 + 3 ^ 40 * 1790393 * 2
def baseEnd_1790393 : Nat := 204296037654515291745253

theorem tailTrace_1790393 : CollatzResearch.WordTrace tailWord_1790393 prefixEnd_1790393 204296037654515291745253 := by
  unfold tailWord_1790393
  simp only [CollatzResearch.WordTrace]
  refine ⟨65300997402719410625535833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43533998268479607083690555 65300997402719410625535833)
  ·
    refine ⟨48975748052039557969151875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65300997402719410625535833 48975748052039557969151875)
    ·
      refine ⟨73463622078059336953727813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48975748052039557969151875 73463622078059336953727813)
      ·
        refine ⟨13774429139636125678823965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73463622078059336953727813 13774429139636125678823965)
        ·
          refine ⟨5165410927363547129558987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13774429139636125678823965 5165410927363547129558987)
          ·
            refine ⟨7748116391045320694338481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165410927363547129558987 7748116391045320694338481)
            ·
              refine ⟨5811087293283990520753861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748116391045320694338481 5811087293283990520753861)
              ·
                refine ⟨1089578867490748222641349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5811087293283990520753861 1089578867490748222641349)
                ·
                  refine ⟨204296037654515291745253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089578867490748222641349 204296037654515291745253)
                  ·
                    rfl

theorem cell22_1790393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_1790393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790393 prefixEnd_1790393 := by exact prefixLift 1790393
  have htrace : WordTrace (prefixWord ++ tailWord_1790393) baseStart_1790393 baseEnd_1790393 := by
    simpa [prefixWord, tailWord_1790393, baseEnd_1790393] using wordTrace_append hprefix tailTrace_1790393
  have hstable : (prefixWord ++ tailWord_1790393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790393).length < 2 ^ (prefixWord ++ tailWord_1790393).sum := by decide
  have hdescent : baseEnd_1790393 < baseStart_1790393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790408 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_1790408 : Nat := 118140960795 + 1790408 * 2 ^ 59
def prefixEnd_1790408 : Nat := 4983230072969 + 3 ^ 40 * 1790408 * 2
def baseEnd_1790408 : Nat := 612893247770090836110713

theorem tailTrace_1790408 : CollatzResearch.WordTrace tailWord_1790408 prefixEnd_1790408 612893247770090836110713 := by
  unfold tailWord_1790408
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650772248832534093665939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43534362998443378791554585 32650772248832534093665939)
  ·
    refine ⟨48976158373248801140498909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32650772248832534093665939 48976158373248801140498909)
    ·
      refine ⟨18366059389968300427687091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48976158373248801140498909 18366059389968300427687091)
      ·
        refine ⟨27549089084952450641530637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18366059389968300427687091 27549089084952450641530637)
        ·
          refine ⟨10330908406857168990573989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27549089084952450641530637 10330908406857168990573989)
          ·
            refine ⟨1937045326285719185732623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10330908406857168990573989 1937045326285719185732623)
            ·
              refine ⟨2905567989428578778598935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937045326285719185732623 2905567989428578778598935)
              ·
                refine ⟨4358351984142868167898403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905567989428578778598935 4358351984142868167898403)
                ·
                  refine ⟨6537527976214302251847605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358351984142868167898403 6537527976214302251847605)
                  ·
                    refine ⟨612893247770090836110713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6537527976214302251847605 612893247770090836110713)
                    ·
                      rfl

theorem cell22_1790408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_1790408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790408 prefixEnd_1790408 := by exact prefixLift 1790408
  have htrace : WordTrace (prefixWord ++ tailWord_1790408) baseStart_1790408 baseEnd_1790408 := by
    simpa [prefixWord, tailWord_1790408, baseEnd_1790408] using wordTrace_append hprefix tailTrace_1790408
  have hstable : (prefixWord ++ tailWord_1790408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790408).length < 2 ^ (prefixWord ++ tailWord_1790408).sum := by decide
  have hdescent : baseEnd_1790408 < baseStart_1790408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790421 : List Nat := [1, 3, 2, 3, 1, 3, 1, 8]
def baseStart_1790421 : Nat := 118140960795 + 1790421 * 2 ^ 59
def prefixEnd_1790421 : Nat := 4983230072969 + 3 ^ 40 * 1790421 * 2
def baseEnd_1790421 : Nat := 68099744215084792837297

theorem tailTrace_1790421 : CollatzResearch.WordTrace tailWord_1790421 prefixEnd_1790421 68099744215084792837297 := by
  unfold tailWord_1790421
  simp only [CollatzResearch.WordTrace]
  refine ⟨65302018646617971407555117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43534679097745314271703411 65302018646617971407555117)
  ·
    refine ⟨24488256992481739277833169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65302018646617971407555117 24488256992481739277833169)
    ·
      refine ⟨18366192744361304458374877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24488256992481739277833169 18366192744361304458374877)
      ·
        refine ⟨6887322279135489171890579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18366192744361304458374877 6887322279135489171890579)
        ·
          refine ⟨10330983418703233757835869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887322279135489171890579 10330983418703233757835869)
          ·
            refine ⟨3874118782013712659188451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10330983418703233757835869 3874118782013712659188451)
            ·
              refine ⟨5811178173020568988782677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874118782013712659188451 5811178173020568988782677)
              ·
                refine ⟨68099744215084792837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5811178173020568988782677 68099744215084792837297)
                ·
                  rfl

theorem cell22_1790421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 8].length) (baseStart_1790421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790421 prefixEnd_1790421 := by exact prefixLift 1790421
  have htrace : WordTrace (prefixWord ++ tailWord_1790421) baseStart_1790421 baseEnd_1790421 := by
    simpa [prefixWord, tailWord_1790421, baseEnd_1790421] using wordTrace_append hprefix tailTrace_1790421
  have hstable : (prefixWord ++ tailWord_1790421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790421).length < 2 ^ (prefixWord ++ tailWord_1790421).sum := by decide
  have hdescent : baseEnd_1790421 < baseStart_1790421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790504 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1790504 : Nat := 118140960795 + 1790504 * 2 ^ 59
def prefixEnd_1790504 : Nat := 4983230072969 + 3 ^ 40 * 1790504 * 2
def baseEnd_1790504 : Nat := 612926110531978585710419

theorem tailTrace_1790504 : CollatzResearch.WordTrace tailWord_1790504 prefixEnd_1790504 612926110531978585710419 := by
  unfold tailWord_1790504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652522952658638291413283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43536697270211517721884377 32652522952658638291413283)
  ·
    refine ⟨48978784428987957437119925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32652522952658638291413283 48978784428987957437119925)
    ·
      refine ⟨4591761040217621009729993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48978784428987957437119925 4591761040217621009729993)
      ·
        refine ⟨3443820780163215757297495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4591761040217621009729993 3443820780163215757297495)
        ·
          refine ⟨5165731170244823635946243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443820780163215757297495 5165731170244823635946243)
          ·
            refine ⟨7748596755367235453919365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165731170244823635946243 7748596755367235453919365)
            ·
              refine ⟨1452861891631356647609881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7748596755367235453919365 1452861891631356647609881)
              ·
                refine ⟨1089646418723517485707411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452861891631356647609881 1089646418723517485707411)
                ·
                  refine ⟨1634469628085276228561117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089646418723517485707411 1634469628085276228561117)
                  ·
                    refine ⟨612926110531978585710419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634469628085276228561117 612926110531978585710419)
                    ·
                      rfl

theorem cell22_1790504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1790504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790504 prefixEnd_1790504 := by exact prefixLift 1790504
  have htrace : WordTrace (prefixWord ++ tailWord_1790504) baseStart_1790504 baseEnd_1790504 := by
    simpa [prefixWord, tailWord_1790504, baseEnd_1790504] using wordTrace_append hprefix tailTrace_1790504
  have hstable : (prefixWord ++ tailWord_1790504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790504).length < 2 ^ (prefixWord ++ tailWord_1790504).sum := by decide
  have hdescent : baseEnd_1790504 < baseStart_1790504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790545 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 4]
def baseStart_1790545 : Nat := 118140960795 + 1790545 * 2 ^ 59
def prefixEnd_1790545 : Nat := 4983230072969 + 3 ^ 40 * 1790545 * 2
def baseEnd_1790545 : Nat := 204313381889956048478431

theorem tailTrace_1790545 : CollatzResearch.WordTrace tailWord_1790545 prefixEnd_1790545 204313381889956048478431 := by
  unfold tailWord_1790545
  simp only [CollatzResearch.WordTrace]
  refine ⟨65306541298168740585069089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43537694198779160390046059 65306541298168740585069089)
  ·
    refine ⟨48979905973626555438801817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65306541298168740585069089 48979905973626555438801817)
    ·
      refine ⟨36734929480219916579101363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48979905973626555438801817 36734929480219916579101363)
      ·
        refine ⟨55102394220329874868652045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36734929480219916579101363 55102394220329874868652045)
        ·
          refine ⟨20663397832623703075744517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55102394220329874868652045 20663397832623703075744517)
          ·
            refine ⟨3874387093616944326702097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20663397832623703075744517 3874387093616944326702097)
            ·
              refine ⟨2905790320212708245026573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874387093616944326702097 2905790320212708245026573)
              ·
                refine ⟨1089671370079765591884965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905790320212708245026573 1089671370079765591884965)
                ·
                  refine ⟨204313381889956048478431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089671370079765591884965 204313381889956048478431)
                  ·
                    rfl

theorem cell22_1790545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_1790545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790545 prefixEnd_1790545 := by exact prefixLift 1790545
  have htrace : WordTrace (prefixWord ++ tailWord_1790545) baseStart_1790545 baseEnd_1790545 := by
    simpa [prefixWord, tailWord_1790545, baseEnd_1790545] using wordTrace_append hprefix tailTrace_1790545
  have hstable : (prefixWord ++ tailWord_1790545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790545).length < 2 ^ (prefixWord ++ tailWord_1790545).sum := by decide
  have hdescent : baseEnd_1790545 < baseStart_1790545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790560 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_1790560 : Nat := 118140960795 + 1790560 * 2 ^ 59
def prefixEnd_1790560 : Nat := 4983230072969 + 3 ^ 40 * 1790560 * 2
def baseEnd_1790560 : Nat := 612945280476413106310247

theorem tailTrace_1790560 : CollatzResearch.WordTrace tailWord_1790560 prefixEnd_1790560 612945280476413106310247 := by
  unfold tailWord_1790560
  simp only [CollatzResearch.WordTrace]
  refine ⟨32653544196557199073432567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43538058928742932097910089 32653544196557199073432567)
  ·
    refine ⟨48980316294835798610148851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32653544196557199073432567 48980316294835798610148851)
    ·
      refine ⟨73470474442253697915223277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48980316294835798610148851 73470474442253697915223277)
      ·
        refine ⟨27551427915845136718208729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73470474442253697915223277 27551427915845136718208729)
        ·
          refine ⟨20663570936883852538656547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27551427915845136718208729 20663570936883852538656547)
          ·
            refine ⟨30995356405325778807984821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20663570936883852538656547 30995356405325778807984821)
            ·
              refine ⟨2905814662999291763248577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30995356405325778807984821 2905814662999291763248577)
              ·
                refine ⟨2179360997249468822436433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905814662999291763248577 2179360997249468822436433)
                ·
                  refine ⟨1634520747937101616827325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2179360997249468822436433 1634520747937101616827325)
                  ·
                    refine ⟨612945280476413106310247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634520747937101616827325 612945280476413106310247)
                    ·
                      rfl

theorem cell22_1790560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_1790560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790560 prefixEnd_1790560 := by exact prefixLift 1790560
  have htrace : WordTrace (prefixWord ++ tailWord_1790560) baseStart_1790560 baseEnd_1790560 := by
    simpa [prefixWord, tailWord_1790560, baseEnd_1790560] using wordTrace_append hprefix tailTrace_1790560
  have hstable : (prefixWord ++ tailWord_1790560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790560).length < 2 ^ (prefixWord ++ tailWord_1790560).sum := by decide
  have hdescent : baseEnd_1790560 < baseStart_1790560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790562 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1790562 : Nat := 118140960795 + 1790562 * 2 ^ 59
def prefixEnd_1790562 : Nat := 4983230072969 + 3 ^ 40 * 1790562 * 2
def baseEnd_1790562 : Nat := 204315321705761922586747

theorem tailTrace_1790562 : CollatzResearch.WordTrace tailWord_1790562 prefixEnd_1790562 204315321705761922586747 := by
  unfold tailWord_1790562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16326790334776788122109485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43538107559404768325625293 16326790334776788122109485)
  ·
    refine ⟨6122546375541295545791057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16326790334776788122109485 6122546375541295545791057)
    ·
      refine ⟨4591909781655971659343293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6122546375541295545791057 4591909781655971659343293)
      ·
        refine ⟨1721966168120989372253735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4591909781655971659343293 1721966168120989372253735)
        ·
          refine ⟨2582949252181484058380603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721966168120989372253735 2582949252181484058380603)
          ·
            refine ⟨3874423878272226087570905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582949252181484058380603 3874423878272226087570905)
            ·
              refine ⟨2905817908704169565678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874423878272226087570905 2905817908704169565678179)
              ·
                refine ⟨4358726863056254348517269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905817908704169565678179 4358726863056254348517269)
                ·
                  refine ⟨204315321705761922586747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4358726863056254348517269 204315321705761922586747)
                  ·
                    rfl

theorem cell22_1790562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1790562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790562 prefixEnd_1790562 := by exact prefixLift 1790562
  have htrace : WordTrace (prefixWord ++ tailWord_1790562) baseStart_1790562 baseEnd_1790562 := by
    simpa [prefixWord, tailWord_1790562, baseEnd_1790562] using wordTrace_append hprefix tailTrace_1790562
  have hstable : (prefixWord ++ tailWord_1790562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790562).length < 2 ^ (prefixWord ++ tailWord_1790562).sum := by decide
  have hdescent : baseEnd_1790562 < baseStart_1790562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790586 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1790586 : Nat := 118140960795 + 1790586 * 2 ^ 59
def prefixEnd_1790586 : Nat := 4983230072969 + 3 ^ 40 * 1790586 * 2
def baseEnd_1790586 : Nat := 612954180807757705160167

theorem tailTrace_1790586 : CollatzResearch.WordTrace tailWord_1790586 prefixEnd_1790586 612954180807757705160167 := by
  unfold tailWord_1790586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327009172755051146827903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43538691127346803058207741 16327009172755051146827903)
  ·
    refine ⟨24490513759132576720241855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16327009172755051146827903 24490513759132576720241855)
    ·
      refine ⟨36735770638698865080362783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24490513759132576720241855 36735770638698865080362783)
      ·
        refine ⟨55103655958048297620544175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36735770638698865080362783 55103655958048297620544175)
        ·
          refine ⟨82655483937072446430816263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55103655958048297620544175 82655483937072446430816263)
          ·
            refine ⟨123983225905608669646224395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82655483937072446430816263 123983225905608669646224395)
            ·
              refine ⟨185974838858413004469336593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123983225905608669646224395 185974838858413004469336593)
              ·
                refine ⟨139481129143809753352002445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185974838858413004469336593 139481129143809753352002445)
                ·
                  refine ⟨52305423428928657507000917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139481129143809753352002445 52305423428928657507000917)
                  ·
                    refine ⟨612954180807757705160167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52305423428928657507000917 612954180807757705160167)
                    ·
                      rfl

theorem cell22_1790586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1790586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790586 prefixEnd_1790586 := by exact prefixLift 1790586
  have htrace : WordTrace (prefixWord ++ tailWord_1790586) baseStart_1790586 baseEnd_1790586 := by
    simpa [prefixWord, tailWord_1790586, baseEnd_1790586] using wordTrace_append hprefix tailTrace_1790586
  have hstable : (prefixWord ++ tailWord_1790586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790586).length < 2 ^ (prefixWord ++ tailWord_1790586).sum := by decide
  have hdescent : baseEnd_1790586 < baseStart_1790586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790669 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1790669 : Nat := 118140960795 + 1790669 * 2 ^ 59
def prefixEnd_1790669 : Nat := 4983230072969 + 3 ^ 40 * 1790669 * 2
def baseEnd_1790669 : Nat := 204327531134657718444971

theorem tailTrace_1790669 : CollatzResearch.WordTrace tailWord_1790669 prefixEnd_1790669 204327531134657718444971 := by
  unfold tailWord_1790669
  simp only [CollatzResearch.WordTrace]
  refine ⟨65311063949719509762583061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43540709299813006508388707 65311063949719509762583061)
  ·
    refine ⟨3061456122643102020121081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65311063949719509762583061 3061456122643102020121081)
    ·
      refine ⟨2296092091982326515090811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3061456122643102020121081 2296092091982326515090811)
      ·
        refine ⟨3444138137973489772636217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296092091982326515090811 3444138137973489772636217)
        ·
          refine ⟨2583103603480117329477163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444138137973489772636217 2583103603480117329477163)
          ·
            refine ⟨3874655405220175994215745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583103603480117329477163 3874655405220175994215745)
            ·
              refine ⟨2905991553915131995661809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874655405220175994215745 2905991553915131995661809)
              ·
                refine ⟨2179493665436348996746357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905991553915131995661809 2179493665436348996746357)
                ·
                  refine ⟨204327531134657718444971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179493665436348996746357 204327531134657718444971)
                  ·
                    rfl

theorem cell22_1790669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1790669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790669 prefixEnd_1790669 := by exact prefixLift 1790669
  have htrace : WordTrace (prefixWord ++ tailWord_1790669) baseStart_1790669 baseEnd_1790669 := by
    simpa [prefixWord, tailWord_1790669, baseEnd_1790669] using wordTrace_append hprefix tailTrace_1790669
  have hstable : (prefixWord ++ tailWord_1790669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790669).length < 2 ^ (prefixWord ++ tailWord_1790669).sum := by decide
  have hdescent : baseEnd_1790669 < baseStart_1790669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790710 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1790710 : Nat := 118140960795 + 1790710 * 2 ^ 59
def prefixEnd_1790710 : Nat := 4983230072969 + 3 ^ 40 * 1790710 * 2
def baseEnd_1790710 : Nat := 612996628541862715059787

theorem tailTrace_1790710 : CollatzResearch.WordTrace tailWord_1790710 prefixEnd_1790710 612996628541862715059787 := by
  unfold tailWord_1790710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082034958910685860301599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43541706228380649176550389 4082034958910685860301599)
  ·
    refine ⟨6123052438366028790452399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082034958910685860301599 6123052438366028790452399)
    ·
      refine ⟨9184578657549043185678599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6123052438366028790452399 9184578657549043185678599)
      ·
        refine ⟨13776867986323564778517899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184578657549043185678599 13776867986323564778517899)
        ·
          refine ⟨20665301979485347167776849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13776867986323564778517899 20665301979485347167776849)
          ·
            refine ⟨15498976484614010375832637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20665301979485347167776849 15498976484614010375832637)
            ·
              refine ⟨5812116181730253890937239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15498976484614010375832637 5812116181730253890937239)
              ·
                refine ⟨8718174272595380836405859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812116181730253890937239 8718174272595380836405859)
                ·
                  refine ⟨13077261408893071254608789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718174272595380836405859 13077261408893071254608789)
                  ·
                    refine ⟨612996628541862715059787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13077261408893071254608789 612996628541862715059787)
                    ·
                      rfl

theorem cell22_1790710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1790710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790710 prefixEnd_1790710 := by exact prefixLift 1790710
  have htrace : WordTrace (prefixWord ++ tailWord_1790710) baseStart_1790710 baseEnd_1790710 := by
    simpa [prefixWord, tailWord_1790710, baseEnd_1790710] using wordTrace_append hprefix tailTrace_1790710
  have hstable : (prefixWord ++ tailWord_1790710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790710).length < 2 ^ (prefixWord ++ tailWord_1790710).sum := by decide
  have hdescent : baseEnd_1790710 < baseStart_1790710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790768 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_1790768 : Nat := 118140960795 + 1790768 * 2 ^ 59
def prefixEnd_1790768 : Nat := 4983230072969 + 3 ^ 40 * 1790768 * 2
def baseEnd_1790768 : Nat := 613016483127169897109609

theorem tailTrace_1790768 : CollatzResearch.WordTrace tailWord_1790768 prefixEnd_1790768 613016483127169897109609 := by
  unfold tailWord_1790768
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657337388180424835218479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43543116517573899780291305 32657337388180424835218479)
  ·
    refine ⟨48986006082270637252827719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32657337388180424835218479 48986006082270637252827719)
    ·
      refine ⟨73479009123405955879241579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48986006082270637252827719 73479009123405955879241579)
      ·
        refine ⟨110218513685108933818862369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73479009123405955879241579 110218513685108933818862369)
        ·
          refine ⟨82663885263831700364146777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110218513685108933818862369 82663885263831700364146777)
          ·
            refine ⟨61997913947873775273110083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82663885263831700364146777 61997913947873775273110083)
            ·
              refine ⟨92996870921810662909665125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61997913947873775273110083 92996870921810662909665125)
              ·
                refine ⟨17436913297839499295562211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92996870921810662909665125 17436913297839499295562211)
                ·
                  refine ⟨26155369946759248943343317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17436913297839499295562211 26155369946759248943343317)
                  ·
                    refine ⟨613016483127169897109609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26155369946759248943343317 613016483127169897109609)
                    ·
                      rfl

theorem cell22_1790768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_1790768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790768 prefixEnd_1790768 := by exact prefixLift 1790768
  have htrace : WordTrace (prefixWord ++ tailWord_1790768) baseStart_1790768 baseEnd_1790768 := by
    simpa [prefixWord, tailWord_1790768, baseEnd_1790768] using wordTrace_append hprefix tailTrace_1790768
  have hstable : (prefixWord ++ tailWord_1790768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790768).length < 2 ^ (prefixWord ++ tailWord_1790768).sum := by decide
  have hdescent : baseEnd_1790768 < baseStart_1790768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790847 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 2, 3]
def baseStart_1790847 : Nat := 118140960795 + 1790847 * 2 ^ 59
def prefixEnd_1790847 : Nat := 4983230072969 + 3 ^ 40 * 1790847 * 2
def baseEnd_1790847 : Nat := 613043526441640024384367

theorem tailTrace_1790847 : CollatzResearch.WordTrace tailWord_1790847 prefixEnd_1790847 613043526441640024384367 := by
  unfold tailWord_1790847
  simp only [CollatzResearch.WordTrace]
  refine ⟨65317556143074646162562795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43545037428716430775041863 65317556143074646162562795)
  ·
    refine ⟨97976334214611969243844193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65317556143074646162562795 97976334214611969243844193)
    ·
      refine ⟨73482250660958976932883145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97976334214611969243844193 73482250660958976932883145)
      ·
        refine ⟨55111687995719232699662359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73482250660958976932883145 55111687995719232699662359)
        ·
          refine ⟨82667531993578849049493539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55111687995719232699662359 82667531993578849049493539)
          ·
            refine ⟨124001297990368273574240309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82667531993578849049493539 124001297990368273574240309)
            ·
              refine ⟨11625121686597025647585029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124001297990368273574240309 11625121686597025647585029)
              ·
                refine ⟨2179710316236942308922193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11625121686597025647585029 2179710316236942308922193)
                ·
                  refine ⟨1634782737177706731691645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2179710316236942308922193 1634782737177706731691645)
                  ·
                    refine ⟨613043526441640024384367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634782737177706731691645 613043526441640024384367)
                    ·
                      rfl

theorem cell22_1790847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_1790847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790847 prefixEnd_1790847 := by exact prefixLift 1790847
  have htrace : WordTrace (prefixWord ++ tailWord_1790847) baseStart_1790847 baseEnd_1790847 := by
    simpa [prefixWord, tailWord_1790847, baseEnd_1790847] using wordTrace_append hprefix tailTrace_1790847
  have hstable : (prefixWord ++ tailWord_1790847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790847).length < 2 ^ (prefixWord ++ tailWord_1790847).sum := by decide
  have hdescent : baseEnd_1790847 < baseStart_1790847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790860 : List Nat := [2, 2, 1, 2, 1, 2, 5, 7]
def baseStart_1790860 : Nat := 118140960795 + 1790860 * 2 ^ 59
def prefixEnd_1790860 : Nat := 4983230072969 + 3 ^ 40 * 1790860 * 2
def baseEnd_1790860 : Nat := 68116441845256924867703

theorem tailTrace_1790860 : CollatzResearch.WordTrace tailWord_1790860 prefixEnd_1790860 68116441845256924867703 := by
  unfold tailWord_1790860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32659015146013774691393017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43545353528018366255190689 32659015146013774691393017)
  ·
    refine ⟨24494261359510331018544763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32659015146013774691393017 24494261359510331018544763)
    ·
      refine ⟨36741392039265496527817145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24494261359510331018544763 36741392039265496527817145)
      ·
        refine ⟨27556044029449122395862859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36741392039265496527817145 27556044029449122395862859)
        ·
          refine ⟨41334066044173683593794289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27556044029449122395862859 41334066044173683593794289)
          ·
            refine ⟨31000549533130262695345717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41334066044173683593794289 31000549533130262695345717)
            ·
              refine ⟨2906301518730962127688661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31000549533130262695345717 2906301518730962127688661)
              ·
                refine ⟨68116441845256924867703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2906301518730962127688661 68116441845256924867703)
                ·
                  rfl

theorem cell22_1790860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_1790860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790860 prefixEnd_1790860 := by exact prefixLift 1790860
  have htrace : WordTrace (prefixWord ++ tailWord_1790860) baseStart_1790860 baseEnd_1790860 := by
    simpa [prefixWord, tailWord_1790860, baseEnd_1790860] using wordTrace_append hprefix tailTrace_1790860
  have hstable : (prefixWord ++ tailWord_1790860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790860).length < 2 ^ (prefixWord ++ tailWord_1790860).sum := by decide
  have hdescent : baseEnd_1790860 < baseStart_1790860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790877 : List Nat := [1, 4, 2, 1, 2, 1, 5, 6]
def baseStart_1790877 : Nat := 118140960795 + 1790877 * 2 ^ 59
def prefixEnd_1790877 : Nat := 4983230072969 + 3 ^ 40 * 1790877 * 2
def baseEnd_1790877 : Nat := 68117088450525549570475

theorem tailTrace_1790877 : CollatzResearch.WordTrace tailWord_1790877 prefixEnd_1790877 68117088450525549570475 := by
  unfold tailWord_1790877
  simp only [CollatzResearch.WordTrace]
  refine ⟨65318650332965961286154885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43545766888643974190769923 65318650332965961286154885)
  ·
    refine ⟨12247246937431117741154041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65318650332965961286154885 12247246937431117741154041)
    ·
      refine ⟨9185435203073338305865531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12247246937431117741154041 9185435203073338305865531)
      ·
        refine ⟨13778152804610007458798297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9185435203073338305865531 13778152804610007458798297)
        ·
          refine ⟨10333614603457505594098723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13778152804610007458798297 10333614603457505594098723)
          ·
            refine ⟨15500421905186258391148085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333614603457505594098723 15500421905186258391148085)
            ·
              refine ⟨1453164553611211724170133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15500421905186258391148085 1453164553611211724170133)
              ·
                refine ⟨68117088450525549570475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1453164553611211724170133 68117088450525549570475)
                ·
                  rfl

theorem cell22_1790877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 6].length) (baseStart_1790877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790877 prefixEnd_1790877 := by exact prefixLift 1790877
  have htrace : WordTrace (prefixWord ++ tailWord_1790877) baseStart_1790877 baseEnd_1790877 := by
    simpa [prefixWord, tailWord_1790877, baseEnd_1790877] using wordTrace_append hprefix tailTrace_1790877
  have hstable : (prefixWord ++ tailWord_1790877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790877).length < 2 ^ (prefixWord ++ tailWord_1790877).sum := by decide
  have hdescent : baseEnd_1790877 < baseStart_1790877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790879 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 2, 4]
def baseStart_1790879 : Nat := 118140960795 + 1790879 * 2 ^ 59
def prefixEnd_1790879 : Nat := 4983230072969 + 3 ^ 40 * 1790879 * 2
def baseEnd_1790879 : Nat := 613054480695602607584269

theorem tailTrace_1790879 : CollatzResearch.WordTrace tailWord_1790879 prefixEnd_1790879 613054480695602607584269 := by
  unfold tailWord_1790879
  simp only [CollatzResearch.WordTrace]
  refine ⟨65318723278958715627727691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43545815519305810418485127 65318723278958715627727691)
  ·
    refine ⟨97978084918438073441591537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65318723278958715627727691 97978084918438073441591537)
    ·
      refine ⟨73483563688828555081193653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97978084918438073441591537 73483563688828555081193653)
      ·
        refine ⟨6889084095827677038861905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73483563688828555081193653 6889084095827677038861905)
        ·
          refine ⟨5166813071870757779146429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889084095827677038861905 5166813071870757779146429)
          ·
            refine ⟨1937554901951534167179911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5166813071870757779146429 1937554901951534167179911)
            ·
              refine ⟨2906332352927301250769867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937554901951534167179911 2906332352927301250769867)
              ·
                refine ⟨4359498529390951876154801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906332352927301250769867 4359498529390951876154801)
                ·
                  refine ⟨3269623897043213907116101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359498529390951876154801 3269623897043213907116101)
                  ·
                    refine ⟨613054480695602607584269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269623897043213907116101 613054480695602607584269)
                    ·
                      rfl

theorem cell22_1790879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_1790879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790879 prefixEnd_1790879 := by exact prefixLift 1790879
  have htrace : WordTrace (prefixWord ++ tailWord_1790879) baseStart_1790879 baseEnd_1790879 := by
    simpa [prefixWord, tailWord_1790879, baseEnd_1790879] using wordTrace_append hprefix tailTrace_1790879
  have hstable : (prefixWord ++ tailWord_1790879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790879).length < 2 ^ (prefixWord ++ tailWord_1790879).sum := by decide
  have hdescent : baseEnd_1790879 < baseStart_1790879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790943 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 1, 3]
def baseStart_1790943 : Nat := 118140960795 + 1790943 * 2 ^ 59
def prefixEnd_1790943 : Nat := 4983230072969 + 3 ^ 40 * 1790943 * 2
def baseEnd_1790943 : Nat := 613076389203527773984073

theorem tailTrace_1790943 : CollatzResearch.WordTrace tailWord_1790943 prefixEnd_1790943 613076389203527773984073 := by
  unfold tailWord_1790943
  simp only [CollatzResearch.WordTrace]
  refine ⟨65321057550726854558057483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43547371700484569705371655 65321057550726854558057483)
  ·
    refine ⟨97981586326090281837086225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65321057550726854558057483 97981586326090281837086225)
    ·
      refine ⟨73486189744567711377814669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97981586326090281837086225 73486189744567711377814669)
      ·
        refine ⟨27557321154212891766680501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73486189744567711377814669 27557321154212891766680501)
        ·
          refine ⟨2583498858207458603126297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27557321154212891766680501 2583498858207458603126297)
          ·
            refine ⟨1937624143655593952344723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583498858207458603126297 1937624143655593952344723)
            ·
              refine ⟨2906436215483390928517085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937624143655593952344723 2906436215483390928517085)
              ·
                refine ⟨1089913580806271598193907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2906436215483390928517085 1089913580806271598193907)
                ·
                  refine ⟨1634870371209407397290861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089913580806271598193907 1634870371209407397290861)
                  ·
                    refine ⟨613076389203527773984073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634870371209407397290861 613076389203527773984073)
                    ·
                      rfl

theorem cell22_1790943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_1790943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790943 prefixEnd_1790943 := by exact prefixLift 1790943
  have htrace : WordTrace (prefixWord ++ tailWord_1790943) baseStart_1790943 baseEnd_1790943 := by
    simpa [prefixWord, tailWord_1790943, baseEnd_1790943] using wordTrace_append hprefix tailTrace_1790943
  have hstable : (prefixWord ++ tailWord_1790943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790943).length < 2 ^ (prefixWord ++ tailWord_1790943).sum := by decide
  have hdescent : baseEnd_1790943 < baseStart_1790943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790986 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1790986 : Nat := 118140960795 + 1790986 * 2 ^ 59
def prefixEnd_1790986 : Nat := 4983230072969 + 3 ^ 40 * 1790986 * 2
def baseEnd_1790986 : Nat := 613091108982289995158941

theorem tailTrace_1790986 : CollatzResearch.WordTrace tailWord_1790986 prefixEnd_1790986 613091108982289995158941 := by
  unfold tailWord_1790986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330656472392768225468203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43548417259714048601248541 16330656472392768225468203)
  ·
    refine ⟨24495984708589152338202305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16330656472392768225468203 24495984708589152338202305)
    ·
      refine ⟨18371988531441864253651729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24495984708589152338202305 18371988531441864253651729)
      ·
        refine ⟨13778991398581398190238797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18371988531441864253651729 13778991398581398190238797)
        ·
          refine ⟨5167121774468024321339549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13778991398581398190238797 5167121774468024321339549)
          ·
            refine ⟨1937670665425509120502331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5167121774468024321339549 1937670665425509120502331)
            ·
              refine ⟨2906505998138263680753497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937670665425509120502331 2906505998138263680753497)
              ·
                refine ⟨2179879498603697760565123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906505998138263680753497 2179879498603697760565123)
                ·
                  refine ⟨3269819247905546640847685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179879498603697760565123 3269819247905546640847685)
                  ·
                    refine ⟨613091108982289995158941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3269819247905546640847685 613091108982289995158941)
                    ·
                      rfl

theorem cell22_1790986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1790986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790986 prefixEnd_1790986 := by exact prefixLift 1790986
  have htrace : WordTrace (prefixWord ++ tailWord_1790986) baseStart_1790986 baseEnd_1790986 := by
    simpa [prefixWord, tailWord_1790986, baseEnd_1790986] using wordTrace_append hprefix tailTrace_1790986
  have hstable : (prefixWord ++ tailWord_1790986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790986).length < 2 ^ (prefixWord ++ tailWord_1790986).sum := by decide
  have hdescent : baseEnd_1790986 < baseStart_1790986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1790999 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1790999 : Nat := 118140960795 + 1790999 * 2 ^ 59
def prefixEnd_1790999 : Nat := 4983230072969 + 3 ^ 40 * 1790999 * 2
def baseEnd_1790999 : Nat := 613095559147962294583901

theorem tailTrace_1790999 : CollatzResearch.WordTrace tailWord_1790999 prefixEnd_1790999 613095559147962294583901 := by
  unfold tailWord_1790999
  simp only [CollatzResearch.WordTrace]
  refine ⟨65323100038523976122096051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43548733359015984081397367 65323100038523976122096051)
  ·
    refine ⟨97984650057785964183144077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65323100038523976122096051 97984650057785964183144077)
    ·
      refine ⟨36744243771669736568679029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97984650057785964183144077 36744243771669736568679029)
      ·
        refine ⟨3444772853594037803313659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36744243771669736568679029 3444772853594037803313659)
        ·
          refine ⟨5167159280391056704970489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444772853594037803313659 5167159280391056704970489)
          ·
            refine ⟨3875369460293292528727867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167159280391056704970489 3875369460293292528727867)
            ·
              refine ⟨5813054190439938793091801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875369460293292528727867 5813054190439938793091801)
              ·
                refine ⟨4359790642829954094818851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813054190439938793091801 4359790642829954094818851)
                ·
                  refine ⟨6539685964244931142228277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359790642829954094818851 6539685964244931142228277)
                  ·
                    refine ⟨613095559147962294583901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6539685964244931142228277 613095559147962294583901)
                    ·
                      rfl

theorem cell22_1790999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1790999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1790999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1790999 prefixEnd_1790999 := by exact prefixLift 1790999
  have htrace : WordTrace (prefixWord ++ tailWord_1790999) baseStart_1790999 baseEnd_1790999 := by
    simpa [prefixWord, tailWord_1790999, baseEnd_1790999] using wordTrace_append hprefix tailTrace_1790999
  have hstable : (prefixWord ++ tailWord_1790999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1790999).length < 2 ^ (prefixWord ++ tailWord_1790999).sum := by decide
  have hdescent : baseEnd_1790999 < baseStart_1790999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1790999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791012 : List Nat := [2, 3, 1, 4, 1, 11]
def baseStart_1791012 : Nat := 118140960795 + 1791012 * 2 ^ 59
def prefixEnd_1791012 : Nat := 4983230072969 + 3 ^ 40 * 1791012 * 2
def baseEnd_1791012 : Nat := 7569135917452278938381

theorem tailTrace_1791012 : CollatzResearch.WordTrace tailWord_1791012 prefixEnd_1791012 7569135917452278938381 := by
  unfold tailWord_1791012
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661787093738439671159645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43549049458317919561546193 32661787093738439671159645)
  ·
    refine ⟨12248170160151914876684867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32661787093738439671159645 12248170160151914876684867)
    ·
      refine ⟨18372255240227872315027301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12248170160151914876684867 18372255240227872315027301)
      ·
        refine ⟨3444797857542726059067619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18372255240227872315027301 3444797857542726059067619)
        ·
          refine ⟨5167196786314089088601429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444797857542726059067619 5167196786314089088601429)
          ·
            refine ⟨7569135917452278938381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5167196786314089088601429 7569135917452278938381)
            ·
              rfl

theorem cell22_1791012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 11].length) (baseStart_1791012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791012 prefixEnd_1791012 := by exact prefixLift 1791012
  have htrace : WordTrace (prefixWord ++ tailWord_1791012) baseStart_1791012 baseEnd_1791012 := by
    simpa [prefixWord, tailWord_1791012, baseEnd_1791012] using wordTrace_append hprefix tailTrace_1791012
  have hstable : (prefixWord ++ tailWord_1791012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791012).length < 2 ^ (prefixWord ++ tailWord_1791012).sum := by decide
  have hdescent : baseEnd_1791012 < baseStart_1791012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791072 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_1791072 : Nat := 118140960795 + 1791072 * 2 ^ 59
def prefixEnd_1791072 : Nat := 4983230072969 + 3 ^ 40 * 1791072 * 2
def baseEnd_1791072 : Nat := 613120548539814437508677

theorem tailTrace_1791072 : CollatzResearch.WordTrace tailWord_1791072 prefixEnd_1791072 613120548539814437508677 := by
  unfold tailWord_1791072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662881283629754794751735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43550508378173006393002313 32662881283629754794751735)
  ·
    refine ⟨48994321925444632192127603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32662881283629754794751735 48994321925444632192127603)
    ·
      refine ⟨73491482888166948288191405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48994321925444632192127603 73491482888166948288191405)
      ·
        refine ⟨27559306083062605608071777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73491482888166948288191405 27559306083062605608071777)
        ·
          refine ⟨20669479562296954206053833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27559306083062605608071777 20669479562296954206053833)
          ·
            refine ⟨15502109671722715654540375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20669479562296954206053833 15502109671722715654540375)
            ·
              refine ⟨23253164507584073481810563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15502109671722715654540375 23253164507584073481810563)
              ·
                refine ⟨34879746761376110222715845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23253164507584073481810563 34879746761376110222715845)
                ·
                  refine ⟨6539952517758020666759221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34879746761376110222715845 6539952517758020666759221)
                  ·
                    refine ⟨613120548539814437508677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6539952517758020666759221 613120548539814437508677)
                    ·
                      rfl

theorem cell22_1791072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_1791072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791072 prefixEnd_1791072 := by exact prefixLift 1791072
  have htrace : WordTrace (prefixWord ++ tailWord_1791072) baseStart_1791072 baseEnd_1791072 := by
    simpa [prefixWord, tailWord_1791072, baseEnd_1791072] using wordTrace_append hprefix tailTrace_1791072
  have hstable : (prefixWord ++ tailWord_1791072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791072).length < 2 ^ (prefixWord ++ tailWord_1791072).sum := by decide
  have hdescent : baseEnd_1791072 < baseStart_1791072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791104 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_1791104 : Nat := 118140960795 + 1791104 * 2 ^ 59
def prefixEnd_1791104 : Nat := 4983230072969 + 3 ^ 40 * 1791104 * 2
def baseEnd_1791104 : Nat := 613131502793777020708579

theorem tailTrace_1791104 : CollatzResearch.WordTrace tailWord_1791104 prefixEnd_1791104 613131502793777020708579 := by
  unfold tailWord_1791104
  simp only [CollatzResearch.WordTrace]
  refine ⟨32663464851571789527334183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43551286468762386036445577 32663464851571789527334183)
  ·
    refine ⟨48995197277357684291001275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32663464851571789527334183 48995197277357684291001275)
    ·
      refine ⟨73492795916036526436501913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48995197277357684291001275 73492795916036526436501913)
      ·
        refine ⟨55119596937027394827376435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73492795916036526436501913 55119596937027394827376435)
        ·
          refine ⟨82679395405541092241064653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55119596937027394827376435 82679395405541092241064653)
          ·
            refine ⟨31004773277077909590399245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82679395405541092241064653 31004773277077909590399245)
            ·
              refine ⟨11626789978904216096399717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31004773277077909590399245 11626789978904216096399717)
              ·
                refine ⟨2180023121044540518074947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11626789978904216096399717 2180023121044540518074947)
                ·
                  refine ⟨3270034681566810777112421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180023121044540518074947 3270034681566810777112421)
                  ·
                    refine ⟨613131502793777020708579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270034681566810777112421 613131502793777020708579)
                    ·
                      rfl

theorem cell22_1791104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_1791104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791104 prefixEnd_1791104 := by exact prefixLift 1791104
  have htrace : WordTrace (prefixWord ++ tailWord_1791104) baseStart_1791104 baseEnd_1791104 := by
    simpa [prefixWord, tailWord_1791104, baseEnd_1791104] using wordTrace_append hprefix tailTrace_1791104
  have hstable : (prefixWord ++ tailWord_1791104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791104).length < 2 ^ (prefixWord ++ tailWord_1791104).sum := by decide
  have hdescent : baseEnd_1791104 < baseStart_1791104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791112 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 1, 3]
def baseStart_1791112 : Nat := 118140960795 + 1791112 * 2 ^ 59
def prefixEnd_1791112 : Nat := 4983230072969 + 3 ^ 40 * 1791112 * 2
def baseEnd_1791112 : Nat := 613134241357267666508555

theorem tailTrace_1791112 : CollatzResearch.WordTrace tailWord_1791112 prefixEnd_1791112 613134241357267666508555 := by
  unfold tailWord_1791112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32663610743557298210479795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43551480991409730947306393 32663610743557298210479795)
  ·
    refine ⟨48995416115335947315719693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32663610743557298210479795 48995416115335947315719693)
    ·
      refine ⟨18373281043250980243394885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48995416115335947315719693 18373281043250980243394885)
      ·
        refine ⟨3444990195609558795636541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18373281043250980243394885 3444990195609558795636541)
        ·
          refine ⟨1291871323353584548363703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3444990195609558795636541 1291871323353584548363703)
          ·
            refine ⟨1937806985030376822545555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291871323353584548363703 1937806985030376822545555)
            ·
              refine ⟨2906710477545565233818333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937806985030376822545555 2906710477545565233818333)
              ·
                refine ⟨1090016429079586962681875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2906710477545565233818333 1090016429079586962681875)
                ·
                  refine ⟨1635024643619380444022813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090016429079586962681875 1635024643619380444022813)
                  ·
                    refine ⟨613134241357267666508555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635024643619380444022813 613134241357267666508555)
                    ·
                      rfl

theorem cell22_1791112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_1791112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791112 prefixEnd_1791112 := by exact prefixLift 1791112
  have htrace : WordTrace (prefixWord ++ tailWord_1791112) baseStart_1791112 baseEnd_1791112 := by
    simpa [prefixWord, tailWord_1791112, baseEnd_1791112] using wordTrace_append hprefix tailTrace_1791112
  have hstable : (prefixWord ++ tailWord_1791112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791112).length < 2 ^ (prefixWord ++ tailWord_1791112).sum := by decide
  have hdescent : baseEnd_1791112 < baseStart_1791112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791164 : List Nat := [2, 2, 2, 3, 2, 1, 2, 8]
def baseStart_1791164 : Nat := 118140960795 + 1791164 * 2 ^ 59
def prefixEnd_1791164 : Nat := 4983230072969 + 3 ^ 40 * 1791164 * 2
def baseEnd_1791164 : Nat := 68128004668884096023155

theorem tailTrace_1791164 : CollatzResearch.WordTrace tailWord_1791164 prefixEnd_1791164 68128004668884096023155 := by
  unfold tailWord_1791164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32664559041463104650926273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43552745388617472867901697 32664559041463104650926273)
  ·
    refine ⟨24498419281097328488194705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32664559041463104650926273 24498419281097328488194705)
    ·
      refine ⟨18373814460822996366146029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24498419281097328488194705 18373814460822996366146029)
      ·
        refine ⟨6890180422808623637304761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18373814460822996366146029 6890180422808623637304761)
        ·
          refine ⟨5167635317106467727978571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890180422808623637304761 5167635317106467727978571)
          ·
            refine ⟨7751452975659701591967857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167635317106467727978571 7751452975659701591967857)
            ·
              refine ⟨5813589731744776193975893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7751452975659701591967857 5813589731744776193975893)
              ·
                refine ⟨68128004668884096023155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5813589731744776193975893 68128004668884096023155)
                ·
                  rfl

theorem cell22_1791164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_1791164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791164 prefixEnd_1791164 := by exact prefixLift 1791164
  have htrace : WordTrace (prefixWord ++ tailWord_1791164) baseStart_1791164 baseEnd_1791164 := by
    simpa [prefixWord, tailWord_1791164, baseEnd_1791164] using wordTrace_append hprefix tailTrace_1791164
  have hstable : (prefixWord ++ tailWord_1791164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791164).length < 2 ^ (prefixWord ++ tailWord_1791164).sum := by decide
  have hdescent : baseEnd_1791164 < baseStart_1791164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791166 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1791166 : Nat := 118140960795 + 1791166 * 2 ^ 59
def prefixEnd_1791166 : Nat := 4983230072969 + 3 ^ 40 * 1791166 * 2
def baseEnd_1791166 : Nat := 613152726660829525658389

theorem tailTrace_1791166 : CollatzResearch.WordTrace tailWord_1791166 prefixEnd_1791166 613152726660829525658389 := by
  unfold tailWord_1791166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166148878614870455428169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43552794019279309095616901 8166148878614870455428169)
  ·
    refine ⟨6124611658961152841571127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8166148878614870455428169 6124611658961152841571127)
    ·
      refine ⟨9186917488441729262356691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124611658961152841571127 9186917488441729262356691)
      ·
        refine ⟨13780376232662593893535037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186917488441729262356691 13780376232662593893535037)
        ·
          refine ⟨5167641087248472710075639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13780376232662593893535037 5167641087248472710075639)
          ·
            refine ⟨7751461630872709065113459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167641087248472710075639 7751461630872709065113459)
            ·
              refine ⟨11627192446309063597670189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751461630872709065113459 11627192446309063597670189)
              ·
                refine ⟨4360197167365898849126321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11627192446309063597670189 4360197167365898849126321)
                ·
                  refine ⟨3270147875524424136844741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360197167365898849126321 3270147875524424136844741)
                  ·
                    refine ⟨613152726660829525658389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270147875524424136844741 613152726660829525658389)
                    ·
                      rfl

theorem cell22_1791166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1791166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791166 prefixEnd_1791166 := by exact prefixLift 1791166
  have htrace : WordTrace (prefixWord ++ tailWord_1791166) baseStart_1791166 baseEnd_1791166 := by
    simpa [prefixWord, tailWord_1791166, baseEnd_1791166] using wordTrace_append hprefix tailTrace_1791166
  have hstable : (prefixWord ++ tailWord_1791166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791166).length < 2 ^ (prefixWord ++ tailWord_1791166).sum := by decide
  have hdescent : baseEnd_1791166 < baseStart_1791166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791179 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 7, 3]
def baseStart_1791179 : Nat := 118140960795 + 1791179 * 2 ^ 59
def prefixEnd_1791179 : Nat := 4983230072969 + 3 ^ 40 * 1791179 * 2
def baseEnd_1791179 : Nat := 613157176826501825083349

theorem tailTrace_1791179 : CollatzResearch.WordTrace tailWord_1791179 prefixEnd_1791179 613157176826501825083349 := by
  unfold tailWord_1791179
  simp only [CollatzResearch.WordTrace]
  refine ⟨65329665177871866863648591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43553110118581244575765727 65329665177871866863648591)
  ·
    refine ⟨97994497766807800295472887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65329665177871866863648591 97994497766807800295472887)
    ·
      refine ⟨146991746650211700443209331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97994497766807800295472887 146991746650211700443209331)
      ·
        refine ⟨220487619975317550664813997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146991746650211700443209331 220487619975317550664813997)
        ·
          refine ⟨82682857490744081499305249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220487619975317550664813997 82682857490744081499305249)
          ·
            refine ⟨62012143118058061124478937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82682857490744081499305249 62012143118058061124478937)
            ·
              refine ⟨46509107338543545843359203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62012143118058061124478937 46509107338543545843359203)
              ·
                refine ⟨69763661007815318765038805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46509107338543545843359203 69763661007815318765038805)
                ·
                  refine ⟨1635085804870671533555597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 69763661007815318765038805 1635085804870671533555597)
                  ·
                    refine ⟨613157176826501825083349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635085804870671533555597 613157176826501825083349)
                    ·
                      rfl

theorem cell22_1791179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3].length) (baseStart_1791179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791179 prefixEnd_1791179 := by exact prefixLift 1791179
  have htrace : WordTrace (prefixWord ++ tailWord_1791179) baseStart_1791179 baseEnd_1791179 := by
    simpa [prefixWord, tailWord_1791179, baseEnd_1791179] using wordTrace_append hprefix tailTrace_1791179
  have hstable : (prefixWord ++ tailWord_1791179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791179).length < 2 ^ (prefixWord ++ tailWord_1791179).sum := by decide
  have hdescent : baseEnd_1791179 < baseStart_1791179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791181 : List Nat := [1, 6, 2, 2, 11]
def baseStart_1791181 : Nat := 118140960795 + 1791181 * 2 ^ 59
def prefixEnd_1791181 : Nat := 4983230072969 + 3 ^ 40 * 1791181 * 2
def baseEnd_1791181 : Nat := 2523283380524174841701

theorem tailTrace_1791181 : CollatzResearch.WordTrace tailWord_1791181 prefixEnd_1791181 2523283380524174841701 := by
  unfold tailWord_1791181
  simp only [CollatzResearch.WordTrace]
  refine ⟨65329738123864621205221397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43553158749243080803480931 65329738123864621205221397)
  ·
    refine ⟨3062331474556154118994753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65329738123864621205221397 3062331474556154118994753)
    ·
      refine ⟨2296748605917115589246065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3062331474556154118994753 2296748605917115589246065)
      ·
        refine ⟨1722561454437836691934549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296748605917115589246065 1722561454437836691934549)
        ·
          refine ⟨2523283380524174841701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1722561454437836691934549 2523283380524174841701)
          ·
            rfl

theorem cell22_1791181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 11].length) (baseStart_1791181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791181 prefixEnd_1791181 := by exact prefixLift 1791181
  have htrace : WordTrace (prefixWord ++ tailWord_1791181) baseStart_1791181 baseEnd_1791181 := by
    simpa [prefixWord, tailWord_1791181, baseEnd_1791181] using wordTrace_append hprefix tailTrace_1791181
  have hstable : (prefixWord ++ tailWord_1791181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791181).length < 2 ^ (prefixWord ++ tailWord_1791181).sum := by decide
  have hdescent : baseEnd_1791181 < baseStart_1791181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791213 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1791213 : Nat := 118140960795 + 1791213 * 2 ^ 59
def prefixEnd_1791213 : Nat := 4983230072969 + 3 ^ 40 * 1791213 * 2
def baseEnd_1791213 : Nat := 613168815721337069733245

theorem tailTrace_1791213 : CollatzResearch.WordTrace tailWord_1791213 prefixEnd_1791213 613168815721337069733245 := by
  unfold tailWord_1791213
  simp only [CollatzResearch.WordTrace]
  refine ⟨65330905259748690670386293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43553936839832460446924195 65330905259748690670386293)
  ·
    refine ⟨6124772368101439750348715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65330905259748690670386293 6124772368101439750348715)
    ·
      refine ⟨9187158552152159625523073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124772368101439750348715 9187158552152159625523073)
      ·
        refine ⟨6890368914114119719142305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9187158552152159625523073 6890368914114119719142305)
        ·
          refine ⟨5167776685585589789356729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890368914114119719142305 5167776685585589789356729)
          ·
            refine ⟨3875832514189192342017547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5167776685585589789356729 3875832514189192342017547)
            ·
              refine ⟨5813748771283788513026321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875832514189192342017547 5813748771283788513026321)
              ·
                refine ⟨4360311578462841384769741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813748771283788513026321 4360311578462841384769741)
                ·
                  refine ⟨1635116841923565519288653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4360311578462841384769741 1635116841923565519288653)
                  ·
                    refine ⟨613168815721337069733245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635116841923565519288653 613168815721337069733245)
                    ·
                      rfl

theorem cell22_1791213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1791213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791213 prefixEnd_1791213 := by exact prefixLift 1791213
  have htrace : WordTrace (prefixWord ++ tailWord_1791213) baseStart_1791213 baseEnd_1791213 := by
    simpa [prefixWord, tailWord_1791213, baseEnd_1791213] using wordTrace_append hprefix tailTrace_1791213
  have hstable : (prefixWord ++ tailWord_1791213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791213).length < 2 ^ (prefixWord ++ tailWord_1791213).sum := by decide
  have hdescent : baseEnd_1791213 < baseStart_1791213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791230 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1791230 : Nat := 118140960795 + 1791230 * 2 ^ 59
def prefixEnd_1791230 : Nat := 4983230072969 + 3 ^ 40 * 1791230 * 2
def baseEnd_1791230 : Nat := 613174635168754692058193

theorem tailTrace_1791230 : CollatzResearch.WordTrace tailWord_1791230 prefixEnd_1791230 613174635168754692058193 := by
  unfold tailWord_1791230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166440662585887821719393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43554350200458068382503429 8166440662585887821719393)
  ·
    refine ⟨6124830496939415866289545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8166440662585887821719393 6124830496939415866289545)
    ·
      refine ⟨4593622872704561899717159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6124830496939415866289545 4593622872704561899717159)
      ·
        refine ⟨6890434309056842849575739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593622872704561899717159 6890434309056842849575739)
        ·
          refine ⟨10335651463585264274363609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890434309056842849575739 10335651463585264274363609)
          ·
            refine ⟨7751738597688948205772707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10335651463585264274363609 7751738597688948205772707)
            ·
              refine ⟨11627607896533422308659061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751738597688948205772707 11627607896533422308659061)
              ·
                refine ⟨1090088240300008341436787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11627607896533422308659061 1090088240300008341436787)
                ·
                  refine ⟨1635132360450012512155181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090088240300008341436787 1635132360450012512155181)
                  ·
                    refine ⟨613174635168754692058193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635132360450012512155181 613174635168754692058193)
                    ·
                      rfl

theorem cell22_1791230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1791230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791230 prefixEnd_1791230 := by exact prefixLift 1791230
  have htrace : WordTrace (prefixWord ++ tailWord_1791230) baseStart_1791230 baseEnd_1791230 := by
    simpa [prefixWord, tailWord_1791230, baseEnd_1791230] using wordTrace_append hprefix tailTrace_1791230
  have hstable : (prefixWord ++ tailWord_1791230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791230).length < 2 ^ (prefixWord ++ tailWord_1791230).sum := by decide
  have hdescent : baseEnd_1791230 < baseStart_1791230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791316 : List Nat := [2, 4, 1, 1, 2, 1, 4, 7]
def baseStart_1791316 : Nat := 118140960795 + 1791316 * 2 ^ 59
def prefixEnd_1791316 : Nat := 4983230072969 + 3 ^ 40 * 1791316 * 2
def baseEnd_1791316 : Nat := 68133786080697681600881

theorem tailTrace_1791316 : CollatzResearch.WordTrace tailWord_1791316 prefixEnd_1791316 68133786080697681600881 := by
  unfold tailWord_1791316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32667330989187769630692901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43556441318917026174257201 32667330989187769630692901)
  ·
    refine ⟨6125124560472706805754919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32667330989187769630692901 6125124560472706805754919)
    ·
      refine ⟨9187686840709060208632379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125124560472706805754919 9187686840709060208632379)
      ·
        refine ⟨13781530261063590312948569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9187686840709060208632379 13781530261063590312948569)
        ·
          refine ⟨10336147695797692734711427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13781530261063590312948569 10336147695797692734711427)
          ·
            refine ⟨15504221543696539102067141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10336147695797692734711427 15504221543696539102067141)
            ·
              refine ⟨2907041539443101081637589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15504221543696539102067141 2907041539443101081637589)
              ·
                refine ⟨68133786080697681600881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2907041539443101081637589 68133786080697681600881)
                ·
                  rfl

theorem cell22_1791316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_1791316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791316 prefixEnd_1791316 := by exact prefixLift 1791316
  have htrace : WordTrace (prefixWord ++ tailWord_1791316) baseStart_1791316 baseEnd_1791316 := by
    simpa [prefixWord, tailWord_1791316, baseEnd_1791316] using wordTrace_append hprefix tailTrace_1791316
  have hstable : (prefixWord ++ tailWord_1791316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791316).length < 2 ^ (prefixWord ++ tailWord_1791316).sum := by decide
  have hdescent : baseEnd_1791316 < baseStart_1791316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791438 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1791438 : Nat := 118140960795 + 1791438 * 2 ^ 59
def prefixEnd_1791438 : Nat := 4983230072969 + 3 ^ 40 * 1791438 * 2
def baseEnd_1791438 : Nat := 613245837819511482857555

theorem tailTrace_1791438 : CollatzResearch.WordTrace tailWord_1791438 prefixEnd_1791438 613245837819511482857555 := by
  unfold tailWord_1791438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167388960491694262165871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43559407789289036064884645 8167388960491694262165871)
  ·
    refine ⟨12251083440737541393248807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167388960491694262165871 12251083440737541393248807)
    ·
      refine ⟨18376625161106312089873211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12251083440737541393248807 18376625161106312089873211)
      ·
        refine ⟨27564937741659468134809817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18376625161106312089873211 27564937741659468134809817)
        ·
          refine ⟨20673703306244601101107363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27564937741659468134809817 20673703306244601101107363)
          ·
            refine ⟨31010554959366901651661045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20673703306244601101107363 31010554959366901651661045)
            ·
              refine ⟨2907239527440647029843223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31010554959366901651661045 2907239527440647029843223)
              ·
                refine ⟨4360859291160970544764835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907239527440647029843223 4360859291160970544764835)
                ·
                  refine ⟨6541288936741455817147253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360859291160970544764835 6541288936741455817147253)
                  ·
                    refine ⟨613245837819511482857555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6541288936741455817147253 613245837819511482857555)
                    ·
                      rfl

theorem cell22_1791438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1791438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791438 prefixEnd_1791438 := by exact prefixLift 1791438
  have htrace : WordTrace (prefixWord ++ tailWord_1791438) baseStart_1791438 baseEnd_1791438 := by
    simpa [prefixWord, tailWord_1791438, baseEnd_1791438] using wordTrace_append hprefix tailTrace_1791438
  have hstable : (prefixWord ++ tailWord_1791438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791438).length < 2 ^ (prefixWord ++ tailWord_1791438).sum := by decide
  have hdescent : baseEnd_1791438 < baseStart_1791438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791453 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1791453 : Nat := 118140960795 + 1791453 * 2 ^ 59
def prefixEnd_1791453 : Nat := 4983230072969 + 3 ^ 40 * 1791453 * 2
def baseEnd_1791453 : Nat := 613250972626056443732509

theorem tailTrace_1791453 : CollatzResearch.WordTrace tailWord_1791453 prefixEnd_1791453 613250972626056443732509 := by
  unfold tailWord_1791453
  simp only [CollatzResearch.WordTrace]
  refine ⟨65339658778879211659123013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43559772519252807772748675 65339658778879211659123013)
  ·
    refine ⟨12251186021039852186085565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65339658778879211659123013 12251186021039852186085565)
    ·
      refine ⟨4594194757889944569782087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12251186021039852186085565 4594194757889944569782087)
      ·
        refine ⟨6891292136834916854673131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594194757889944569782087 6891292136834916854673131)
        ·
          refine ⟨10336938205252375282009697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891292136834916854673131 10336938205252375282009697)
          ·
            refine ⟨7752703653939281461507273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10336938205252375282009697 7752703653939281461507273)
            ·
              refine ⟨5814527740454461096130455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7752703653939281461507273 5814527740454461096130455)
              ·
                refine ⟨8721791610681691644195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814527740454461096130455 8721791610681691644195683)
                ·
                  refine ⟨13082687416022537466293525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8721791610681691644195683 13082687416022537466293525)
                  ·
                    refine ⟨613250972626056443732509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13082687416022537466293525 613250972626056443732509)
                    ·
                      rfl

theorem cell22_1791453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1791453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791453 prefixEnd_1791453 := by exact prefixLift 1791453
  have htrace : WordTrace (prefixWord ++ tailWord_1791453) baseStart_1791453 baseEnd_1791453 := by
    simpa [prefixWord, tailWord_1791453, baseEnd_1791453] using wordTrace_append hprefix tailTrace_1791453
  have hstable : (prefixWord ++ tailWord_1791453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791453).length < 2 ^ (prefixWord ++ tailWord_1791453).sum := by decide
  have hdescent : baseEnd_1791453 < baseStart_1791453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791481 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1791481 : Nat := 118140960795 + 1791481 * 2 ^ 59
def prefixEnd_1791481 : Nat := 4983230072969 + 3 ^ 40 * 1791481 * 2
def baseEnd_1791481 : Nat := 613260557598273704032423

theorem tailTrace_1791481 : CollatzResearch.WordTrace tailWord_1791481 prefixEnd_1791481 613260557598273704032423 := by
  unfold tailWord_1791481
  simp only [CollatzResearch.WordTrace]
  refine ⟨65340680022777772441142297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43560453348518514960761531 65340680022777772441142297)
  ·
    refine ⟨49005510017083329330856723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65340680022777772441142297 49005510017083329330856723)
    ·
      refine ⟨73508265025624993996285085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49005510017083329330856723 73508265025624993996285085)
      ·
        refine ⟨27565599384609372748606907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73508265025624993996285085 27565599384609372748606907)
        ·
          refine ⟨41348399076914059122910361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27565599384609372748606907 41348399076914059122910361)
          ·
            refine ⟨31011299307685544342182771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41348399076914059122910361 31011299307685544342182771)
            ·
              refine ⟨46516948961528316513274157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31011299307685544342182771 46516948961528316513274157)
              ·
                refine ⟨17443855860573118692477809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46516948961528316513274157 17443855860573118692477809)
                ·
                  refine ⟨13082891895429839019358357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17443855860573118692477809 13082891895429839019358357)
                  ·
                    refine ⟨613260557598273704032423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13082891895429839019358357 613260557598273704032423)
                    ·
                      rfl

theorem cell22_1791481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1791481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791481 prefixEnd_1791481 := by exact prefixLift 1791481
  have htrace : WordTrace (prefixWord ++ tailWord_1791481) baseStart_1791481 baseEnd_1791481 := by
    simpa [prefixWord, tailWord_1791481, baseEnd_1791481] using wordTrace_append hprefix tailTrace_1791481
  have hstable : (prefixWord ++ tailWord_1791481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791481).length < 2 ^ (prefixWord ++ tailWord_1791481).sum := by decide
  have hdescent : baseEnd_1791481 < baseStart_1791481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791489 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1791489 : Nat := 118140960795 + 1791489 * 2 ^ 59
def prefixEnd_1791489 : Nat := 4983230072969 + 3 ^ 40 * 1791489 * 2
def baseEnd_1791489 : Nat := 613263296161764349832399

theorem tailTrace_1791489 : CollatzResearch.WordTrace tailWord_1791489 prefixEnd_1791489 613263296161764349832399 := by
  unfold tailWord_1791489
  simp only [CollatzResearch.WordTrace]
  refine ⟨65340971806748789807433521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43560647871165859871622347 65340971806748789807433521)
  ·
    refine ⟨49005728855061592355575141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65340971806748789807433521 49005728855061592355575141)
    ·
      refine ⟨9188574160324048566670339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49005728855061592355575141 9188574160324048566670339)
      ·
        refine ⟨13782861240486072850005509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188574160324048566670339 13782861240486072850005509)
        ·
          refine ⟨2584286482591138659376033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13782861240486072850005509 2584286482591138659376033)
          ·
            refine ⟨1938214861943353994532025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584286482591138659376033 1938214861943353994532025)
            ·
              refine ⟨1453661146457515495899019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938214861943353994532025 1453661146457515495899019)
              ·
                refine ⟨2180491719686273243848529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453661146457515495899019 2180491719686273243848529)
                ·
                  refine ⟨1635368789764704932886397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180491719686273243848529 1635368789764704932886397)
                  ·
                    refine ⟨613263296161764349832399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635368789764704932886397 613263296161764349832399)
                    ·
                      rfl

theorem cell22_1791489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1791489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791489 prefixEnd_1791489 := by exact prefixLift 1791489
  have htrace : WordTrace (prefixWord ++ tailWord_1791489) baseStart_1791489 baseEnd_1791489 := by
    simpa [prefixWord, tailWord_1791489, baseEnd_1791489] using wordTrace_append hprefix tailTrace_1791489
  have hstable : (prefixWord ++ tailWord_1791489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791489).length < 2 ^ (prefixWord ++ tailWord_1791489).sum := by decide
  have hdescent : baseEnd_1791489 < baseStart_1791489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791517 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1791517 : Nat := 118140960795 + 1791517 * 2 ^ 59
def prefixEnd_1791517 : Nat := 4983230072969 + 3 ^ 40 * 1791517 * 2
def baseEnd_1791517 : Nat := 613272881133981610132313

theorem tailTrace_1791517 : CollatzResearch.WordTrace tailWord_1791517 prefixEnd_1791517 613272881133981610132313 := by
  unfold tailWord_1791517
  simp only [CollatzResearch.WordTrace]
  refine ⟨65341993050647350589452805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43561328700431567059635203 65341993050647350589452805)
  ·
    refine ⟨12251623696996378235522401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65341993050647350589452805 12251623696996378235522401)
    ·
      refine ⟨9188717772747283676641801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12251623696996378235522401 9188717772747283676641801)
      ·
        refine ⟨6891538329560462757481351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9188717772747283676641801 6891538329560462757481351)
        ·
          refine ⟨10337307494340694136222027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891538329560462757481351 10337307494340694136222027)
          ·
            refine ⟨15505961241511041204333041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337307494340694136222027 15505961241511041204333041)
            ·
              refine ⟨11629470931133280903249781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15505961241511041204333041 11629470931133280903249781)
              ·
                refine ⟨1090262899793745084679667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11629470931133280903249781 1090262899793745084679667)
                ·
                  refine ⟨1635394349690617627019501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090262899793745084679667 1635394349690617627019501)
                  ·
                    refine ⟨613272881133981610132313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635394349690617627019501 613272881133981610132313)
                    ·
                      rfl

theorem cell22_1791517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1791517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791517 prefixEnd_1791517 := by exact prefixLift 1791517
  have htrace : WordTrace (prefixWord ++ tailWord_1791517) baseStart_1791517 baseEnd_1791517 := by
    simpa [prefixWord, tailWord_1791517, baseEnd_1791517] using wordTrace_append hprefix tailTrace_1791517
  have hstable : (prefixWord ++ tailWord_1791517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791517).length < 2 ^ (prefixWord ++ tailWord_1791517).sum := by decide
  have hdescent : baseEnd_1791517 < baseStart_1791517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791530 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_1791530 : Nat := 118140960795 + 1791530 * 2 ^ 59
def prefixEnd_1791530 : Nat := 4983230072969 + 3 ^ 40 * 1791530 * 2
def baseEnd_1791530 : Nat := 204425777099884636519091

theorem tailTrace_1791530 : CollatzResearch.WordTrace tailWord_1791530 prefixEnd_1791530 204425777099884636519091 := by
  unfold tailWord_1791530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335616799900063452419011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43561644799733502539784029 16335616799900063452419011)
  ·
    refine ⟨24503425199850095178628517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16335616799900063452419011 24503425199850095178628517)
    ·
      refine ⟨4594392224971892845992847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24503425199850095178628517 4594392224971892845992847)
      ·
        refine ⟨6891588337457839268989271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594392224971892845992847 6891588337457839268989271)
        ·
          refine ⟨10337382506186758903483907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891588337457839268989271 10337382506186758903483907)
          ·
            refine ⟨15506073759280138355225861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337382506186758903483907 15506073759280138355225861)
            ·
              refine ⟨2907388829865025941604849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15506073759280138355225861 2907388829865025941604849)
              ·
                refine ⟨2180541622398769456203637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907388829865025941604849 2180541622398769456203637)
                ·
                  refine ⟨204425777099884636519091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180541622398769456203637 204425777099884636519091)
                  ·
                    rfl

theorem cell22_1791530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_1791530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791530 prefixEnd_1791530 := by exact prefixLift 1791530
  have htrace : WordTrace (prefixWord ++ tailWord_1791530) baseStart_1791530 baseEnd_1791530 := by
    simpa [prefixWord, tailWord_1791530, baseEnd_1791530] using wordTrace_append hprefix tailTrace_1791530
  have hstable : (prefixWord ++ tailWord_1791530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791530).length < 2 ^ (prefixWord ++ tailWord_1791530).sum := by decide
  have hdescent : baseEnd_1791530 < baseStart_1791530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791534 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1791534 : Nat := 118140960795 + 1791534 * 2 ^ 59
def prefixEnd_1791534 : Nat := 4983230072969 + 3 ^ 40 * 1791534 * 2
def baseEnd_1791534 : Nat := 613278700581399232457261

theorem tailTrace_1791534 : CollatzResearch.WordTrace tailWord_1791534 prefixEnd_1791534 613278700581399232457261 := by
  unfold tailWord_1791534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167826636448220311602707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43561742061057174995214437 8167826636448220311602707)
  ·
    refine ⟨12251739954672330467404061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167826636448220311602707 12251739954672330467404061)
    ·
      refine ⟨4594402483002123925276523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12251739954672330467404061 4594402483002123925276523)
      ·
        refine ⟨6891603724503185887914785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594402483002123925276523 6891603724503185887914785)
        ·
          refine ⟨5168702793377389415936089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6891603724503185887914785 5168702793377389415936089)
          ·
            refine ⟨3876527095033042061952067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5168702793377389415936089 3876527095033042061952067)
            ·
              refine ⟨5814790642549563092928101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876527095033042061952067 5814790642549563092928101)
              ·
                refine ⟨1090273245478043079924019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5814790642549563092928101 1090273245478043079924019)
                ·
                  refine ⟨1635409868217064619886029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090273245478043079924019 1635409868217064619886029)
                  ·
                    refine ⟨613278700581399232457261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635409868217064619886029 613278700581399232457261)
                    ·
                      rfl

theorem cell22_1791534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1791534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791534 prefixEnd_1791534 := by exact prefixLift 1791534
  have htrace : WordTrace (prefixWord ++ tailWord_1791534) baseStart_1791534 baseEnd_1791534 := by
    simpa [prefixWord, tailWord_1791534, baseEnd_1791534] using wordTrace_append hprefix tailTrace_1791534
  have hstable : (prefixWord ++ tailWord_1791534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791534).length < 2 ^ (prefixWord ++ tailWord_1791534).sum := by decide
  have hdescent : baseEnd_1791534 < baseStart_1791534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791543 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1791543 : Nat := 118140960795 + 1791543 * 2 ^ 59
def prefixEnd_1791543 : Nat := 4983230072969 + 3 ^ 40 * 1791543 * 2
def baseEnd_1791543 : Nat := 613281781465326208982233

theorem tailTrace_1791543 : CollatzResearch.WordTrace tailWord_1791543 prefixEnd_1791543 613281781465326208982233 := by
  unfold tailWord_1791543
  simp only [CollatzResearch.WordTrace]
  refine ⟨65342941348553157029899283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43561960899035438019932855 65342941348553157029899283)
  ·
    refine ⟨98014412022829735544848925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65342941348553157029899283 98014412022829735544848925)
    ·
      refine ⟨36755404508561150829318347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98014412022829735544848925 36755404508561150829318347)
      ·
        refine ⟨55133106762841726243977521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36755404508561150829318347 55133106762841726243977521)
        ·
          refine ⟨41349830072131294682983141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55133106762841726243977521 41349830072131294682983141)
          ·
            refine ⟨7753093138524617753059339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41349830072131294682983141 7753093138524617753059339)
            ·
              refine ⟨11629639707786926629589009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753093138524617753059339 11629639707786926629589009)
              ·
                refine ⟨8722229780840194972191757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11629639707786926629589009 8722229780840194972191757)
                ·
                  refine ⟨3270836167815073114571909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8722229780840194972191757 3270836167815073114571909)
                  ·
                    refine ⟨613281781465326208982233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270836167815073114571909 613281781465326208982233)
                    ·
                      rfl

theorem cell22_1791543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1791543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791543 prefixEnd_1791543 := by exact prefixLift 1791543
  have htrace : WordTrace (prefixWord ++ tailWord_1791543) baseStart_1791543 baseEnd_1791543 := by
    simpa [prefixWord, tailWord_1791543, baseEnd_1791543] using wordTrace_append hprefix tailTrace_1791543
  have hstable : (prefixWord ++ tailWord_1791543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791543).length < 2 ^ (prefixWord ++ tailWord_1791543).sum := by decide
  have hdescent : baseEnd_1791543 < baseStart_1791543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791575 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 4]
def baseStart_1791575 : Nat := 118140960795 + 1791575 * 2 ^ 59
def prefixEnd_1791575 : Nat := 4983230072969 + 3 ^ 40 * 1791575 * 2
def baseEnd_1791575 : Nat := 204430911906429597394045

theorem tailTrace_1791575 : CollatzResearch.WordTrace tailWord_1791575 prefixEnd_1791575 204430911906429597394045 := by
  unfold tailWord_1791575
  simp only [CollatzResearch.WordTrace]
  refine ⟨65344108484437226495064179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43562738989624817663376119 65344108484437226495064179)
  ·
    refine ⟨98016162726655839742596269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65344108484437226495064179 98016162726655839742596269)
    ·
      refine ⟨36756061022495939903473601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98016162726655839742596269 36756061022495939903473601)
      ·
        refine ⟨27567045766871954927605201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36756061022495939903473601 27567045766871954927605201)
        ·
          refine ⟨20675284325153966195703901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27567045766871954927605201 20675284325153966195703901)
          ·
            refine ⟨7753231621932737323388963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20675284325153966195703901 7753231621932737323388963)
            ·
              refine ⟨11629847432899105985083445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753231621932737323388963 11629847432899105985083445)
              ·
                refine ⟨1090298196834291186101573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11629847432899105985083445 1090298196834291186101573)
                ·
                  refine ⟨204430911906429597394045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090298196834291186101573 204430911906429597394045)
                  ·
                    rfl

theorem cell22_1791575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 4].length) (baseStart_1791575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791575 prefixEnd_1791575 := by exact prefixLift 1791575
  have htrace : WordTrace (prefixWord ++ tailWord_1791575) baseStart_1791575 baseEnd_1791575 := by
    simpa [prefixWord, tailWord_1791575, baseEnd_1791575] using wordTrace_append hprefix tailTrace_1791575
  have hstable : (prefixWord ++ tailWord_1791575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791575).length < 2 ^ (prefixWord ++ tailWord_1791575).sum := by decide
  have hdescent : baseEnd_1791575 < baseStart_1791575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791581 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 5]
def baseStart_1791581 : Nat := 118140960795 + 1791581 * 2 ^ 59
def prefixEnd_1791581 : Nat := 4983230072969 + 3 ^ 40 * 1791581 * 2
def baseEnd_1791581 : Nat := 204431596547302258844039

theorem tailTrace_1791581 : CollatzResearch.WordTrace tailWord_1791581 prefixEnd_1791581 204431596547302258844039 := by
  unfold tailWord_1791581
  simp only [CollatzResearch.WordTrace]
  refine ⟨65344327322415489519782597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43562884881610326346521731 65344327322415489519782597)
  ·
    refine ⟨12252061372952904284959237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65344327322415489519782597 12252061372952904284959237)
    ·
      refine ⟨2297261507428669553429857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12252061372952904284959237 2297261507428669553429857)
      ·
        refine ⟨1722946130571502165072393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2297261507428669553429857 1722946130571502165072393)
        ·
          refine ⟨1292209597928626623804295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722946130571502165072393 1292209597928626623804295)
          ·
            refine ⟨1938314396892939935706443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292209597928626623804295 1938314396892939935706443)
            ·
              refine ⟨2907471595339409903559665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938314396892939935706443 2907471595339409903559665)
              ·
                refine ⟨2180603696504557427669749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907471595339409903559665 2180603696504557427669749)
                ·
                  refine ⟨204431596547302258844039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180603696504557427669749 204431596547302258844039)
                  ·
                    rfl

theorem cell22_1791581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_1791581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791581 prefixEnd_1791581 := by exact prefixLift 1791581
  have htrace : WordTrace (prefixWord ++ tailWord_1791581) baseStart_1791581 baseEnd_1791581 := by
    simpa [prefixWord, tailWord_1791581, baseEnd_1791581] using wordTrace_append hprefix tailTrace_1791581
  have hstable : (prefixWord ++ tailWord_1791581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791581).length < 2 ^ (prefixWord ++ tailWord_1791581).sum := by decide
  have hdescent : baseEnd_1791581 < baseStart_1791581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791592 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_1791592 : Nat := 118140960795 + 1791592 * 2 ^ 59
def prefixEnd_1791592 : Nat := 4983230072969 + 3 ^ 40 * 1791592 * 2
def baseEnd_1791592 : Nat := 204432851722235471502361

theorem tailTrace_1791592 : CollatzResearch.WordTrace tailWord_1791592 prefixEnd_1791592 204432851722235471502361 := by
  unfold tailWord_1791592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32672364262687819199216515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43563152350250425598955353 32672364262687819199216515)
  ·
    refine ⟨49008546394031728798824773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32672364262687819199216515 49008546394031728798824773)
    ·
      refine ⟨9189102448880949149779645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49008546394031728798824773 9189102448880949149779645)
      ·
        refine ⟨3445913418330355931167367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9189102448880949149779645 3445913418330355931167367)
        ·
          refine ⟨5168870127495533896751051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445913418330355931167367 5168870127495533896751051)
          ·
            refine ⟨7753305191243300845126577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168870127495533896751051 7753305191243300845126577)
            ·
              refine ⟨5814978893432475633844933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753305191243300845126577 5814978893432475633844933)
              ·
                refine ⟨1090308542518589181345925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5814978893432475633844933 1090308542518589181345925)
                ·
                  refine ⟨204432851722235471502361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090308542518589181345925 204432851722235471502361)
                  ·
                    rfl

theorem cell22_1791592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_1791592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791592 prefixEnd_1791592 := by exact prefixLift 1791592
  have htrace : WordTrace (prefixWord ++ tailWord_1791592) baseStart_1791592 baseEnd_1791592 := by
    simpa [prefixWord, tailWord_1791592, baseEnd_1791592] using wordTrace_append hprefix tailTrace_1791592
  have hstable : (prefixWord ++ tailWord_1791592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791592).length < 2 ^ (prefixWord ++ tailWord_1791592).sum := by decide
  have hdescent : baseEnd_1791592 < baseStart_1791592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791605 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1791605 : Nat := 118140960795 + 1791605 * 2 ^ 59
def prefixEnd_1791605 : Nat := 4983230072969 + 3 ^ 40 * 1791605 * 2
def baseEnd_1791605 : Nat := 613303005332378713932043

theorem tailTrace_1791605 : CollatzResearch.WordTrace tailWord_1791605 prefixEnd_1791605 613303005332378713932043 := by
  unfold tailWord_1791605
  simp only [CollatzResearch.WordTrace]
  refine ⟨65345202674328541618656269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43563468449552361079104179 65345202674328541618656269)
  ·
    refine ⟨24504451002873203106996101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65345202674328541618656269 24504451002873203106996101)
    ·
      refine ⟨4594584563038725582561769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24504451002873203106996101 4594584563038725582561769)
      ·
        refine ⟨3445938422279044186921327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4594584563038725582561769 3445938422279044186921327)
        ·
          refine ⟨5168907633418566280381991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445938422279044186921327 5168907633418566280381991)
          ·
            refine ⟨7753361450127849420572987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168907633418566280381991 7753361450127849420572987)
            ·
              refine ⟨11630042175191774130859481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753361450127849420572987 11630042175191774130859481)
              ·
                refine ⟨8722531631393830598144611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11630042175191774130859481 8722531631393830598144611)
                ·
                  refine ⟨13083797447090745897216917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722531631393830598144611 13083797447090745897216917)
                  ·
                    refine ⟨613303005332378713932043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13083797447090745897216917 613303005332378713932043)
                    ·
                      rfl

theorem cell22_1791605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1791605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791605 prefixEnd_1791605 := by exact prefixLift 1791605
  have htrace : WordTrace (prefixWord ++ tailWord_1791605) baseStart_1791605 baseEnd_1791605 := by
    simpa [prefixWord, tailWord_1791605, baseEnd_1791605] using wordTrace_append hprefix tailTrace_1791605
  have hstable : (prefixWord ++ tailWord_1791605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791605).length < 2 ^ (prefixWord ++ tailWord_1791605).sum := by decide
  have hdescent : baseEnd_1791605 < baseStart_1791605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791620 : List Nat := [2, 3, 2, 1, 4, 1, 1, 8]
def baseStart_1791620 : Nat := 118140960795 + 1791620 * 2 ^ 59
def prefixEnd_1791620 : Nat := 4983230072969 + 3 ^ 40 * 1791620 * 2
def baseEnd_1791620 : Nat := 68145348904324852756333

theorem tailTrace_1791620 : CollatzResearch.WordTrace tailWord_1791620 prefixEnd_1791620 68145348904324852756333 := by
  unfold tailWord_1791620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32672874884637099590226157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43563833179516132786968209 32672874884637099590226157)
  ·
    refine ⟨12252328081738912346334809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32672874884637099590226157 12252328081738912346334809)
    ·
      refine ⟨9189246061304184259751107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12252328081738912346334809 9189246061304184259751107)
      ·
        refine ⟨13783869091956276389626661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9189246061304184259751107 13783869091956276389626661)
        ·
          refine ⟨2584475454741801823054999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13783869091956276389626661 2584475454741801823054999)
          ·
            refine ⟨3876713182112702734582499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584475454741801823054999 3876713182112702734582499)
            ·
              refine ⟨5815069773169054101873749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876713182112702734582499 5815069773169054101873749)
              ·
                refine ⟨68145348904324852756333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5815069773169054101873749 68145348904324852756333)
                ·
                  rfl

theorem cell22_1791620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_1791620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791620 prefixEnd_1791620 := by exact prefixLift 1791620
  have htrace : WordTrace (prefixWord ++ tailWord_1791620) baseStart_1791620 baseEnd_1791620 := by
    simpa [prefixWord, tailWord_1791620, baseEnd_1791620] using wordTrace_append hprefix tailTrace_1791620
  have hstable : (prefixWord ++ tailWord_1791620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791620).length < 2 ^ (prefixWord ++ tailWord_1791620).sum := by decide
  have hdescent : baseEnd_1791620 < baseStart_1791620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791652 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_1791652 : Nat := 118140960795 + 1791652 * 2 ^ 59
def prefixEnd_1791652 : Nat := 4983230072969 + 3 ^ 40 * 1791652 * 2
def baseEnd_1791652 : Nat := 613319094392886258006899

theorem tailTrace_1791652 : CollatzResearch.WordTrace tailWord_1791652 prefixEnd_1791652 613319094392886258006899 := by
  unfold tailWord_1791652
  simp only [CollatzResearch.WordTrace]
  refine ⟨32673458452579134322808605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43564611270105512430411473 32673458452579134322808605)
  ·
    refine ⟨12252546919717175371053227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32673458452579134322808605 12252546919717175371053227)
    ·
      refine ⟨18378820379575763056579841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252546919717175371053227 18378820379575763056579841)
      ·
        refine ⟨13784115284681822292434881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18378820379575763056579841 13784115284681822292434881)
        ·
          refine ⟨10338086463511366719326161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13784115284681822292434881 10338086463511366719326161)
          ·
            refine ⟨7753564847633525039494621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338086463511366719326161 7753564847633525039494621)
            ·
              refine ⟨2907586817862571889810483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7753564847633525039494621 2907586817862571889810483)
              ·
                refine ⟨4361380226793857834715725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907586817862571889810483 4361380226793857834715725)
                ·
                  refine ⟨1635517585047696688018397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4361380226793857834715725 1635517585047696688018397)
                  ·
                    refine ⟨613319094392886258006899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635517585047696688018397 613319094392886258006899)
                    ·
                      rfl

theorem cell22_1791652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_1791652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791652 prefixEnd_1791652 := by exact prefixLift 1791652
  have htrace : WordTrace (prefixWord ++ tailWord_1791652) baseStart_1791652 baseEnd_1791652 := by
    simpa [prefixWord, tailWord_1791652, baseEnd_1791652] using wordTrace_append hprefix tailTrace_1791652
  have hstable : (prefixWord ++ tailWord_1791652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791652).length < 2 ^ (prefixWord ++ tailWord_1791652).sum := by decide
  have hdescent : baseEnd_1791652 < baseStart_1791652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791663 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_1791663 : Nat := 118140960795 + 1791663 * 2 ^ 59
def prefixEnd_1791663 : Nat := 4983230072969 + 3 ^ 40 * 1791663 * 2
def baseEnd_1791663 : Nat := 613322859917685895981865

theorem tailTrace_1791663 : CollatzResearch.WordTrace tailWord_1791663 prefixEnd_1791663 613322859917685895981865 := by
  unfold tailWord_1791663
  simp only [CollatzResearch.WordTrace]
  refine ⟨65347318108118417524267643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43564878738745611682845095 65347318108118417524267643)
  ·
    refine ⟨98020977162177626286401465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65347318108118417524267643 98020977162177626286401465)
    ·
      refine ⟨73515732871633219714801099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98020977162177626286401465 73515732871633219714801099)
      ·
        refine ⟨110273599307449829572201649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73515732871633219714801099 110273599307449829572201649)
        ·
          refine ⟨82705199480587372179151237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110273599307449829572201649 82705199480587372179151237)
          ·
            refine ⟨15507224902610132283590857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82705199480587372179151237 15507224902610132283590857)
            ·
              refine ⟨11630418676957599212693143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15507224902610132283590857 11630418676957599212693143)
              ·
                refine ⟨17445628015436398819039715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630418676957599212693143 17445628015436398819039715)
                ·
                  refine ⟨26168442023154598228559573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17445628015436398819039715 26168442023154598228559573)
                  ·
                    refine ⟨613322859917685895981865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26168442023154598228559573 613322859917685895981865)
                    ·
                      rfl

theorem cell22_1791663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_1791663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791663 prefixEnd_1791663 := by exact prefixLift 1791663
  have htrace : WordTrace (prefixWord ++ tailWord_1791663) baseStart_1791663 baseEnd_1791663 := by
    simpa [prefixWord, tailWord_1791663, baseEnd_1791663] using wordTrace_append hprefix tailTrace_1791663
  have hstable : (prefixWord ++ tailWord_1791663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791663).length < 2 ^ (prefixWord ++ tailWord_1791663).sum := by decide
  have hdescent : baseEnd_1791663 < baseStart_1791663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791695 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 1, 4]
def baseStart_1791695 : Nat := 118140960795 + 1791695 * 2 ^ 59
def prefixEnd_1791695 : Nat := 4983230072969 + 3 ^ 40 * 1791695 * 2
def baseEnd_1791695 : Nat := 613333814171648479181767

theorem tailTrace_1791695 : CollatzResearch.WordTrace tailWord_1791695 prefixEnd_1791695 613333814171648479181767 := by
  unfold tailWord_1791695
  simp only [CollatzResearch.WordTrace]
  refine ⟨65348485244002486989432539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43565656829334991326288359 65348485244002486989432539)
  ·
    refine ⟨98022727866003730484148809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65348485244002486989432539 98022727866003730484148809)
    ·
      refine ⟨73517045899502797863111607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98022727866003730484148809 73517045899502797863111607)
      ·
        refine ⟨110275568849254196794667411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73517045899502797863111607 110275568849254196794667411)
        ·
          refine ⟨165413353273881295192001117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110275568849254196794667411 165413353273881295192001117)
          ·
            refine ⟨62030007477705485697000419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165413353273881295192001117 62030007477705485697000419)
            ·
              refine ⟨93045011216558228545500629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62030007477705485697000419 93045011216558228545500629)
              ·
                refine ⟨2180742450388083481535171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93045011216558228545500629 2180742450388083481535171)
                ·
                  refine ⟨3271113675582125222302757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180742450388083481535171 3271113675582125222302757)
                  ·
                    refine ⟨613333814171648479181767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271113675582125222302757 613333814171648479181767)
                    ·
                      rfl

theorem cell22_1791695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_1791695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791695 prefixEnd_1791695 := by exact prefixLift 1791695
  have htrace : WordTrace (prefixWord ++ tailWord_1791695) baseStart_1791695 baseEnd_1791695 := by
    simpa [prefixWord, tailWord_1791695, baseEnd_1791695] using wordTrace_append hprefix tailTrace_1791695
  have hstable : (prefixWord ++ tailWord_1791695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791695).length < 2 ^ (prefixWord ++ tailWord_1791695).sum := by decide
  have hdescent : baseEnd_1791695 < baseStart_1791695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791740 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1791740 : Nat := 118140960795 + 1791740 * 2 ^ 59
def prefixEnd_1791740 : Nat := 4983230072969 + 3 ^ 40 * 1791740 * 2
def baseEnd_1791740 : Nat := 613349218591283361806629

theorem tailTrace_1791740 : CollatzResearch.WordTrace tailWord_1791740 prefixEnd_1791740 613349218591283361806629 := by
  unfold tailWord_1791740
  simp only [CollatzResearch.WordTrace]
  refine ⟨32675063264419729837410337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43566751019226306449880449 32675063264419729837410337)
  ·
    refine ⟨24506297448314797378057753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32675063264419729837410337 24506297448314797378057753)
    ·
      refine ⟨18379723086236098033543315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24506297448314797378057753 18379723086236098033543315)
      ·
        refine ⟨27569584629354147050314973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18379723086236098033543315 27569584629354147050314973)
        ·
          refine ⟨10338594236007805143868115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27569584629354147050314973 10338594236007805143868115)
          ·
            refine ⟨15507891354011707715802173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338594236007805143868115 15507891354011707715802173)
            ·
              refine ⟨5815459257754390393425815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15507891354011707715802173 5815459257754390393425815)
              ·
                refine ⟨8723188886631585590138723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815459257754390393425815 8723188886631585590138723)
                ·
                  refine ⟨13084783329947378385208085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8723188886631585590138723 13084783329947378385208085)
                  ·
                    refine ⟨613349218591283361806629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13084783329947378385208085 613349218591283361806629)
                    ·
                      rfl

theorem cell22_1791740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1791740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791740 prefixEnd_1791740 := by exact prefixLift 1791740
  have htrace : WordTrace (prefixWord ++ tailWord_1791740) baseStart_1791740 baseEnd_1791740 := by
    simpa [prefixWord, tailWord_1791740, baseEnd_1791740] using wordTrace_append hprefix tailTrace_1791740
  have hstable : (prefixWord ++ tailWord_1791740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791740).length < 2 ^ (prefixWord ++ tailWord_1791740).sum := by decide
  have hdescent : baseEnd_1791740 < baseStart_1791740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791800 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_1791800 : Nat := 118140960795 + 1791800 * 2 ^ 59
def prefixEnd_1791800 : Nat := 4983230072969 + 3 ^ 40 * 1791800 * 2
def baseEnd_1791800 : Nat := 204456585939154401768815

theorem tailTrace_1791800 : CollatzResearch.WordTrace tailWord_1791800 prefixEnd_1791800 204456585939154401768815 := by
  unfold tailWord_1791800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676157454311044961002427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43568209939081393281336569 32676157454311044961002427)
  ·
    refine ⟨49014236181466567441503641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32676157454311044961002427 49014236181466567441503641)
    ·
      refine ⟨36760677136099925581127731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49014236181466567441503641 36760677136099925581127731)
      ·
        refine ⟨55141015704149888371691597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36760677136099925581127731 55141015704149888371691597)
        ·
          refine ⟨20677880889056208139384349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55141015704149888371691597 20677880889056208139384349)
          ·
            refine ⟨7754205333396078052269131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20677880889056208139384349 7754205333396078052269131)
            ·
              refine ⟨11631308000094117078403697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754205333396078052269131 11631308000094117078403697)
              ·
                refine ⟨8723481000070587808802773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11631308000094117078403697 8723481000070587808802773)
                ·
                  refine ⟨204456585939154401768815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8723481000070587808802773 204456585939154401768815)
                  ·
                    rfl

theorem cell22_1791800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_1791800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791800 prefixEnd_1791800 := by exact prefixLift 1791800
  have htrace : WordTrace (prefixWord ++ tailWord_1791800) baseStart_1791800 baseEnd_1791800 := by
    simpa [prefixWord, tailWord_1791800, baseEnd_1791800] using wordTrace_append hprefix tailTrace_1791800
  have hstable : (prefixWord ++ tailWord_1791800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791800).length < 2 ^ (prefixWord ++ tailWord_1791800).sum := by decide
  have hdescent : baseEnd_1791800 < baseStart_1791800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791815 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1791815 : Nat := 118140960795 + 1791815 * 2 ^ 59
def prefixEnd_1791815 : Nat := 4983230072969 + 3 ^ 40 * 1791815 * 2
def baseEnd_1791815 : Nat := 613374892624008166181399

theorem tailTrace_1791815 : CollatzResearch.WordTrace tailWord_1791815 prefixEnd_1791815 613374892624008166181399 := by
  unfold tailWord_1791815
  simp only [CollatzResearch.WordTrace]
  refine ⟨65352862003567747483800899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43568574669045164989200599 65352862003567747483800899)
  ·
    refine ⟨98029293005351621225701349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65352862003567747483800899 98029293005351621225701349)
    ·
      refine ⟨18380492438503428979819003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98029293005351621225701349 18380492438503428979819003)
      ·
        refine ⟨27570738657755143469728505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18380492438503428979819003 27570738657755143469728505)
        ·
          refine ⟨20678053993316357602296379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27570738657755143469728505 20678053993316357602296379)
          ·
            refine ⟨31017080989974536403444569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20678053993316357602296379 31017080989974536403444569)
            ·
              refine ⟨23262810742480902302583427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31017080989974536403444569 23262810742480902302583427)
              ·
                refine ⟨34894216113721353453875141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23262810742480902302583427 34894216113721353453875141)
                ·
                  refine ⟨6542665521322753772601589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34894216113721353453875141 6542665521322753772601589)
                  ·
                    refine ⟨613374892624008166181399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6542665521322753772601589 613374892624008166181399)
                    ·
                      rfl

theorem cell22_1791815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1791815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791815 prefixEnd_1791815 := by exact prefixLift 1791815
  have htrace : WordTrace (prefixWord ++ tailWord_1791815) baseStart_1791815 baseEnd_1791815 := by
    simpa [prefixWord, tailWord_1791815, baseEnd_1791815] using wordTrace_append hprefix tailTrace_1791815
  have hstable : (prefixWord ++ tailWord_1791815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791815).length < 2 ^ (prefixWord ++ tailWord_1791815).sum := by decide
  have hdescent : baseEnd_1791815 < baseStart_1791815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791821 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1791821 : Nat := 118140960795 + 1791821 * 2 ^ 59
def prefixEnd_1791821 : Nat := 4983230072969 + 3 ^ 40 * 1791821 * 2
def baseEnd_1791821 : Nat := 613376946546626150531381

theorem tailTrace_1791821 : CollatzResearch.WordTrace tailWord_1791821 prefixEnd_1791821 613376946546626150531381 := by
  unfold tailWord_1791821
  simp only [CollatzResearch.WordTrace]
  refine ⟨65353080841546010508519317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43568720561030673672346211 65353080841546010508519317)
  ·
    refine ⟨3063425664447469242586843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65353080841546010508519317 3063425664447469242586843)
    ·
      refine ⟨4595138496671203863880265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063425664447469242586843 4595138496671203863880265)
      ·
        refine ⟨3446353872503402897910199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4595138496671203863880265 3446353872503402897910199)
        ·
          refine ⟨5169530808755104346865299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446353872503402897910199 5169530808755104346865299)
          ·
            refine ⟨7754296213132656520297949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169530808755104346865299 7754296213132656520297949)
            ·
              refine ⟨2907861079924746195111731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7754296213132656520297949 2907861079924746195111731)
              ·
                refine ⟨4361791619887119292667597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907861079924746195111731 4361791619887119292667597)
                ·
                  refine ⟨1635671857457669734750349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4361791619887119292667597 1635671857457669734750349)
                  ·
                    refine ⟨613376946546626150531381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635671857457669734750349 613376946546626150531381)
                    ·
                      rfl

theorem cell22_1791821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1791821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791821 prefixEnd_1791821 := by exact prefixLift 1791821
  have htrace : WordTrace (prefixWord ++ tailWord_1791821) baseStart_1791821 baseEnd_1791821 := by
    simpa [prefixWord, tailWord_1791821, baseEnd_1791821] using wordTrace_append hprefix tailTrace_1791821
  have hstable : (prefixWord ++ tailWord_1791821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791821).length < 2 ^ (prefixWord ++ tailWord_1791821).sum := by decide
  have hdescent : baseEnd_1791821 < baseStart_1791821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791845 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 8]
def baseStart_1791845 : Nat := 118140960795 + 1791845 * 2 ^ 59
def prefixEnd_1791845 : Nat := 4983230072969 + 3 ^ 40 * 1791845 * 2
def baseEnd_1791845 : Nat := 204461720745699362643769

theorem tailTrace_1791845 : CollatzResearch.WordTrace tailWord_1791845 prefixEnd_1791845 204461720745699362643769 := by
  unfold tailWord_1791845
  simp only [CollatzResearch.WordTrace]
  refine ⟨65353956193459062607392989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43569304128972708404928659 65353956193459062607392989)
  ·
    refine ⟨24507733572547148477772371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65353956193459062607392989 24507733572547148477772371)
    ·
      refine ⟨36761600358820722716658557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507733572547148477772371 36761600358820722716658557)
      ·
        refine ⟨13785600134557771018746959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36761600358820722716658557 13785600134557771018746959)
        ·
          refine ⟨20678400201836656528120439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13785600134557771018746959 20678400201836656528120439)
          ·
            refine ⟨31017600302754984792180659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20678400201836656528120439 31017600302754984792180659)
            ·
              refine ⟨46526400454132477188270989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31017600302754984792180659 46526400454132477188270989)
              ·
                refine ⟨17447400170299678945601621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46526400454132477188270989 17447400170299678945601621)
                ·
                  refine ⟨204461720745699362643769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17447400170299678945601621 204461720745699362643769)
                  ·
                    rfl

theorem cell22_1791845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_1791845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791845 prefixEnd_1791845 := by exact prefixLift 1791845
  have htrace : WordTrace (prefixWord ++ tailWord_1791845) baseStart_1791845 baseEnd_1791845 := by
    simpa [prefixWord, tailWord_1791845, baseEnd_1791845] using wordTrace_append hprefix tailTrace_1791845
  have hstable : (prefixWord ++ tailWord_1791845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791845).length < 2 ^ (prefixWord ++ tailWord_1791845).sum := by decide
  have hdescent : baseEnd_1791845 < baseStart_1791845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791847 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1791847 : Nat := 118140960795 + 1791847 * 2 ^ 59
def prefixEnd_1791847 : Nat := 4983230072969 + 3 ^ 40 * 1791847 * 2
def baseEnd_1791847 : Nat := 613385846877970749381301

theorem tailTrace_1791847 : CollatzResearch.WordTrace tailWord_1791847 prefixEnd_1791847 613385846877970749381301 := by
  unfold tailWord_1791847
  simp only [CollatzResearch.WordTrace]
  refine ⟨65354029139451816948965795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43569352759634544632643863 65354029139451816948965795)
  ·
    refine ⟨98031043709177725423448693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65354029139451816948965795 98031043709177725423448693)
    ·
      refine ⟨9190410347735411758448315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98031043709177725423448693 9190410347735411758448315)
      ·
        refine ⟨13785615521603117637672473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190410347735411758448315 13785615521603117637672473)
        ·
          refine ⟨10339211641202338228254355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13785615521603117637672473 10339211641202338228254355)
          ·
            refine ⟨15508817461803507342381533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10339211641202338228254355 15508817461803507342381533)
            ·
              refine ⟨5815806548176315253393075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15508817461803507342381533 5815806548176315253393075)
              ·
                refine ⟨8723709822264472880089613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815806548176315253393075 8723709822264472880089613)
                ·
                  refine ⟨3271391183349177330033605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8723709822264472880089613 3271391183349177330033605)
                  ·
                    refine ⟨613385846877970749381301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271391183349177330033605 613385846877970749381301)
                    ·
                      rfl

theorem cell22_1791847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1791847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791847 prefixEnd_1791847 := by exact prefixLift 1791847
  have htrace : WordTrace (prefixWord ++ tailWord_1791847) baseStart_1791847 baseEnd_1791847 := by
    simpa [prefixWord, tailWord_1791847, baseEnd_1791847] using wordTrace_append hprefix tailTrace_1791847
  have hstable : (prefixWord ++ tailWord_1791847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791847).length < 2 ^ (prefixWord ++ tailWord_1791847).sum := by decide
  have hdescent : baseEnd_1791847 < baseStart_1791847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791952 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_1791952 : Nat := 118140960795 + 1791952 * 2 ^ 59
def prefixEnd_1791952 : Nat := 4983230072969 + 3 ^ 40 * 1791952 * 2
def baseEnd_1791952 : Nat := 204473930174595158501993

theorem tailTrace_1791952 : CollatzResearch.WordTrace tailWord_1791952 prefixEnd_1791952 204473930174595158501993 := by
  unfold tailWord_1791952
  simp only [CollatzResearch.WordTrace]
  refine ⟨32678929402035709940769055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43571905869380946587692073 32678929402035709940769055)
  ·
    refine ⟨49018394103053564911153583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32678929402035709940769055 49018394103053564911153583)
    ·
      refine ⟨73527591154580347366730375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49018394103053564911153583 73527591154580347366730375)
      ·
        refine ⟨110291386731870521050095563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73527591154580347366730375 110291386731870521050095563)
        ·
          refine ⟨165437080097805781575143345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110291386731870521050095563 165437080097805781575143345)
          ·
            refine ⟨124077810073354336181357509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165437080097805781575143345 124077810073354336181357509)
            ·
              refine ⟨23264589388753938034004533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124077810073354336181357509 23264589388753938034004533)
              ·
                refine ⟨2181055255195681690687925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23264589388753938034004533 2181055255195681690687925)
                ·
                  refine ⟨204473930174595158501993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2181055255195681690687925 204473930174595158501993)
                  ·
                    rfl

theorem cell22_1791952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_1791952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791952 prefixEnd_1791952 := by exact prefixLift 1791952
  have htrace : WordTrace (prefixWord ++ tailWord_1791952) baseStart_1791952 baseEnd_1791952 := by
    simpa [prefixWord, tailWord_1791952, baseEnd_1791952] using wordTrace_append hprefix tailTrace_1791952
  have hstable : (prefixWord ++ tailWord_1791952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791952).length < 2 ^ (prefixWord ++ tailWord_1791952).sum := by decide
  have hdescent : baseEnd_1791952 < baseStart_1791952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791958 : List Nat := [5, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1791958 : Nat := 118140960795 + 1791958 * 2 ^ 59
def prefixEnd_1791958 : Nat := 4983230072969 + 3 ^ 40 * 1791958 * 2
def baseEnd_1791958 : Nat := 68158204938489273317329

theorem tailTrace_1791958 : CollatzResearch.WordTrace tailWord_1791958 prefixEnd_1791958 68158204938489273317329 := by
  unfold tailWord_1791958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084879852628105181641033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43572051761366455270837685 4084879852628105181641033)
  ·
    refine ⟨3063659889471078886230775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4084879852628105181641033 3063659889471078886230775)
    ·
      refine ⟨4595489834206618329346163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063659889471078886230775 4595489834206618329346163)
      ·
        refine ⟨6893234751309927494019245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595489834206618329346163 6893234751309927494019245)
        ·
          refine ⟨2584963031741222810257217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6893234751309927494019245 2584963031741222810257217)
          ·
            refine ⟨1938722273805917107692913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584963031741222810257217 1938722273805917107692913)
            ·
              refine ⟨1454041705354437830769685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938722273805917107692913 1454041705354437830769685)
              ·
                refine ⟨68158204938489273317329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1454041705354437830769685 68158204938489273317329)
                ·
                  rfl

theorem cell22_1791958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1791958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791958 prefixEnd_1791958 := by exact prefixLift 1791958
  have htrace : WordTrace (prefixWord ++ tailWord_1791958) baseStart_1791958 baseEnd_1791958 := by
    simpa [prefixWord, tailWord_1791958, baseEnd_1791958] using wordTrace_append hprefix tailTrace_1791958
  have hstable : (prefixWord ++ tailWord_1791958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791958).length < 2 ^ (prefixWord ++ tailWord_1791958).sum := by decide
  have hdescent : baseEnd_1791958 < baseStart_1791958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791990 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_1791990 : Nat := 118140960795 + 1791990 * 2 ^ 59
def prefixEnd_1791990 : Nat := 4983230072969 + 3 ^ 40 * 1791990 * 2
def baseEnd_1791990 : Nat := 613434798700366043055863

theorem tailTrace_1791990 : CollatzResearch.WordTrace tailWord_1791990 prefixEnd_1791990 613434798700366043055863 := by
  unfold tailWord_1791990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084952798620859523213839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43572829851955834914280949 4084952798620859523213839)
  ·
    refine ⟨6127429197931289284820759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084952798620859523213839 6127429197931289284820759)
    ·
      refine ⟨9191143796896933927231139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127429197931289284820759 9191143796896933927231139)
      ·
        refine ⟨13786715695345400890846709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191143796896933927231139 13786715695345400890846709)
        ·
          refine ⟨1292504596438631333516879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13786715695345400890846709 1292504596438631333516879)
          ·
            refine ⟨1938756894657947000275319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292504596438631333516879 1938756894657947000275319)
            ·
              refine ⟨2908135341986920500412979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938756894657947000275319 2908135341986920500412979)
              ·
                refine ⟨4362203012980380750619469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908135341986920500412979 4362203012980380750619469)
                ·
                  refine ⟨1635826129867642781482301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4362203012980380750619469 1635826129867642781482301)
                  ·
                    refine ⟨613434798700366043055863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635826129867642781482301 613434798700366043055863)
                    ·
                      rfl

theorem cell22_1791990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_1791990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1791990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1791990 prefixEnd_1791990 := by exact prefixLift 1791990
  have htrace : WordTrace (prefixWord ++ tailWord_1791990) baseStart_1791990 baseEnd_1791990 := by
    simpa [prefixWord, tailWord_1791990, baseEnd_1791990] using wordTrace_append hprefix tailTrace_1791990
  have hstable : (prefixWord ++ tailWord_1791990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791990).length < 2 ^ (prefixWord ++ tailWord_1791990).sum := by decide
  have hdescent : baseEnd_1791990 < baseStart_1791990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792029 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1792029 : Nat := 118140960795 + 1792029 * 2 ^ 59
def prefixEnd_1792029 : Nat := 4983230072969 + 3 ^ 40 * 1792029 * 2
def baseEnd_1792029 : Nat := 613448149197382941330743

theorem tailTrace_1792029 : CollatzResearch.WordTrace tailWord_1792029 prefixEnd_1792029 613448149197382941330743 := by
  unfold tailWord_1792029
  simp only [CollatzResearch.WordTrace]
  refine ⟨65360667224792462032091141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43573778149861641354727427 65360667224792462032091141)
  ·
    refine ⟨12255125104648586631017089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65360667224792462032091141 12255125104648586631017089)
    ·
      refine ⟨9191343828486439973262817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12255125104648586631017089 9191343828486439973262817)
      ·
        refine ⟨6893507871364829979947113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191343828486439973262817 6893507871364829979947113)
        ·
          refine ⟨5170130903523622484960335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6893507871364829979947113 5170130903523622484960335)
          ·
            refine ⟨7755196355285433727440503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170130903523622484960335 7755196355285433727440503)
            ·
              refine ⟨11632794532928150591160755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755196355285433727440503 11632794532928150591160755)
              ·
                refine ⟨17449191799392225886741133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11632794532928150591160755 17449191799392225886741133)
                ·
                  refine ⟨6543446924772084707527925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17449191799392225886741133 6543446924772084707527925)
                  ·
                    refine ⟨613448149197382941330743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6543446924772084707527925 613448149197382941330743)
                    ·
                      rfl

theorem cell22_1792029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1792029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792029 prefixEnd_1792029 := by exact prefixLift 1792029
  have htrace : WordTrace (prefixWord ++ tailWord_1792029) baseStart_1792029 baseEnd_1792029 := by
    simpa [prefixWord, tailWord_1792029, baseEnd_1792029] using wordTrace_append hprefix tailTrace_1792029
  have hstable : (prefixWord ++ tailWord_1792029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792029).length < 2 ^ (prefixWord ++ tailWord_1792029).sum := by decide
  have hdescent : baseEnd_1792029 < baseStart_1792029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792033 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_1792033 : Nat := 118140960795 + 1792033 * 2 ^ 59
def prefixEnd_1792033 : Nat := 4983230072969 + 3 ^ 40 * 1792033 * 2
def baseEnd_1792033 : Nat := 613449518479128264230731

theorem tailTrace_1792033 : CollatzResearch.WordTrace tailWord_1792033 prefixEnd_1792033 613449518479128264230731 := by
  unfold tailWord_1792033
  simp only [CollatzResearch.WordTrace]
  refine ⟨65360813116777970715236753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43573875411185313810157835 65360813116777970715236753)
  ·
    refine ⟨49020609837583478036427565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65360813116777970715236753 49020609837583478036427565)
    ·
      refine ⟨18382728689093804263660337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49020609837583478036427565 18382728689093804263660337)
      ·
        refine ⟨13787046516820353197745253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18382728689093804263660337 13787046516820353197745253)
        ·
          refine ⟨2585071221903816224577235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13787046516820353197745253 2585071221903816224577235)
          ·
            refine ⟨3877606832855724336865853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585071221903816224577235 3877606832855724336865853)
            ·
              refine ⟨1454102562320896626324695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3877606832855724336865853 1454102562320896626324695)
              ·
                refine ⟨2181153843481344939487043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454102562320896626324695 2181153843481344939487043)
                ·
                  refine ⟨3271730765222017409230565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181153843481344939487043 3271730765222017409230565)
                  ·
                    refine ⟨613449518479128264230731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271730765222017409230565 613449518479128264230731)
                    ·
                      rfl

theorem cell22_1792033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_1792033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792033 prefixEnd_1792033 := by exact prefixLift 1792033
  have htrace : WordTrace (prefixWord ++ tailWord_1792033) baseStart_1792033 baseEnd_1792033 := by
    simpa [prefixWord, tailWord_1792033, baseEnd_1792033] using wordTrace_append hprefix tailTrace_1792033
  have hstable : (prefixWord ++ tailWord_1792033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792033).length < 2 ^ (prefixWord ++ tailWord_1792033).sum := by decide
  have hdescent : baseEnd_1792033 < baseStart_1792033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792048 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_1792048 : Nat := 118140960795 + 1792048 * 2 ^ 59
def prefixEnd_1792048 : Nat := 4983230072969 + 3 ^ 40 * 1792048 * 2
def baseEnd_1792048 : Nat := 204484884428557741701895

theorem tailTrace_1792048 : CollatzResearch.WordTrace tailWord_1792048 prefixEnd_1792048 204484884428557741701895 := by
  unfold tailWord_1792048
  simp only [CollatzResearch.WordTrace]
  refine ⟨32680680105861814138516399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43574240141149085518021865 32680680105861814138516399)
  ·
    refine ⟨49021020158792721207774599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32680680105861814138516399 49021020158792721207774599)
    ·
      refine ⟨73531530238189081811661899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49021020158792721207774599 73531530238189081811661899)
      ·
        refine ⟨110297295357283622717492849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73531530238189081811661899 110297295357283622717492849)
        ·
          refine ⟨82722971517962717038119637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110297295357283622717492849 82722971517962717038119637)
          ·
            refine ⟨1938819644952251180580929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82722971517962717038119637 1938819644952251180580929)
            ·
              refine ⟨1454114733714188385435697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938819644952251180580929 1454114733714188385435697)
              ·
                refine ⟨1090586050285641289076773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454114733714188385435697 1090586050285641289076773)
                ·
                  refine ⟨204484884428557741701895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090586050285641289076773 204484884428557741701895)
                  ·
                    rfl

theorem cell22_1792048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_1792048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792048 prefixEnd_1792048 := by exact prefixLift 1792048
  have htrace : WordTrace (prefixWord ++ tailWord_1792048) baseStart_1792048 baseEnd_1792048 := by
    simpa [prefixWord, tailWord_1792048, baseEnd_1792048] using wordTrace_append hprefix tailTrace_1792048
  have hstable : (prefixWord ++ tailWord_1792048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792048).length < 2 ^ (prefixWord ++ tailWord_1792048).sum := by decide
  have hdescent : baseEnd_1792048 < baseStart_1792048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792108 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_1792108 : Nat := 118140960795 + 1792108 * 2 ^ 59
def prefixEnd_1792108 : Nat := 4983230072969 + 3 ^ 40 * 1792108 * 2
def baseEnd_1792108 : Nat := 613475192511853068605501

theorem tailTrace_1792108 : CollatzResearch.WordTrace tailWord_1792108 prefixEnd_1792108 613475192511853068605501 := by
  unfold tailWord_1792108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32681774295753129262108489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43575699061004172349477985 32681774295753129262108489)
  ·
    refine ⟨24511330721814846946581367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32681774295753129262108489 24511330721814846946581367)
    ·
      refine ⟨36766996082722270419872051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24511330721814846946581367 36766996082722270419872051)
      ·
        refine ⟨55150494124083405629808077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36766996082722270419872051 55150494124083405629808077)
        ·
          refine ⟨20681435296531277111178029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55150494124083405629808077 20681435296531277111178029)
          ·
            refine ⟨7755538236199228916691761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20681435296531277111178029 7755538236199228916691761)
            ·
              refine ⟨5816653677149421687518821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7755538236199228916691761 5816653677149421687518821)
              ·
                refine ⟨1090622564465516566409779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5816653677149421687518821 1090622564465516566409779)
                ·
                  refine ⟨1635933846698274849614669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090622564465516566409779 1635933846698274849614669)
                  ·
                    refine ⟨613475192511853068605501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635933846698274849614669 613475192511853068605501)
                    ·
                      rfl

theorem cell22_1792108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_1792108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792108 prefixEnd_1792108 := by exact prefixLift 1792108
  have htrace : WordTrace (prefixWord ++ tailWord_1792108) baseStart_1792108 baseEnd_1792108 := by
    simpa [prefixWord, tailWord_1792108, baseEnd_1792108] using wordTrace_append hprefix tailTrace_1792108
  have hstable : (prefixWord ++ tailWord_1792108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792108).length < 2 ^ (prefixWord ++ tailWord_1792108).sum := by decide
  have hdescent : baseEnd_1792108 < baseStart_1792108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792119 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1792119 : Nat := 118140960795 + 1792119 * 2 ^ 59
def prefixEnd_1792119 : Nat := 4983230072969 + 3 ^ 40 * 1792119 * 2
def baseEnd_1792119 : Nat := 613478958036652706580467

theorem tailTrace_1792119 : CollatzResearch.WordTrace tailWord_1792119 prefixEnd_1792119 613478958036652706580467 := by
  unfold tailWord_1792119
  simp only [CollatzResearch.WordTrace]
  refine ⟨65363949794466407402867411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43575966529644271601911607 65363949794466407402867411)
  ·
    refine ⟨98045924691699611104301117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65363949794466407402867411 98045924691699611104301117)
    ·
      refine ⟨36767221759387354164112919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98045924691699611104301117 36767221759387354164112919)
      ·
        refine ⟨55150832639081031246169379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36767221759387354164112919 55150832639081031246169379)
        ·
          refine ⟨82726248958621546869254069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55150832639081031246169379 82726248958621546869254069)
          ·
            refine ⟨7755585839870770018992569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82726248958621546869254069 7755585839870770018992569)
            ·
              refine ⟨5816689379903077514244427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7755585839870770018992569 5816689379903077514244427)
              ·
                refine ⟨8725034069854616271366641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816689379903077514244427 8725034069854616271366641)
                ·
                  refine ⟨6543775552390962203524981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725034069854616271366641 6543775552390962203524981)
                  ·
                    refine ⟨613478958036652706580467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6543775552390962203524981 613478958036652706580467)
                    ·
                      rfl

theorem cell22_1792119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1792119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792119 prefixEnd_1792119 := by exact prefixLift 1792119
  have htrace : WordTrace (prefixWord ++ tailWord_1792119) baseStart_1792119 baseEnd_1792119 := by
    simpa [prefixWord, tailWord_1792119, baseEnd_1792119] using wordTrace_append hprefix tailTrace_1792119
  have hstable : (prefixWord ++ tailWord_1792119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792119).length < 2 ^ (prefixWord ++ tailWord_1792119).sum := by decide
  have hdescent : baseEnd_1792119 < baseStart_1792119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792142 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_1792142 : Nat := 118140960795 + 1792142 * 2 ^ 59
def prefixEnd_1792142 : Nat := 4983230072969 + 3 ^ 40 * 1792142 * 2
def baseEnd_1792142 : Nat := 613486831406688313255397

theorem tailTrace_1792142 : CollatzResearch.WordTrace tailWord_1792142 prefixEnd_1792142 613486831406688313255397 := by
  unfold tailWord_1792142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170598584172885291369335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43576525782255388220636453 8170598584172885291369335)
  ·
    refine ⟨12255897876259327937054003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8170598584172885291369335 12255897876259327937054003)
    ·
      refine ⟨18383846814388991905581005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255897876259327937054003 18383846814388991905581005)
      ·
        refine ⟨6893942555395871964592877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18383846814388991905581005 6893942555395871964592877)
        ·
          refine ⟨2585228458273451986722329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6893942555395871964592877 2585228458273451986722329)
          ·
            refine ⟨1938921343705088990041747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585228458273451986722329 1938921343705088990041747)
            ·
              refine ⟨2908382015557633485062621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938921343705088990041747 2908382015557633485062621)
              ·
                refine ⟨1090643255834112556898483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2908382015557633485062621 1090643255834112556898483)
                ·
                  refine ⟨1635964883751168835347725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090643255834112556898483 1635964883751168835347725)
                  ·
                    refine ⟨613486831406688313255397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635964883751168835347725 613486831406688313255397)
                    ·
                      rfl

theorem cell22_1792142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_1792142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792142 prefixEnd_1792142 := by exact prefixLift 1792142
  have htrace : WordTrace (prefixWord ++ tailWord_1792142) baseStart_1792142 baseEnd_1792142 := by
    simpa [prefixWord, tailWord_1792142, baseEnd_1792142] using wordTrace_append hprefix tailTrace_1792142
  have hstable : (prefixWord ++ tailWord_1792142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792142).length < 2 ^ (prefixWord ++ tailWord_1792142).sum := by decide
  have hdescent : baseEnd_1792142 < baseStart_1792142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792179 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_1792179 : Nat := 118140960795 + 1792179 * 2 ^ 59
def prefixEnd_1792179 : Nat := 4983230072969 + 3 ^ 40 * 1792179 * 2
def baseEnd_1792179 : Nat := 613499497262832550080283

theorem tailTrace_1792179 : CollatzResearch.WordTrace tailWord_1792179 prefixEnd_1792179 613499497262832550080283 := by
  unfold tailWord_1792179
  simp only [CollatzResearch.WordTrace]
  refine ⟨65366138174249037650051591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43577425449499358433367727 65366138174249037650051591)
  ·
    refine ⟨98049207261373556475077387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65366138174249037650051591 98049207261373556475077387)
    ·
      refine ⟨147073810892060334712616081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98049207261373556475077387 147073810892060334712616081)
      ·
        refine ⟨110305358169045251034462061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147073810892060334712616081 110305358169045251034462061)
        ·
          refine ⟨41364509313391969137923273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110305358169045251034462061 41364509313391969137923273)
          ·
            refine ⟨31023381985043976853442455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41364509313391969137923273 31023381985043976853442455)
            ·
              refine ⟨46535072977565965280163683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31023381985043976853442455 46535072977565965280163683)
              ·
                refine ⟨69802609466348947920245525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46535072977565965280163683 69802609466348947920245525)
                ·
                  refine ⟨3271997318735106933761509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69802609466348947920245525 3271997318735106933761509)
                  ·
                    refine ⟨613499497262832550080283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271997318735106933761509 613499497262832550080283)
                    ·
                      rfl

theorem cell22_1792179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_1792179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792179 prefixEnd_1792179 := by exact prefixLift 1792179
  have htrace : WordTrace (prefixWord ++ tailWord_1792179) baseStart_1792179 baseEnd_1792179 := by
    simpa [prefixWord, tailWord_1792179, baseEnd_1792179] using wordTrace_append hprefix tailTrace_1792179
  have hstable : (prefixWord ++ tailWord_1792179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792179).length < 2 ^ (prefixWord ++ tailWord_1792179).sum := by decide
  have hdescent : baseEnd_1792179 < baseStart_1792179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792224 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_1792224 : Nat := 118140960795 + 1792224 * 2 ^ 59
def prefixEnd_1792224 : Nat := 4983230072969 + 3 ^ 40 * 1792224 * 2
def baseEnd_1792224 : Nat := 613514901682467432705145

theorem tailTrace_1792224 : CollatzResearch.WordTrace tailWord_1792224 prefixEnd_1792224 613514901682467432705145 := by
  unfold tailWord_1792224
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683889729543005167719863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43578519639390673556959817 32683889729543005167719863)
  ·
    refine ⟨49025834594314507751579795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32683889729543005167719863 49025834594314507751579795)
    ·
      refine ⟨73538751891471761627369693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49025834594314507751579795 73538751891471761627369693)
      ·
        refine ⟨27577031959301910610263635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73538751891471761627369693 27577031959301910610263635)
        ·
          refine ⟨41365547938952865915395453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27577031959301910610263635 41365547938952865915395453)
          ·
            refine ⟨15512080477107324718273295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41365547938952865915395453 15512080477107324718273295)
            ·
              refine ⟨23268120715660987077409943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15512080477107324718273295 23268120715660987077409943)
              ·
                refine ⟨34902181073491480616114915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23268120715660987077409943 34902181073491480616114915)
                ·
                  refine ⟨52353271610237220924172373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34902181073491480616114915 52353271610237220924172373)
                  ·
                    refine ⟨613514901682467432705145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52353271610237220924172373 613514901682467432705145)
                    ·
                      rfl

theorem cell22_1792224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_1792224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792224 prefixEnd_1792224 := by exact prefixLift 1792224
  have htrace : WordTrace (prefixWord ++ tailWord_1792224) baseStart_1792224 baseEnd_1792224 := by
    simpa [prefixWord, tailWord_1792224, baseEnd_1792224] using wordTrace_append hprefix tailTrace_1792224
  have hstable : (prefixWord ++ tailWord_1792224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792224).length < 2 ^ (prefixWord ++ tailWord_1792224).sum := by decide
  have hdescent : baseEnd_1792224 < baseStart_1792224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792273 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 5]
def baseStart_1792273 : Nat := 118140960795 + 1792273 * 2 ^ 59
def prefixEnd_1792273 : Nat := 4983230072969 + 3 ^ 40 * 1792273 * 2
def baseEnd_1792273 : Nat := 204510558461282546076665

theorem tailTrace_1792273 : CollatzResearch.WordTrace tailWord_1792273 prefixEnd_1792273 204510558461282546076665 := by
  unfold tailWord_1792273
  simp only [CollatzResearch.WordTrace]
  refine ⟨65369566635908491703973473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43579711090605661135982315 65369566635908491703973473)
  ·
    refine ⟨49027174976931368777980105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65369566635908491703973473 49027174976931368777980105)
    ·
      refine ⟨36770381232698526583485079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49027174976931368777980105 36770381232698526583485079)
      ·
        refine ⟨55155571849047789875227619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36770381232698526583485079 55155571849047789875227619)
        ·
          refine ⟨82733357773571684812841429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55155571849047789875227619 82733357773571684812841429)
          ·
            refine ⟨1939063072818086362800971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82733357773571684812841429 1939063072818086362800971)
            ·
              refine ⟨2908594609227129544201457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939063072818086362800971 2908594609227129544201457)
              ·
                refine ⟨2181445956920347158151093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908594609227129544201457 2181445956920347158151093)
                ·
                  refine ⟨204510558461282546076665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2181445956920347158151093 204510558461282546076665)
                  ·
                    rfl

theorem cell22_1792273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_1792273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792273 prefixEnd_1792273 := by exact prefixLift 1792273
  have htrace : WordTrace (prefixWord ++ tailWord_1792273) baseStart_1792273 baseEnd_1792273 := by
    simpa [prefixWord, tailWord_1792273, baseEnd_1792273] using wordTrace_append hprefix tailTrace_1792273
  have hstable : (prefixWord ++ tailWord_1792273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792273).length < 2 ^ (prefixWord ++ tailWord_1792273).sum := by decide
  have hdescent : baseEnd_1792273 < baseStart_1792273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792290 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1792290 : Nat := 118140960795 + 1792290 * 2 ^ 59
def prefixEnd_1792290 : Nat := 4983230072969 + 3 ^ 40 * 1792290 * 2
def baseEnd_1792290 : Nat := 204512498277088420184981

theorem tailTrace_1792290 : CollatzResearch.WordTrace tailWord_1792290 prefixEnd_1792290 204512498277088420184981 := by
  unfold tailWord_1792290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342546669211725901835581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43580124451231269071561549 16342546669211725901835581)
  ·
    refine ⟨6128455000954397213188343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16342546669211725901835581 6128455000954397213188343)
    ·
      refine ⟨9192682501431595819782515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6128455000954397213188343 9192682501431595819782515)
      ·
        refine ⟨13789023752147393729673773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9192682501431595819782515 13789023752147393729673773)
        ·
          refine ⟨5170883907055272648627665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13789023752147393729673773 5170883907055272648627665)
          ·
            refine ⟨3878162930291454486470749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170883907055272648627665 3878162930291454486470749)
            ·
              refine ⟨1454311098859295432426531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3878162930291454486470749 1454311098859295432426531)
              ·
                refine ⟨2181466648288943148639797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454311098859295432426531 2181466648288943148639797)
                ·
                  refine ⟨204512498277088420184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2181466648288943148639797 204512498277088420184981)
                  ·
                    rfl

theorem cell22_1792290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1792290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792290 prefixEnd_1792290 := by exact prefixLift 1792290
  have htrace : WordTrace (prefixWord ++ tailWord_1792290) baseStart_1792290 baseEnd_1792290 := by
    simpa [prefixWord, tailWord_1792290, baseEnd_1792290] using wordTrace_append hprefix tailTrace_1792290
  have hstable : (prefixWord ++ tailWord_1792290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792290).length < 2 ^ (prefixWord ++ tailWord_1792290).sum := by decide
  have hdescent : baseEnd_1792290 < baseStart_1792290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792316 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1792316 : Nat := 118140960795 + 1792316 * 2 ^ 59
def prefixEnd_1792316 : Nat := 4983230072969 + 3 ^ 40 * 1792316 * 2
def baseEnd_1792316 : Nat := 613546395162609859404863

theorem tailTrace_1792316 : CollatzResearch.WordTrace tailWord_1792316 prefixEnd_1792316 613546395162609859404863 := by
  unfold tailWord_1792316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32685567487376355023894401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43580756649835140031859201 32685567487376355023894401)
  ·
    refine ⟨24514175615532266267920801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32685567487376355023894401 24514175615532266267920801)
    ·
      refine ⟨18385631711649199700940601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24514175615532266267920801 18385631711649199700940601)
      ·
        refine ⟨13789223783736899775705451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18385631711649199700940601 13789223783736899775705451)
        ·
          refine ⟨20683835675605349663558177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13789223783736899775705451 20683835675605349663558177)
          ·
            refine ⟨15512876756704012247668633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20683835675605349663558177 15512876756704012247668633)
            ·
              refine ⟨11634657567528009185751475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15512876756704012247668633 11634657567528009185751475)
              ·
                refine ⟨17451986351292013778627213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11634657567528009185751475 17451986351292013778627213)
                ·
                  refine ⟨6544494881734505166985205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17451986351292013778627213 6544494881734505166985205)
                  ·
                    refine ⟨613546395162609859404863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6544494881734505166985205 613546395162609859404863)
                    ·
                      rfl

theorem cell22_1792316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1792316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792316 prefixEnd_1792316 := by exact prefixLift 1792316
  have htrace : WordTrace (prefixWord ++ tailWord_1792316) baseStart_1792316 baseEnd_1792316 := by
    simpa [prefixWord, tailWord_1792316, baseEnd_1792316] using wordTrace_append hprefix tailTrace_1792316
  have hstable : (prefixWord ++ tailWord_1792316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792316).length < 2 ^ (prefixWord ++ tailWord_1792316).sum := by decide
  have hdescent : baseEnd_1792316 < baseStart_1792316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792386 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1792386 : Nat := 118140960795 + 1792386 * 2 ^ 59
def prefixEnd_1792386 : Nat := 4983230072969 + 3 ^ 40 * 1792386 * 2
def baseEnd_1792386 : Nat := 204523452531051003384883

theorem tailTrace_1792386 : CollatzResearch.WordTrace tailWord_1792386 prefixEnd_1792386 204523452531051003384883 := by
  unfold tailWord_1792386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16343422021124778000709253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43582458722999408001891341 16343422021124778000709253)
  ·
    refine ⟨3064391628960895875132985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16343422021124778000709253 3064391628960895875132985)
    ·
      refine ⟨2298293721720671906349739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064391628960895875132985 2298293721720671906349739)
      ·
        refine ⟨3447440582581007859524609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298293721720671906349739 3447440582581007859524609)
        ·
          refine ⟨2585580436935755894643457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447440582581007859524609 2585580436935755894643457)
          ·
            refine ⟨1939185327701816920982593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585580436935755894643457 1939185327701816920982593)
            ·
              refine ⟨1454388995776362690736945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939185327701816920982593 1454388995776362690736945)
              ·
                refine ⟨1090791746832272018052709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454388995776362690736945 1090791746832272018052709)
                ·
                  refine ⟨204523452531051003384883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090791746832272018052709 204523452531051003384883)
                  ·
                    rfl

theorem cell22_1792386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1792386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792386 prefixEnd_1792386 := by exact prefixLift 1792386
  have htrace : WordTrace (prefixWord ++ tailWord_1792386) baseStart_1792386 baseEnd_1792386 := by
    simpa [prefixWord, tailWord_1792386, baseEnd_1792386] using wordTrace_append hprefix tailTrace_1792386
  have hstable : (prefixWord ++ tailWord_1792386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792386).length < 2 ^ (prefixWord ++ tailWord_1792386).sum := by decide
  have hdescent : baseEnd_1792386 < baseStart_1792386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792470 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1792470 : Nat := 118140960795 + 1792470 * 2 ^ 59
def prefixEnd_1792470 : Nat := 4983230072969 + 3 ^ 40 * 1792470 * 2
def baseEnd_1792470 : Nat := 204533037503268263684797

theorem tailTrace_1792470 : CollatzResearch.WordTrace tailWord_1792470 prefixEnd_1792470 204533037503268263684797 := by
  unfold tailWord_1792470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086046988512174646805929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43584501210796529565929909 4086046988512174646805929)
  ·
    refine ⟨3064535241384130985104447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4086046988512174646805929 3064535241384130985104447)
    ·
      refine ⟨4596802862076196477656671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064535241384130985104447 4596802862076196477656671)
      ·
        refine ⟨6895204293114294716485007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596802862076196477656671 6895204293114294716485007)
        ·
          refine ⟨10342806439671442074727511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895204293114294716485007 10342806439671442074727511)
          ·
            refine ⟨15514209659507163112091267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342806439671442074727511 15514209659507163112091267)
            ·
              refine ⟨23271314489260744668136901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15514209659507163112091267 23271314489260744668136901)
              ·
                refine ⟨4363371466736389625275669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23271314489260744668136901 4363371466736389625275669)
                ·
                  refine ⟨204533037503268263684797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4363371466736389625275669 204533037503268263684797)
                  ·
                    rfl

theorem cell22_1792470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1792470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1792470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1792470 prefixEnd_1792470 := by exact prefixLift 1792470
  have htrace : WordTrace (prefixWord ++ tailWord_1792470) baseStart_1792470 baseEnd_1792470 := by
    simpa [prefixWord, tailWord_1792470, baseEnd_1792470] using wordTrace_append hprefix tailTrace_1792470
  have hstable : (prefixWord ++ tailWord_1792470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792470).length < 2 ^ (prefixWord ++ tailWord_1792470).sum := by decide
  have hdescent : baseEnd_1792470 < baseStart_1792470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
