import V185TrunkScan23Chunk1054

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6246066 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_6246066 : Nat := 118140960795 + 6246066 * 2 ^ 59
def prefixEnd_6246066 : Nat := 4983230072969 + 3 ^ 40 * 6246066 * 2
def baseEnd_6246066 : Nat := 1069078019235288157249957

theorem tailTrace_6246066 : CollatzResearch.WordTrace tailWord_6246066 prefixEnd_6246066 1069078019235288157249957 := by
  unfold tailWord_6246066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56953185647394274997537513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151875161726384733326766701 56953185647394274997537513)
  ·
    refine ⟨42714889235545706248153135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56953185647394274997537513 42714889235545706248153135)
    ·
      refine ⟨64072333853318559372229703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42714889235545706248153135 64072333853318559372229703)
      ·
        refine ⟨96108500779977839058344555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64072333853318559372229703 96108500779977839058344555)
        ·
          refine ⟨144162751169966758587516833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96108500779977839058344555 144162751169966758587516833)
          ·
            refine ⟨108122063377475068940637625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144162751169966758587516833 108122063377475068940637625)
            ·
              refine ⟨81091547533106301705478219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108122063377475068940637625 81091547533106301705478219)
              ·
                refine ⟨121637321299659452558217329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81091547533106301705478219 121637321299659452558217329)
                ·
                  refine ⟨91227990974744589418662997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121637321299659452558217329 91227990974744589418662997)
                  ·
                    refine ⟨1069078019235288157249957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91227990974744589418662997 1069078019235288157249957)
                    ·
                      rfl

theorem cell23_6246066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_6246066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246066 prefixEnd_6246066 := by exact prefixLift 6246066
  have htrace : WordTrace (prefixWord ++ tailWord_6246066) baseStart_6246066 baseEnd_6246066 := by
    simpa [prefixWord, tailWord_6246066, baseEnd_6246066] using wordTrace_append hprefix tailTrace_6246066
  have hstable : (prefixWord ++ tailWord_6246066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246066).length < 2 ^ (prefixWord ++ tailWord_6246066).sum := by decide
  have hdescent : baseEnd_6246066 < baseStart_6246066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246073 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6246073 : Nat := 118140960795 + 6246073 * 2 ^ 59
def prefixEnd_6246073 : Nat := 4983230072969 + 3 ^ 40 * 6246073 * 2
def baseEnd_6246073 : Nat := 3207237652070445944362339

theorem tailTrace_6246073 : CollatzResearch.WordTrace tailWord_6246073 prefixEnd_6246073 3207237652070445944362339 := by
  unfold tailWord_6246073
  simp only [CollatzResearch.WordTrace]
  refine ⟨227812997900551740185654873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151875331933701160123769915 227812997900551740185654873)
  ·
    refine ⟨170859748425413805139241155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227812997900551740185654873 170859748425413805139241155)
    ·
      refine ⟨256289622638120707708861733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170859748425413805139241155 256289622638120707708861733)
      ·
        refine ⟨48054304244647632695411575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256289622638120707708861733 48054304244647632695411575)
        ·
          refine ⟨72081456366971449043117363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48054304244647632695411575 72081456366971449043117363)
          ·
            refine ⟨108122184550457173564676045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72081456366971449043117363 108122184550457173564676045)
            ·
              refine ⟨40545819206421440086753517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108122184550457173564676045 40545819206421440086753517)
              ·
                refine ⟨15204682202408040032532569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40545819206421440086753517 15204682202408040032532569)
                ·
                  refine ⟨11403511651806030024399427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15204682202408040032532569 11403511651806030024399427)
                  ·
                    refine ⟨17105267477709045036599141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11403511651806030024399427 17105267477709045036599141)
                    ·
                      refine ⟨3207237652070445944362339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17105267477709045036599141 3207237652070445944362339)
                      ·
                        rfl

theorem cell23_6246073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6246073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246073 prefixEnd_6246073 := by exact prefixLift 6246073
  have htrace : WordTrace (prefixWord ++ tailWord_6246073) baseStart_6246073 baseEnd_6246073 := by
    simpa [prefixWord, tailWord_6246073, baseEnd_6246073] using wordTrace_append hprefix tailTrace_6246073
  have hstable : (prefixWord ++ tailWord_6246073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246073).length < 2 ^ (prefixWord ++ tailWord_6246073).sum := by decide
  have hdescent : baseEnd_6246073 < baseStart_6246073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246134 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6246134 : Nat := 118140960795 + 6246134 * 2 ^ 59
def prefixEnd_6246134 : Nat := 4983230072969 + 3 ^ 40 * 6246134 * 2
def baseEnd_6246134 : Nat := 1069089658130123401899853

theorem tailTrace_6246134 : CollatzResearch.WordTrace tailWord_6246134 prefixEnd_6246134 1069089658130123401899853 := by
  unfold tailWord_6246134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14238451422083171725226591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151876815168887165069083637 14238451422083171725226591)
  ·
    refine ⟨21357677133124757587839887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14238451422083171725226591 21357677133124757587839887)
    ·
      refine ⟨32036515699687136381759831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21357677133124757587839887 32036515699687136381759831)
      ·
        refine ⟨48054773549530704572639747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32036515699687136381759831 48054773549530704572639747)
        ·
          refine ⟨72082160324296056858959621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48054773549530704572639747 72082160324296056858959621)
          ·
            refine ⟨13515405060805510661054929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72082160324296056858959621 13515405060805510661054929)
            ·
              refine ⟨10136553795604132995791197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13515405060805510661054929 10136553795604132995791197)
              ·
                refine ⟨3801207673351549873421699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10136553795604132995791197 3801207673351549873421699)
                ·
                  refine ⟨5701811510027324810132549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801207673351549873421699 5701811510027324810132549)
                  ·
                    refine ⟨1069089658130123401899853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701811510027324810132549 1069089658130123401899853)
                    ·
                      rfl

theorem cell23_6246134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6246134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246134 prefixEnd_6246134 := by exact prefixLift 6246134
  have htrace : WordTrace (prefixWord ++ tailWord_6246134) baseStart_6246134 baseEnd_6246134 := by
    simpa [prefixWord, tailWord_6246134, baseEnd_6246134] using wordTrace_append hprefix tailTrace_6246134
  have hstable : (prefixWord ++ tailWord_6246134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246134).length < 2 ^ (prefixWord ++ tailWord_6246134).sum := by decide
  have hdescent : baseEnd_6246134 < baseStart_6246134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246140 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_6246140 : Nat := 118140960795 + 6246140 * 2 ^ 59
def prefixEnd_6246140 : Nat := 4983230072969 + 3 ^ 40 * 6246140 * 2
def baseEnd_6246140 : Nat := 3207272055274297182224531

theorem tailTrace_6246140 : CollatzResearch.WordTrace tailWord_6246140 prefixEnd_6246140 3207272055274297182224531 := by
  unfold tailWord_6246140
  simp only [CollatzResearch.WordTrace]
  refine ⟨113907720795654505314171937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151876961060872673752229249 113907720795654505314171937)
  ·
    refine ⟨85430790596740878985628953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113907720795654505314171937 85430790596740878985628953)
    ·
      refine ⟨64073092947555659239221715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85430790596740878985628953 64073092947555659239221715)
      ·
        refine ⟨96109639421333488858832573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64073092947555659239221715 96109639421333488858832573)
        ·
          refine ⟨36041114783000058322062215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96109639421333488858832573 36041114783000058322062215)
          ·
            refine ⟨54061672174500087483093323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36041114783000058322062215 54061672174500087483093323)
            ·
              refine ⟨81092508261750131224639985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54061672174500087483093323 81092508261750131224639985)
              ·
                refine ⟨60819381196312598418479989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81092508261750131224639985 60819381196312598418479989)
                ·
                  refine ⟨5701816987154306101732499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60819381196312598418479989 5701816987154306101732499)
                  ·
                    refine ⟨8552725480731459152598749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5701816987154306101732499 8552725480731459152598749)
                    ·
                      refine ⟨3207272055274297182224531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8552725480731459152598749 3207272055274297182224531)
                      ·
                        rfl

theorem cell23_6246140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_6246140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246140 prefixEnd_6246140 := by exact prefixLift 6246140
  have htrace : WordTrace (prefixWord ++ tailWord_6246140) baseStart_6246140 baseEnd_6246140 := by
    simpa [prefixWord, tailWord_6246140, baseEnd_6246140] using wordTrace_append hprefix tailTrace_6246140
  have hstable : (prefixWord ++ tailWord_6246140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246140).length < 2 ^ (prefixWord ++ tailWord_6246140).sum := by decide
  have hdescent : baseEnd_6246140 < baseStart_6246140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246163 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4]
def baseStart_6246163 : Nat := 118140960795 + 6246163 * 2 ^ 59
def prefixEnd_6246163 : Nat := 4983230072969 + 3 ^ 40 * 6246163 * 2
def baseEnd_6246163 : Nat := 3207283865329350592236925

theorem tailTrace_6246163 : CollatzResearch.WordTrace tailWord_6246163 prefixEnd_6246163 3207283865329350592236925 := by
  unfold tailWord_6246163
  simp only [CollatzResearch.WordTrace]
  refine ⟨227816280470225685556431143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151877520313483790370954095 227816280470225685556431143)
  ·
    refine ⟨341724420705338528334646715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227816280470225685556431143 341724420705338528334646715)
    ·
      refine ⟨512586631058007792501970073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341724420705338528334646715 512586631058007792501970073)
      ·
        refine ⟨384439973293505844376477555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512586631058007792501970073 384439973293505844376477555)
        ·
          refine ⟨576659959940258766564716333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384439973293505844376477555 576659959940258766564716333)
          ·
            refine ⟨216247484977597037461768625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576659959940258766564716333 216247484977597037461768625)
            ·
              refine ⟨162185613733197778096326469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216247484977597037461768625 162185613733197778096326469)
              ·
                refine ⟨30409802574974583393061213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162185613733197778096326469 30409802574974583393061213)
                ·
                  refine ⟨11403675965615468772397955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30409802574974583393061213 11403675965615468772397955)
                  ·
                    refine ⟨17105513948423203158596933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11403675965615468772397955 17105513948423203158596933)
                    ·
                      refine ⟨3207283865329350592236925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17105513948423203158596933 3207283865329350592236925)
                      ·
                        rfl

theorem cell23_6246163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_6246163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246163 prefixEnd_6246163 := by exact prefixLift 6246163
  have htrace : WordTrace (prefixWord ++ tailWord_6246163) baseStart_6246163 baseEnd_6246163 := by
    simpa [prefixWord, tailWord_6246163, baseEnd_6246163] using wordTrace_append hprefix tailTrace_6246163
  have hstable : (prefixWord ++ tailWord_6246163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246163).length < 2 ^ (prefixWord ++ tailWord_6246163).sum := by decide
  have hdescent : baseEnd_6246163 < baseStart_6246163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246200 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_6246200 : Nat := 118140960795 + 6246200 * 2 ^ 59
def prefixEnd_6246200 : Nat := 4983230072969 + 3 ^ 40 * 6246200 * 2
def baseEnd_6246200 : Nat := 3207302864113566947474255

theorem tailTrace_6246200 : CollatzResearch.WordTrace tailWord_6246200 prefixEnd_6246200 3207302864113566947474255 := by
  unfold tailWord_6246200
  simp only [CollatzResearch.WordTrace]
  refine ⟨113908814985545820437764027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151878419980727760583685369 113908814985545820437764027)
  ·
    refine ⟨170863222478318730656646041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113908814985545820437764027 170863222478318730656646041)
    ·
      refine ⟨128147416858739047992484531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170863222478318730656646041 128147416858739047992484531)
      ·
        refine ⟨192221125288108571988726797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128147416858739047992484531 192221125288108571988726797)
        ·
          refine ⟨72082921983040714495772549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192221125288108571988726797 72082921983040714495772549)
          ·
            refine ⟨13515547871820133967957353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72082921983040714495772549 13515547871820133967957353)
            ·
              refine ⟨10136660903865100475968015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13515547871820133967957353 10136660903865100475968015)
              ·
                refine ⟨15204991355797650713952023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136660903865100475968015 15204991355797650713952023)
                ·
                  refine ⟨22807487033696476070928035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15204991355797650713952023 22807487033696476070928035)
                  ·
                    refine ⟨34211230550544714106392053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22807487033696476070928035 34211230550544714106392053)
                    ·
                      refine ⟨3207302864113566947474255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34211230550544714106392053 3207302864113566947474255)
                      ·
                        rfl

theorem cell23_6246200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_6246200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246200 prefixEnd_6246200 := by exact prefixLift 6246200
  have htrace : WordTrace (prefixWord ++ tailWord_6246200) baseStart_6246200 baseEnd_6246200 := by
    simpa [prefixWord, tailWord_6246200, baseEnd_6246200] using wordTrace_append hprefix tailTrace_6246200
  have hstable : (prefixWord ++ tailWord_6246200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246200).length < 2 ^ (prefixWord ++ tailWord_6246200).sum := by decide
  have hdescent : baseEnd_6246200 < baseStart_6246200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246220 : List Nat := [2, 2, 1, 3, 4, 1, 2, 8]
def baseStart_6246220 : Nat := 118140960795 + 6246220 * 2 ^ 59
def prefixEnd_6246220 : Nat := 4983230072969 + 3 ^ 40 * 6246220 * 2
def baseEnd_6246220 : Nat := 118789375323209513674969

theorem tailTrace_6246220 : CollatzResearch.WordTrace tailWord_6246220 prefixEnd_6246220 118789375323209513674969 := by
  unfold tailWord_6246220
  simp only [CollatzResearch.WordTrace]
  refine ⟨113909179715509592145628057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151878906287346122860837409 113909179715509592145628057)
  ·
    refine ⟨85431884786632194109221043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113909179715509592145628057 85431884786632194109221043)
    ·
      refine ⟨128147827179948291163831565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85431884786632194109221043 128147827179948291163831565)
      ·
        refine ⟨48055435192480609186436837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128147827179948291163831565 48055435192480609186436837)
        ·
          refine ⟨9010394098590114222456907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48055435192480609186436837 9010394098590114222456907)
          ·
            refine ⟨13515591147885171333685361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9010394098590114222456907 13515591147885171333685361)
            ·
              refine ⟨10136693360913878500264021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13515591147885171333685361 10136693360913878500264021)
              ·
                refine ⟨118789375323209513674969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10136693360913878500264021 118789375323209513674969)
                ·
                  rfl

theorem cell23_6246220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 8].length) (baseStart_6246220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246220 prefixEnd_6246220 := by exact prefixLift 6246220
  have htrace : WordTrace (prefixWord ++ tailWord_6246220) baseStart_6246220 baseEnd_6246220 := by
    simpa [prefixWord, tailWord_6246220, baseEnd_6246220] using wordTrace_append hprefix tailTrace_6246220
  have hstable : (prefixWord ++ tailWord_6246220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246220).length < 2 ^ (prefixWord ++ tailWord_6246220).sum := by decide
  have hdescent : baseEnd_6246220 < baseStart_6246220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246321 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6246321 : Nat := 118140960795 + 6246321 * 2 ^ 59
def prefixEnd_6246321 : Nat := 4983230072969 + 3 ^ 40 * 6246321 * 2
def baseEnd_6246321 : Nat := 3207364995272760974061199

theorem tailTrace_6246321 : CollatzResearch.WordTrace tailWord_6246321 prefixEnd_6246321 3207364995272760974061199 := by
  unfold tailWord_6246321
  simp only [CollatzResearch.WordTrace]
  refine ⟨227822043203653278540682817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151881362135768852360455211 227822043203653278540682817)
  ·
    refine ⟨170866532402739958905512113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227822043203653278540682817 170866532402739958905512113)
    ·
      refine ⟨128149899302054969179134085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170866532402739958905512113 128149899302054969179134085)
      ·
        refine ⟨24028106119135306721087641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128149899302054969179134085 24028106119135306721087641)
        ·
          refine ⟨18021079589351480040815731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24028106119135306721087641 18021079589351480040815731)
          ·
            refine ⟨27031619384027220061223597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18021079589351480040815731 27031619384027220061223597)
            ·
              refine ⟨10136857269010207522958849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27031619384027220061223597 10136857269010207522958849)
              ·
                refine ⟨7602642951757655642219137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10136857269010207522958849 7602642951757655642219137)
                ·
                  refine ⟨5701982213818241731664353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7602642951757655642219137 5701982213818241731664353)
                  ·
                    refine ⟨4276486660363681298748265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5701982213818241731664353 4276486660363681298748265)
                    ·
                      refine ⟨3207364995272760974061199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276486660363681298748265 3207364995272760974061199)
                      ·
                        rfl

theorem cell23_6246321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6246321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246321 prefixEnd_6246321 := by exact prefixLift 6246321
  have htrace : WordTrace (prefixWord ++ tailWord_6246321) baseStart_6246321 baseEnd_6246321 := by
    simpa [prefixWord, tailWord_6246321, baseEnd_6246321] using wordTrace_append hprefix tailTrace_6246321
  have hstable : (prefixWord ++ tailWord_6246321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246321).length < 2 ^ (prefixWord ++ tailWord_6246321).sum := by decide
  have hdescent : baseEnd_6246321 < baseStart_6246321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246360 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6246360 : Nat := 118140960795 + 6246360 * 2 ^ 59
def prefixEnd_6246360 : Nat := 4983230072969 + 3 ^ 40 * 6246360 * 2
def baseEnd_6246360 : Nat := 3207385021018286321473519

theorem tailTrace_6246360 : CollatzResearch.WordTrace tailWord_6246360 prefixEnd_6246360 3207385021018286321473519 := by
  unfold tailWord_6246360
  simp only [CollatzResearch.WordTrace]
  refine ⟨113911732825255994100676267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151882310433674658800901689 113911732825255994100676267)
  ·
    refine ⟨170867599237883991151014401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113911732825255994100676267 170867599237883991151014401)
    ·
      refine ⟨128150699428412993363260801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170867599237883991151014401 128150699428412993363260801)
      ·
        refine ⟨96113024571309745022445601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128150699428412993363260801 96113024571309745022445601)
        ·
          refine ⟨72084768428482308766834201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96113024571309745022445601 72084768428482308766834201)
          ·
            refine ⟨54063576321361731575125651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72084768428482308766834201 54063576321361731575125651)
            ·
              refine ⟨81095364482042597362688477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54063576321361731575125651 81095364482042597362688477)
              ·
                refine ⟨30410761680765974011008179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81095364482042597362688477 30410761680765974011008179)
                ·
                  refine ⟨45616142521148961016512269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30410761680765974011008179 45616142521148961016512269)
                  ·
                    refine ⟨17106053445430860381192101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45616142521148961016512269 17106053445430860381192101)
                    ·
                      refine ⟨3207385021018286321473519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17106053445430860381192101 3207385021018286321473519)
                      ·
                        rfl

theorem cell23_6246360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6246360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246360 prefixEnd_6246360 := by exact prefixLift 6246360
  have htrace : WordTrace (prefixWord ++ tailWord_6246360) baseStart_6246360 baseEnd_6246360 := by
    simpa [prefixWord, tailWord_6246360, baseEnd_6246360] using wordTrace_append hprefix tailTrace_6246360
  have hstable : (prefixWord ++ tailWord_6246360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246360).length < 2 ^ (prefixWord ++ tailWord_6246360).sum := by decide
  have hdescent : baseEnd_6246360 < baseStart_6246360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246361 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 5]
def baseStart_6246361 : Nat := 118140960795 + 6246361 * 2 ^ 59
def prefixEnd_6246361 : Nat := 4983230072969 + 3 ^ 40 * 6246361 * 2
def baseEnd_6246361 : Nat := 356376170499882313062335

theorem tailTrace_6246361 : CollatzResearch.WordTrace tailWord_6246361 prefixEnd_6246361 356376170499882313062335 := by
  unfold tailWord_6246361
  simp only [CollatzResearch.WordTrace]
  refine ⟨227823502123508365372138937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151882334749005576914759291 227823502123508365372138937)
  ·
    refine ⟨170867626592631274029104203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227823502123508365372138937 170867626592631274029104203)
    ·
      refine ⟨256301439888946911043656305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170867626592631274029104203 256301439888946911043656305)
      ·
        refine ⟨192226079916710183282742229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256301439888946911043656305 192226079916710183282742229)
        ·
          refine ⟨4505298748047894920689271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 192226079916710183282742229 4505298748047894920689271)
          ·
            refine ⟨6757948122071842381033907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505298748047894920689271 6757948122071842381033907)
            ·
              refine ⟨10136922183107763571550861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757948122071842381033907 10136922183107763571550861)
              ·
                refine ⟨3801345818665411339331573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10136922183107763571550861 3801345818665411339331573)
                ·
                  refine ⟨356376170499882313062335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3801345818665411339331573 356376170499882313062335)
                  ·
                    rfl

theorem cell23_6246361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 5].length) (baseStart_6246361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246361 prefixEnd_6246361 := by exact prefixLift 6246361
  have htrace : WordTrace (prefixWord ++ tailWord_6246361) baseStart_6246361 baseEnd_6246361 := by
    simpa [prefixWord, tailWord_6246361, baseEnd_6246361] using wordTrace_append hprefix tailTrace_6246361
  have hstable : (prefixWord ++ tailWord_6246361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246361).length < 2 ^ (prefixWord ++ tailWord_6246361).sum := by decide
  have hdescent : baseEnd_6246361 < baseStart_6246361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246414 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6246414 : Nat := 118140960795 + 6246414 * 2 ^ 59
def prefixEnd_6246414 : Nat := 4983230072969 + 3 ^ 40 * 6246414 * 2
def baseEnd_6246414 : Nat := 3207412748973629110198271

theorem tailTrace_6246414 : CollatzResearch.WordTrace tailWord_6246414 prefixEnd_6246414 3207412748973629110198271 := by
  unfold tailWord_6246414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28478179399039544427977287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151883623461544236949212197 28478179399039544427977287)
  ·
    refine ⟨42717269098559316641965931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28478179399039544427977287 42717269098559316641965931)
    ·
      refine ⟨64075903647838974962948897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42717269098559316641965931 64075903647838974962948897)
      ·
        refine ⟨48056927735879231222211673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64075903647838974962948897 48056927735879231222211673)
        ·
          refine ⟨36042695801909423416658755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48056927735879231222211673 36042695801909423416658755)
          ·
            refine ⟨54064043702864135124988133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36042695801909423416658755 54064043702864135124988133)
            ·
              refine ⟨10137008194287025335935275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54064043702864135124988133 10137008194287025335935275)
              ·
                refine ⟨15205512291430538003902913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137008194287025335935275 15205512291430538003902913)
                ·
                  refine ⟨11404134218572903502927185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15205512291430538003902913 11404134218572903502927185)
                  ·
                    refine ⟨8553100663929677627195389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11404134218572903502927185 8553100663929677627195389)
                    ·
                      refine ⟨3207412748973629110198271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553100663929677627195389 3207412748973629110198271)
                      ·
                        rfl

theorem cell23_6246414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6246414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246414 prefixEnd_6246414 := by exact prefixLift 6246414
  have htrace : WordTrace (prefixWord ++ tailWord_6246414) baseStart_6246414 baseEnd_6246414 := by
    simpa [prefixWord, tailWord_6246414, baseEnd_6246414] using wordTrace_append hprefix tailTrace_6246414
  have hstable : (prefixWord ++ tailWord_6246414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246414).length < 2 ^ (prefixWord ++ tailWord_6246414).sum := by decide
  have hdescent : baseEnd_6246414 < baseStart_6246414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246427 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 3]
def baseStart_6246427 : Nat := 118140960795 + 6246427 * 2 ^ 59
def prefixEnd_6246427 : Nat := 4983230072969 + 3 ^ 40 * 6246427 * 2
def baseEnd_6246427 : Nat := 3207419424222137559335711

theorem tailTrace_6246427 : CollatzResearch.WordTrace tailWord_6246427 prefixEnd_6246427 3207419424222137559335711 := by
  unfold tailWord_6246427
  simp only [CollatzResearch.WordTrace]
  refine ⟨227825909341269258644041535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151883939560846172429361023 227825909341269258644041535)
  ·
    refine ⟨341738864011903887966062303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227825909341269258644041535 341738864011903887966062303)
    ·
      refine ⟨512608296017855831949093455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341738864011903887966062303 512608296017855831949093455)
      ·
        refine ⟨768912444026783747923640183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512608296017855831949093455 768912444026783747923640183)
        ·
          refine ⟨1153368666040175621885460275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768912444026783747923640183 1153368666040175621885460275)
          ·
            refine ⟨1730052999060263432828190413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153368666040175621885460275 1730052999060263432828190413)
            ·
              refine ⟨648769874647598787310571405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730052999060263432828190413 648769874647598787310571405)
              ·
                refine ⟨243288702992849545241464277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648769874647598787310571405 243288702992849545241464277)
                ·
                  refine ⟨5702078976394911216596819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 243288702992849545241464277 5702078976394911216596819)
                  ·
                    refine ⟨8553118464592366824895229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702078976394911216596819 8553118464592366824895229)
                    ·
                      refine ⟨3207419424222137559335711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553118464592366824895229 3207419424222137559335711)
                      ·
                        rfl

theorem cell23_6246427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 3].length) (baseStart_6246427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246427 prefixEnd_6246427 := by exact prefixLift 6246427
  have htrace : WordTrace (prefixWord ++ tailWord_6246427) baseStart_6246427 baseEnd_6246427 := by
    simpa [prefixWord, tailWord_6246427, baseEnd_6246427] using wordTrace_append hprefix tailTrace_6246427
  have hstable : (prefixWord ++ tailWord_6246427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246427).length < 2 ^ (prefixWord ++ tailWord_6246427).sum := by decide
  have hdescent : baseEnd_6246427 < baseStart_6246427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246467 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 8, 2]
def baseStart_6246467 : Nat := 118140960795 + 6246467 * 2 ^ 59
def prefixEnd_6246467 : Nat := 4983230072969 + 3 ^ 40 * 6246467 * 2
def baseEnd_6246467 : Nat := 3207439963448317402835527

theorem tailTrace_6246467 : CollatzResearch.WordTrace tailWord_6246467 prefixEnd_6246467 3207439963448317402835527 := by
  unfold tailWord_6246467
  simp only [CollatzResearch.WordTrace]
  refine ⟨227827368261124345475497655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151884912174082896983665103 227827368261124345475497655)
  ·
    refine ⟨341741052391686518213246483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227827368261124345475497655 341741052391686518213246483)
    ·
      refine ⟨512611578587529777319869725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341741052391686518213246483 512611578587529777319869725)
      ·
        refine ⟨192229341970323666494951147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512611578587529777319869725 192229341970323666494951147)
        ·
          refine ⟨288344012955485499742426721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192229341970323666494951147 288344012955485499742426721)
          ·
            refine ⟨216258009716614124806820041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288344012955485499742426721 216258009716614124806820041)
            ·
              refine ⟨162193507287460593605115031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216258009716614124806820041 162193507287460593605115031)
              ·
                refine ⟨243290260931190890407672547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162193507287460593605115031 243290260931190890407672547)
                ·
                  refine ⟨364935391396786335611508821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243290260931190890407672547 364935391396786335611508821)
                  ·
                    refine ⟨4276586617931089870447369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 364935391396786335611508821 4276586617931089870447369)
                    ·
                      refine ⟨3207439963448317402835527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276586617931089870447369 3207439963448317402835527)
                      ·
                        rfl

theorem cell23_6246467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_6246467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246467 prefixEnd_6246467 := by exact prefixLift 6246467
  have htrace : WordTrace (prefixWord ++ tailWord_6246467) baseStart_6246467 baseEnd_6246467 := by
    simpa [prefixWord, tailWord_6246467, baseEnd_6246467] using wordTrace_append hprefix tailTrace_6246467
  have hstable : (prefixWord ++ tailWord_6246467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246467).length < 2 ^ (prefixWord ++ tailWord_6246467).sum := by decide
  have hdescent : baseEnd_6246467 < baseStart_6246467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246478 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_6246478 : Nat := 118140960795 + 6246478 * 2 ^ 59
def prefixEnd_6246478 : Nat := 4983230072969 + 3 ^ 40 * 6246478 * 2
def baseEnd_6246478 : Nat := 3207445611735516859797977

theorem tailTrace_6246478 : CollatzResearch.WordTrace tailWord_6246478 prefixEnd_6246478 3207445611735516859797977 := by
  unfold tailWord_6246478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28478471183010561794268511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151885179642722996236098725 28478471183010561794268511)
  ·
    refine ⟨42717706774515842691402767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28478471183010561794268511 42717706774515842691402767)
    ·
      refine ⟨64076560161773764037104151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42717706774515842691402767 64076560161773764037104151)
      ·
        refine ⟨96114840242660646055656227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64076560161773764037104151 96114840242660646055656227)
        ·
          refine ⟨144172260363990969083484341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96114840242660646055656227 144172260363990969083484341)
          ·
            refine ⟨13516149409124153351576657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144172260363990969083484341 13516149409124153351576657)
            ·
              refine ⟨10137112056843115013682493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13516149409124153351576657 10137112056843115013682493)
              ·
                refine ⟨3801417021316168130130935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10137112056843115013682493 3801417021316168130130935)
                ·
                  refine ⟨5702125531974252195196403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801417021316168130130935 5702125531974252195196403)
                  ·
                    refine ⟨8553188297961378292794605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702125531974252195196403 8553188297961378292794605)
                    ·
                      refine ⟨3207445611735516859797977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553188297961378292794605 3207445611735516859797977)
                      ·
                        rfl

theorem cell23_6246478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_6246478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246478 prefixEnd_6246478 := by exact prefixLift 6246478
  have htrace : WordTrace (prefixWord ++ tailWord_6246478) baseStart_6246478 baseEnd_6246478 := by
    simpa [prefixWord, tailWord_6246478, baseEnd_6246478] using wordTrace_append hprefix tailTrace_6246478
  have hstable : (prefixWord ++ tailWord_6246478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246478).length < 2 ^ (prefixWord ++ tailWord_6246478).sum := by decide
  have hdescent : baseEnd_6246478 < baseStart_6246478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246480 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_6246480 : Nat := 118140960795 + 6246480 * 2 ^ 59
def prefixEnd_6246480 : Nat := 4983230072969 + 3 ^ 40 * 6246480 * 2
def baseEnd_6246480 : Nat := 3207446638696825851972967

theorem tailTrace_6246480 : CollatzResearch.WordTrace tailWord_6246480 prefixEnd_6246480 3207446638696825851972967 := by
  unfold tailWord_6246480
  simp only [CollatzResearch.WordTrace]
  refine ⟨113913921205038624347860447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151885228273384832463813929 113913921205038624347860447)
  ·
    refine ⟨170870881807557936521790671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113913921205038624347860447 170870881807557936521790671)
    ·
      refine ⟨256306322711336904782686007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170870881807557936521790671 256306322711336904782686007)
      ·
        refine ⟨384459484067005357174029011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256306322711336904782686007 384459484067005357174029011)
        ·
          refine ⟨576689226100508035761043517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384459484067005357174029011 576689226100508035761043517)
          ·
            refine ⟨216258459787690513410391319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576689226100508035761043517 216258459787690513410391319)
            ·
              refine ⟨324387689681535770115586979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216258459787690513410391319 324387689681535770115586979)
              ·
                refine ⟨486581534522303655173380469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324387689681535770115586979 486581534522303655173380469)
                ·
                  refine ⟨45617018861465967672504419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 486581534522303655173380469 45617018861465967672504419)
                  ·
                    refine ⟨68425528292198951508756629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45617018861465967672504419 68425528292198951508756629)
                    ·
                      refine ⟨3207446638696825851972967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68425528292198951508756629 3207446638696825851972967)
                      ·
                        rfl

theorem cell23_6246480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_6246480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246480 prefixEnd_6246480 := by exact prefixLift 6246480
  have htrace : WordTrace (prefixWord ++ tailWord_6246480) baseStart_6246480 baseEnd_6246480 := by
    simpa [prefixWord, tailWord_6246480, baseEnd_6246480] using wordTrace_append hprefix tailTrace_6246480
  have hstable : (prefixWord ++ tailWord_6246480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246480).length < 2 ^ (prefixWord ++ tailWord_6246480).sum := by decide
  have hdescent : baseEnd_6246480 < baseStart_6246480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246490 : List Nat := [3, 1, 1, 2, 1, 1, 14]
def baseStart_6246490 : Nat := 118140960795 + 6246490 * 2 ^ 59
def prefixEnd_6246490 : Nat := 4983230072969 + 3 ^ 40 * 6246490 * 2
def baseEnd_6246490 : Nat := 39598170043251491516641

theorem tailTrace_6246490 : CollatzResearch.WordTrace tailWord_6246490 prefixEnd_6246490 39598170043251491516641 := by
  unfold tailWord_6246490
  simp only [CollatzResearch.WordTrace]
  refine ⟨56957051785010255100896231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151885471426694013602389949 56957051785010255100896231)
  ·
    refine ⟨85435577677515382651344347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56957051785010255100896231 85435577677515382651344347)
    ·
      refine ⟨128153366516273073977016521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85435577677515382651344347 128153366516273073977016521)
      ·
        refine ⟨96115024887204805482762391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128153366516273073977016521 96115024887204805482762391)
        ·
          refine ⟨144172537330807208224143587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96115024887204805482762391 144172537330807208224143587)
          ·
            refine ⟨216258805996210812336215381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144172537330807208224143587 216258805996210812336215381)
            ·
              refine ⟨39598170043251491516641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 216258805996210812336215381 39598170043251491516641)
              ·
                rfl

theorem cell23_6246490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 14].length) (baseStart_6246490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246490 prefixEnd_6246490 := by exact prefixLift 6246490
  have htrace : WordTrace (prefixWord ++ tailWord_6246490) baseStart_6246490 baseEnd_6246490 := by
    simpa [prefixWord, tailWord_6246490, baseEnd_6246490] using wordTrace_append hprefix tailTrace_6246490
  have hstable : (prefixWord ++ tailWord_6246490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246490).length < 2 ^ (prefixWord ++ tailWord_6246490).sum := by decide
  have hdescent : baseEnd_6246490 < baseStart_6246490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246501 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_6246501 : Nat := 118140960795 + 6246501 * 2 ^ 59
def prefixEnd_6246501 : Nat := 4983230072969 + 3 ^ 40 * 6246501 * 2
def baseEnd_6246501 : Nat := 3207457421790570269810371

theorem tailTrace_6246501 : CollatzResearch.WordTrace tailWord_6246501 prefixEnd_6246501 3207457421790570269810371 := by
  unfold tailWord_6246501
  simp only [CollatzResearch.WordTrace]
  refine ⟨227828608343001169282235357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151885738895334112854823571 227828608343001169282235357)
  ·
    refine ⟨85435728128625438480838259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227828608343001169282235357 85435728128625438480838259)
    ·
      refine ⟨128153592192938157721257389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85435728128625438480838259 128153592192938157721257389)
      ·
        refine ⟨48057597072351809145471521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128153592192938157721257389 48057597072351809145471521)
        ·
          refine ⟨36043197804263856859103641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48057597072351809145471521 36043197804263856859103641)
          ·
            refine ⟨27032398353197892644327731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36043197804263856859103641 27032398353197892644327731)
            ·
              refine ⟨40548597529796838966491597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27032398353197892644327731 40548597529796838966491597)
              ·
                refine ⟨15205724073673814612434349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40548597529796838966491597 15205724073673814612434349)
                ·
                  refine ⟨5702146527627680479662881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15205724073673814612434349 5702146527627680479662881)
                  ·
                    refine ⟨4276609895720760359747161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5702146527627680479662881 4276609895720760359747161)
                    ·
                      refine ⟨3207457421790570269810371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276609895720760359747161 3207457421790570269810371)
                      ·
                        rfl

theorem cell23_6246501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_6246501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246501 prefixEnd_6246501 := by exact prefixLift 6246501
  have htrace : WordTrace (prefixWord ++ tailWord_6246501) baseStart_6246501 baseEnd_6246501 := by
    simpa [prefixWord, tailWord_6246501, baseEnd_6246501] using wordTrace_append hprefix tailTrace_6246501
  have hstable : (prefixWord ++ tailWord_6246501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246501).length < 2 ^ (prefixWord ++ tailWord_6246501).sum := by decide
  have hdescent : baseEnd_6246501 < baseStart_6246501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246511 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 2, 4]
def baseStart_6246511 : Nat := 118140960795 + 6246511 * 2 ^ 59
def prefixEnd_6246511 : Nat := 4983230072969 + 3 ^ 40 * 6246511 * 2
def baseEnd_6246511 : Nat := 1069154185532371743561775

theorem tailTrace_6246511 : CollatzResearch.WordTrace tailWord_6246511 prefixEnd_6246511 1069154185532371743561775 := by
  unfold tailWord_6246511
  simp only [CollatzResearch.WordTrace]
  refine ⟨227828973072964940990099387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151885982048643293993399591 227828973072964940990099387)
  ·
    refine ⟨341743459609447411485149081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227828973072964940990099387 341743459609447411485149081)
    ·
      refine ⟨256307594707085558613861811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341743459609447411485149081 256307594707085558613861811)
      ·
        refine ⟨384461392060628337920792717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256307594707085558613861811 384461392060628337920792717)
        ·
          refine ⟨144173022022735626720297269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384461392060628337920792717 144173022022735626720297269)
          ·
            refine ⟨13516220814631465005027869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144173022022735626720297269 13516220814631465005027869)
            ·
              refine ⟨5068582805486799376885451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13516220814631465005027869 5068582805486799376885451)
              ·
                refine ⟨7602874208230199065328177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5068582805486799376885451 7602874208230199065328177)
                ·
                  refine ⟨5702155656172649298996133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7602874208230199065328177 5702155656172649298996133)
                  ·
                    refine ⟨1069154185532371743561775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702155656172649298996133 1069154185532371743561775)
                    ·
                      rfl

theorem cell23_6246511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_6246511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246511 prefixEnd_6246511 := by exact prefixLift 6246511
  have htrace : WordTrace (prefixWord ++ tailWord_6246511) baseStart_6246511 baseEnd_6246511 := by
    simpa [prefixWord, tailWord_6246511, baseEnd_6246511] using wordTrace_append hprefix tailTrace_6246511
  have hstable : (prefixWord ++ tailWord_6246511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246511).length < 2 ^ (prefixWord ++ tailWord_6246511).sum := by decide
  have hdescent : baseEnd_6246511 < baseStart_6246511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246514 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6246514 : Nat := 118140960795 + 6246514 * 2 ^ 59
def prefixEnd_6246514 : Nat := 4983230072969 + 3 ^ 40 * 6246514 * 2
def baseEnd_6246514 : Nat := 3207464097039078718947811

theorem tailTrace_6246514 : CollatzResearch.WordTrace tailWord_6246514 prefixEnd_6246514 3207464097039078718947811 := by
  unfold tailWord_6246514
  simp only [CollatzResearch.WordTrace]
  refine ⟨56957270622988518125614649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151886054994636048334972397 56957270622988518125614649)
  ·
    refine ⟨42717952967241388594210987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56957270622988518125614649 42717952967241388594210987)
    ·
      refine ⟨64076929450862082891316481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42717952967241388594210987 64076929450862082891316481)
      ·
        refine ⟨48057697088146562168487361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64076929450862082891316481 48057697088146562168487361)
        ·
          refine ⟨36043272816109921626365521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48057697088146562168487361 36043272816109921626365521)
          ·
            refine ⟨27032454612082441219774141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36043272816109921626365521 27032454612082441219774141)
            ·
              refine ⟨10137170479530915457415303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27032454612082441219774141 10137170479530915457415303)
              ·
                refine ⟨15205755719296373186122955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137170479530915457415303 15205755719296373186122955)
                ·
                  refine ⟨22808633578944559779184433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15205755719296373186122955 22808633578944559779184433)
                  ·
                    refine ⟨17106475184208419834388325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22808633578944559779184433 17106475184208419834388325)
                    ·
                      refine ⟨3207464097039078718947811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17106475184208419834388325 3207464097039078718947811)
                      ·
                        rfl

theorem cell23_6246514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6246514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246514 prefixEnd_6246514 := by exact prefixLift 6246514
  have htrace : WordTrace (prefixWord ++ tailWord_6246514) baseStart_6246514 baseEnd_6246514 := by
    simpa [prefixWord, tailWord_6246514, baseEnd_6246514] using wordTrace_append hprefix tailTrace_6246514
  have hstable : (prefixWord ++ tailWord_6246514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246514).length < 2 ^ (prefixWord ++ tailWord_6246514).sum := by decide
  have hdescent : baseEnd_6246514 < baseStart_6246514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246518 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6246518 : Nat := 118140960795 + 6246518 * 2 ^ 59
def prefixEnd_6246518 : Nat := 4983230072969 + 3 ^ 40 * 6246518 * 2
def baseEnd_6246518 : Nat := 3207466150961696703297793

theorem tailTrace_6246518 : CollatzResearch.WordTrace tailWord_6246518 prefixEnd_6246518 3207466150961696703297793 := by
  unfold tailWord_6246518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14239326773996223824100263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151886152255959720790402805 14239326773996223824100263)
  ·
    refine ⟨21358990160994335736150395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14239326773996223824100263 21358990160994335736150395)
    ·
      refine ⟨32038485241491503604225593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21358990160994335736150395 32038485241491503604225593)
      ·
        refine ⟨24028863931118627703169195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32038485241491503604225593 24028863931118627703169195)
        ·
          refine ⟨36043295896677941554753793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24028863931118627703169195 36043295896677941554753793)
          ·
            refine ⟨27032471922508456166065345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36043295896677941554753793 27032471922508456166065345)
            ·
              refine ⟨20274353941881342124549009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27032471922508456166065345 20274353941881342124549009)
              ·
                refine ⟨15205765456411006593411757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20274353941881342124549009 15205765456411006593411757)
                ·
                  refine ⟨5702162046154127472529409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15205765456411006593411757 5702162046154127472529409)
                  ·
                    refine ⟨4276621534615595604397057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5702162046154127472529409 4276621534615595604397057)
                    ·
                      refine ⟨3207466150961696703297793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276621534615595604397057 3207466150961696703297793)
                      ·
                        rfl

theorem cell23_6246518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6246518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246518 prefixEnd_6246518 := by exact prefixLift 6246518
  have htrace : WordTrace (prefixWord ++ tailWord_6246518) baseStart_6246518 baseEnd_6246518 := by
    simpa [prefixWord, tailWord_6246518, baseEnd_6246518] using wordTrace_append hprefix tailTrace_6246518
  have hstable : (prefixWord ++ tailWord_6246518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246518).length < 2 ^ (prefixWord ++ tailWord_6246518).sum := by decide
  have hdescent : baseEnd_6246518 < baseStart_6246518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246521 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_6246521 : Nat := 118140960795 + 6246521 * 2 ^ 59
def prefixEnd_6246521 : Nat := 4983230072969 + 3 ^ 40 * 6246521 * 2
def baseEnd_6246521 : Nat := 3207467691403660191560279

theorem tailTrace_6246521 : CollatzResearch.WordTrace tailWord_6246521 prefixEnd_6246521 3207467691403660191560279 := by
  unfold tailWord_6246521
  simp only [CollatzResearch.WordTrace]
  refine ⟨227829337802928712697963417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151886225201952475131975611 227829337802928712697963417)
  ·
    refine ⟨170872003352196534523472563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227829337802928712697963417 170872003352196534523472563)
    ·
      refine ⟨256308005028294801785208845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170872003352196534523472563 256308005028294801785208845)
      ·
        refine ⟨96115501885610550669453317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256308005028294801785208845 96115501885610550669453317)
        ·
          refine ⟨18021656603551978250522497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96115501885610550669453317 18021656603551978250522497)
          ·
            refine ⟨13516242452663983687891873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18021656603551978250522497 13516242452663983687891873)
            ·
              refine ⟨10137181839497987765918905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13516242452663983687891873 10137181839497987765918905)
              ·
                refine ⟨7602886379623490824439179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10137181839497987765918905 7602886379623490824439179)
                ·
                  refine ⟨11404329569435236236658769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7602886379623490824439179 11404329569435236236658769)
                  ·
                    refine ⟨8553247177076427177494077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11404329569435236236658769 8553247177076427177494077)
                    ·
                      refine ⟨3207467691403660191560279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553247177076427177494077 3207467691403660191560279)
                      ·
                        rfl

theorem cell23_6246521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_6246521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246521 prefixEnd_6246521 := by exact prefixLift 6246521
  have htrace : WordTrace (prefixWord ++ tailWord_6246521) baseStart_6246521 baseEnd_6246521 := by
    simpa [prefixWord, tailWord_6246521, baseEnd_6246521] using wordTrace_append hprefix tailTrace_6246521
  have hstable : (prefixWord ++ tailWord_6246521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246521).length < 2 ^ (prefixWord ++ tailWord_6246521).sum := by decide
  have hdescent : baseEnd_6246521 < baseStart_6246521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246524 : List Nat := [2, 2, 2, 1, 1, 6, 2, 7]
def baseStart_6246524 : Nat := 118140960795 + 6246524 * 2 ^ 59
def prefixEnd_6246524 : Nat := 4983230072969 + 3 ^ 40 * 6246524 * 2
def baseEnd_6246524 : Nat := 118795156735023099252695

theorem tailTrace_6246524 : CollatzResearch.WordTrace tailWord_6246524 prefixEnd_6246524 118795156735023099252695 := by
  unfold tailWord_6246524
  simp only [CollatzResearch.WordTrace]
  refine ⟨113914723610958922105161313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151886298147945229473548417 113914723610958922105161313)
  ·
    refine ⟨85436042708219191578870985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113914723610958922105161313 85436042708219191578870985)
    ·
      refine ⟨64077032031164393684153239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85436042708219191578870985 64077032031164393684153239)
      ·
        refine ⟨96115548046746590526229859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64077032031164393684153239 96115548046746590526229859)
        ·
          refine ⟨144173322070119885789344789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96115548046746590526229859 144173322070119885789344789)
          ·
            refine ⟨6758124472036869646375537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144173322070119885789344789 6758124472036869646375537)
            ·
              refine ⟨5068593354027652234781653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6758124472036869646375537 5068593354027652234781653)
              ·
                refine ⟨118795156735023099252695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5068593354027652234781653 118795156735023099252695)
                ·
                  rfl

theorem cell23_6246524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 7].length) (baseStart_6246524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246524 prefixEnd_6246524 := by exact prefixLift 6246524
  have htrace : WordTrace (prefixWord ++ tailWord_6246524) baseStart_6246524 baseEnd_6246524 := by
    simpa [prefixWord, tailWord_6246524, baseEnd_6246524] using wordTrace_append hprefix tailTrace_6246524
  have hstable : (prefixWord ++ tailWord_6246524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246524).length < 2 ^ (prefixWord ++ tailWord_6246524).sum := by decide
  have hdescent : baseEnd_6246524 < baseStart_6246524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246552 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6246552 : Nat := 118140960795 + 6246552 * 2 ^ 59
def prefixEnd_6246552 : Nat := 4983230072969 + 3 ^ 40 * 6246552 * 2
def baseEnd_6246552 : Nat := 3207483609303949570272637

theorem tailTrace_6246552 : CollatzResearch.WordTrace tailWord_6246552 prefixEnd_6246552 3207483609303949570272637 := by
  unfold tailWord_6246552
  simp only [CollatzResearch.WordTrace]
  refine ⟨113915234232908202496170955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151886978977210936661561273 113915234232908202496170955)
  ·
    refine ⟨170872851349362303744256433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113915234232908202496170955 170872851349362303744256433)
    ·
      refine ⟨128154638512021727808192325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170872851349362303744256433 128154638512021727808192325)
      ·
        refine ⟨24028994721004073964036061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128154638512021727808192325 24028994721004073964036061)
        ·
          refine ⟨9010873020376527736513523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24028994721004073964036061 9010873020376527736513523)
          ·
            refine ⟨13516309530564791604770285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9010873020376527736513523 13516309530564791604770285)
            ·
              refine ⟨5068616073961796851788857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13516309530564791604770285 5068616073961796851788857)
              ·
                refine ⟨3801462055471347638841643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068616073961796851788857 3801462055471347638841643)
                ·
                  refine ⟨5702193083207021458262465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801462055471347638841643 5702193083207021458262465)
                  ·
                    refine ⟨4276644812405266093696849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5702193083207021458262465 4276644812405266093696849)
                    ·
                      refine ⟨3207483609303949570272637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276644812405266093696849 3207483609303949570272637)
                      ·
                        rfl

theorem cell23_6246552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6246552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246552 prefixEnd_6246552 := by exact prefixLift 6246552
  have htrace : WordTrace (prefixWord ++ tailWord_6246552) baseStart_6246552 baseEnd_6246552 := by
    simpa [prefixWord, tailWord_6246552, baseEnd_6246552] using wordTrace_append hprefix tailTrace_6246552
  have hstable : (prefixWord ++ tailWord_6246552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246552).length < 2 ^ (prefixWord ++ tailWord_6246552).sum := by decide
  have hdescent : baseEnd_6246552 < baseStart_6246552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246621 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6246621 : Nat := 118140960795 + 6246621 * 2 ^ 59
def prefixEnd_6246621 : Nat := 4983230072969 + 3 ^ 40 * 6246621 * 2
def baseEnd_6246621 : Nat := 3207519039469109800309819

theorem tailTrace_6246621 : CollatzResearch.WordTrace tailWord_6246621 prefixEnd_6246621 3207519039469109800309819 := by
  unfold tailWord_6246621
  simp only [CollatzResearch.WordTrace]
  refine ⟨227832985102566429776603717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151888656735044286517735811 227832985102566429776603717)
  ·
    refine ⟨42718684706731205583113197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227832985102566429776603717 42718684706731205583113197)
    ·
      refine ⟨16019506765024202093667449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42718684706731205583113197 16019506765024202093667449)
      ·
        refine ⟨12014630073768151570250587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16019506765024202093667449 12014630073768151570250587)
        ·
          refine ⟨18021945110652227355375881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12014630073768151570250587 18021945110652227355375881)
          ·
            refine ⟨13516458832989170516531911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18021945110652227355375881 13516458832989170516531911)
            ·
              refine ⟨20274688249483755774797867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13516458832989170516531911 20274688249483755774797867)
              ·
                refine ⟨30412032374225633662196801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20274688249483755774797867 30412032374225633662196801)
                ·
                  refine ⟨22809024280669225246647601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30412032374225633662196801 22809024280669225246647601)
                  ·
                    refine ⟨17106768210501918934985701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22809024280669225246647601 17106768210501918934985701)
                    ·
                      refine ⟨3207519039469109800309819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17106768210501918934985701 3207519039469109800309819)
                      ·
                        rfl

theorem cell23_6246621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6246621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246621 prefixEnd_6246621 := by exact prefixLift 6246621
  have htrace : WordTrace (prefixWord ++ tailWord_6246621) baseStart_6246621 baseEnd_6246621 := by
    simpa [prefixWord, tailWord_6246621, baseEnd_6246621] using wordTrace_append hprefix tailTrace_6246621
  have hstable : (prefixWord ++ tailWord_6246621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246621).length < 2 ^ (prefixWord ++ tailWord_6246621).sum := by decide
  have hdescent : baseEnd_6246621 < baseStart_6246621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246624 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_6246624 : Nat := 118140960795 + 6246624 * 2 ^ 59
def prefixEnd_6246624 : Nat := 4983230072969 + 3 ^ 40 * 6246624 * 2
def baseEnd_6246624 : Nat := 3207520579911073288572305

theorem tailTrace_6246624 : CollatzResearch.WordTrace tailWord_6246624 prefixEnd_6246624 3207520579911073288572305 := by
  unfold tailWord_6246624
  simp only [CollatzResearch.WordTrace]
  refine ⟨113916547260777780644481463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151888729681037040859308617 113916547260777780644481463)
  ·
    refine ⟨170874820891166670966722195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113916547260777780644481463 170874820891166670966722195)
    ·
      refine ⟨256312231336750006450083293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170874820891166670966722195 256312231336750006450083293)
      ·
        refine ⟨96117086751281252418781235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256312231336750006450083293 96117086751281252418781235)
        ·
          refine ⟨144175630126921878628171853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96117086751281252418781235 144175630126921878628171853)
          ·
            refine ⟨54065861297595704485564445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144175630126921878628171853 54065861297595704485564445)
            ·
              refine ⟨20274697986598389182086667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54065861297595704485564445 20274697986598389182086667)
              ·
                refine ⟨30412046979897583773130001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20274697986598389182086667 30412046979897583773130001)
                ·
                  refine ⟨22809035234923187829847501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30412046979897583773130001 22809035234923187829847501)
                  ·
                    refine ⟨8553388213096195436192813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22809035234923187829847501 8553388213096195436192813)
                    ·
                      refine ⟨3207520579911073288572305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553388213096195436192813 3207520579911073288572305)
                      ·
                        rfl

theorem cell23_6246624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_6246624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246624 prefixEnd_6246624 := by exact prefixLift 6246624
  have htrace : WordTrace (prefixWord ++ tailWord_6246624) baseStart_6246624 baseEnd_6246624 := by
    simpa [prefixWord, tailWord_6246624, baseEnd_6246624] using wordTrace_append hprefix tailTrace_6246624
  have hstable : (prefixWord ++ tailWord_6246624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246624).length < 2 ^ (prefixWord ++ tailWord_6246624).sum := by decide
  have hdescent : baseEnd_6246624 < baseStart_6246624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246718 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_6246718 : Nat := 118140960795 + 6246718 * 2 ^ 59
def prefixEnd_6246718 : Nat := 4983230072969 + 3 ^ 40 * 6246718 * 2
def baseEnd_6246718 : Nat := 3207568847092595920796873

theorem tailTrace_6246718 : CollatzResearch.WordTrace tailWord_6246718 prefixEnd_6246718 3207568847092595920796873 := by
  unfold tailWord_6246718
  simp only [CollatzResearch.WordTrace]
  refine ⟨28479565372901876917860601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151891015322143343561923205 28479565372901876917860601)
  ·
    refine ⟨21359674029676407688395451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28479565372901876917860601 21359674029676407688395451)
    ·
      refine ⟨32039511044514611532593177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21359674029676407688395451 32039511044514611532593177)
      ·
        refine ⟨24029633283385958649444883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32039511044514611532593177 24029633283385958649444883)
        ·
          refine ⟨36044449925078937974167325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24029633283385958649444883 36044449925078937974167325)
          ·
            refine ⟨13516668721904601740312747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36044449925078937974167325 13516668721904601740312747)
            ·
              refine ⟨20275003082856902610469121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13516668721904601740312747 20275003082856902610469121)
              ·
                refine ⟨15206252312142676957851841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20275003082856902610469121 15206252312142676957851841)
                ·
                  refine ⟨11404689234107007718388881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15206252312142676957851841 11404689234107007718388881)
                  ·
                    refine ⟨8553516925580255788791661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11404689234107007718388881 8553516925580255788791661)
                    ·
                      refine ⟨3207568847092595920796873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553516925580255788791661 3207568847092595920796873)
                      ·
                        rfl

theorem cell23_6246718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_6246718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246718 prefixEnd_6246718 := by exact prefixLift 6246718
  have htrace : WordTrace (prefixWord ++ tailWord_6246718) baseStart_6246718 baseEnd_6246718 := by
    simpa [prefixWord, tailWord_6246718, baseEnd_6246718] using wordTrace_append hprefix tailTrace_6246718
  have hstable : (prefixWord ++ tailWord_6246718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246718).length < 2 ^ (prefixWord ++ tailWord_6246718).sum := by decide
  have hdescent : baseEnd_6246718 < baseStart_6246718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246731 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 3]
def baseStart_6246731 : Nat := 118140960795 + 6246731 * 2 ^ 59
def prefixEnd_6246731 : Nat := 4983230072969 + 3 ^ 40 * 6246731 * 2
def baseEnd_6246731 : Nat := 3207575522341104369934313

theorem tailTrace_6246731 : CollatzResearch.WordTrace tailWord_6246731 prefixEnd_6246731 3207575522341104369934313 := by
  unfold tailWord_6246731
  simp only [CollatzResearch.WordTrace]
  refine ⟨227836997132167918563108047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151891331421445279042072031 227836997132167918563108047)
  ·
    refine ⟨341755495698251877844662071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227836997132167918563108047 341755495698251877844662071)
    ·
      refine ⟨512633243547377816766993107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341755495698251877844662071 512633243547377816766993107)
      ·
        refine ⟨768949865321066725150489661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512633243547377816766993107 768949865321066725150489661)
        ·
          refine ⟨288356199495400021931433623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768949865321066725150489661 288356199495400021931433623)
          ·
            refine ⟨432534299243100032897150435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288356199495400021931433623 432534299243100032897150435)
            ·
              refine ⟨648801448864650049345725653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432534299243100032897150435 648801448864650049345725653)
              ·
                refine ⟨15206283957765235531540445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 648801448864650049345725653 15206283957765235531540445)
                ·
                  refine ⟨5702356484161963324327667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15206283957765235531540445 5702356484161963324327667)
                  ·
                    refine ⟨8553534726242944986491501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702356484161963324327667 8553534726242944986491501)
                    ·
                      refine ⟨3207575522341104369934313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553534726242944986491501 3207575522341104369934313)
                      ·
                        rfl

theorem cell23_6246731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 3].length) (baseStart_6246731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246731 prefixEnd_6246731 := by exact prefixLift 6246731
  have htrace : WordTrace (prefixWord ++ tailWord_6246731) baseStart_6246731 baseEnd_6246731 := by
    simpa [prefixWord, tailWord_6246731, baseEnd_6246731] using wordTrace_append hprefix tailTrace_6246731
  have hstable : (prefixWord ++ tailWord_6246731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246731).length < 2 ^ (prefixWord ++ tailWord_6246731).sum := by decide
  have hdescent : baseEnd_6246731 < baseStart_6246731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246751 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 1, 5]
def baseStart_6246751 : Nat := 118140960795 + 6246751 * 2 ^ 59
def prefixEnd_6246751 : Nat := 4983230072969 + 3 ^ 40 * 6246751 * 2
def baseEnd_6246751 : Nat := 1069195263984731430561407

theorem tailTrace_6246751 : CollatzResearch.WordTrace tailWord_6246751 prefixEnd_6246751 1069195263984731430561407 := by
  unfold tailWord_6246751
  simp only [CollatzResearch.WordTrace]
  refine ⟨227837726592095461978836107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151891817728063641319224071 227837726592095461978836107)
  ·
    refine ⟨341756589888143192968254161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227837726592095461978836107 341756589888143192968254161)
    ·
      refine ⟨256317442416107394726190621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341756589888143192968254161 256317442416107394726190621)
      ·
        refine ⟨96119040906040273022321483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256317442416107394726190621 96119040906040273022321483)
        ·
          refine ⟨144178561359060409533482225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96119040906040273022321483 144178561359060409533482225)
          ·
            refine ⟨108133921019295307150111669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144178561359060409533482225 108133921019295307150111669)
            ·
              refine ⟨10137555095558935045322969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108133921019295307150111669 10137555095558935045322969)
              ·
                refine ⟨7603166321669201283992227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10137555095558935045322969 7603166321669201283992227)
                ·
                  refine ⟨11404749482503801925988341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7603166321669201283992227 11404749482503801925988341)
                  ·
                    refine ⟨1069195263984731430561407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11404749482503801925988341 1069195263984731430561407)
                    ·
                      rfl

theorem cell23_6246751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_6246751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246751 prefixEnd_6246751 := by exact prefixLift 6246751
  have htrace : WordTrace (prefixWord ++ tailWord_6246751) baseStart_6246751 baseEnd_6246751 := by
    simpa [prefixWord, tailWord_6246751, baseEnd_6246751] using wordTrace_append hprefix tailTrace_6246751
  have hstable : (prefixWord ++ tailWord_6246751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246751).length < 2 ^ (prefixWord ++ tailWord_6246751).sum := by decide
  have hdescent : baseEnd_6246751 < baseStart_6246751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246765 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6246765 : Nat := 118140960795 + 6246765 * 2 ^ 59
def prefixEnd_6246765 : Nat := 4983230072969 + 3 ^ 40 * 6246765 * 2
def baseEnd_6246765 : Nat := 3207592980683357236909157

theorem tailTrace_6246765 : CollatzResearch.WordTrace tailWord_6246765 prefixEnd_6246765 3207592980683357236909157 := by
  unfold tailWord_6246765
  simp only [CollatzResearch.WordTrace]
  refine ⟨227838237214044742369845749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151892158142696494913230499 227838237214044742369845749)
  ·
    refine ⟨21359834738816694597173039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227838237214044742369845749 21359834738816694597173039)
    ·
      refine ⟨32039752108225041895759559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21359834738816694597173039 32039752108225041895759559)
      ·
        refine ⟨48059628162337562843639339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32039752108225041895759559 48059628162337562843639339)
        ·
          refine ⟨72089442243506344265459009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48059628162337562843639339 72089442243506344265459009)
          ·
            refine ⟨54067081682629758199094257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72089442243506344265459009 54067081682629758199094257)
            ·
              refine ⟨40550311261972318649320693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54067081682629758199094257 40550311261972318649320693)
              ·
                refine ⟨3801591680809904873373815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40550311261972318649320693 3801591680809904873373815)
                ·
                  refine ⟨5702387521214857310060723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801591680809904873373815 5702387521214857310060723)
                  ·
                    refine ⟨8553581281822285965091085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702387521214857310060723 8553581281822285965091085)
                    ·
                      refine ⟨3207592980683357236909157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553581281822285965091085 3207592980683357236909157)
                      ·
                        rfl

theorem cell23_6246765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6246765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246765 prefixEnd_6246765 := by exact prefixLift 6246765
  have htrace : WordTrace (prefixWord ++ tailWord_6246765) baseStart_6246765 baseEnd_6246765 := by
    simpa [prefixWord, tailWord_6246765, baseEnd_6246765] using wordTrace_append hprefix tailTrace_6246765
  have hstable : (prefixWord ++ tailWord_6246765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246765).length < 2 ^ (prefixWord ++ tailWord_6246765).sum := by decide
  have hdescent : baseEnd_6246765 < baseStart_6246765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246768 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 1, 5]
def baseStart_6246768 : Nat := 118140960795 + 6246768 * 2 ^ 59
def prefixEnd_6246768 : Nat := 4983230072969 + 3 ^ 40 * 6246768 * 2
def baseEnd_6246768 : Nat := 1069198173708440241723881

theorem tailTrace_6246768 : CollatzResearch.WordTrace tailWord_6246768 prefixEnd_6246768 1069198173708440241723881 := by
  unfold tailWord_6246768
  simp only [CollatzResearch.WordTrace]
  refine ⟨113919173316516936941102479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151892231088689249254803305 113919173316516936941102479)
  ·
    refine ⟨170878759974775405411653719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113919173316516936941102479 170878759974775405411653719)
    ·
      refine ⟨256318139962163108117480579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170878759974775405411653719 256318139962163108117480579)
      ·
        refine ⟨384477209943244662176220869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256318139962163108117480579 384477209943244662176220869)
        ·
          refine ⟨72089476864358374158041413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384477209943244662176220869 72089476864358374158041413)
          ·
            refine ⟨13516776912067195154632765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72089476864358374158041413 13516776912067195154632765)
            ·
              refine ⟨5068791342025198182987287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13516776912067195154632765 5068791342025198182987287)
              ·
                refine ⟨7603187013037797274480931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5068791342025198182987287 7603187013037797274480931)
                ·
                  refine ⟨11404780519556695911721397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7603187013037797274480931 11404780519556695911721397)
                  ·
                    refine ⟨1069198173708440241723881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11404780519556695911721397 1069198173708440241723881)
                    ·
                      rfl

theorem cell23_6246768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_6246768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246768 prefixEnd_6246768 := by exact prefixLift 6246768
  have htrace : WordTrace (prefixWord ++ tailWord_6246768) baseStart_6246768 baseEnd_6246768 := by
    simpa [prefixWord, tailWord_6246768, baseEnd_6246768] using wordTrace_append hprefix tailTrace_6246768
  have hstable : (prefixWord ++ tailWord_6246768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246768).length < 2 ^ (prefixWord ++ tailWord_6246768).sum := by decide
  have hdescent : baseEnd_6246768 < baseStart_6246768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246791 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_6246791 : Nat := 118140960795 + 6246791 * 2 ^ 59
def prefixEnd_6246791 : Nat := 4983230072969 + 3 ^ 40 * 6246791 * 2
def baseEnd_6246791 : Nat := 3207606331180374135184037

theorem tailTrace_6246791 : CollatzResearch.WordTrace tailWord_6246791 prefixEnd_6246791 3207606331180374135184037 := by
  unfold tailWord_6246791
  simp only [CollatzResearch.WordTrace]
  refine ⟨227839185511950548810292227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151892790341300365873528151 227839185511950548810292227)
  ·
    refine ⟨341758778267925823215438341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227839185511950548810292227 341758778267925823215438341)
    ·
      refine ⟨64079770925236091852894689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341758778267925823215438341 64079770925236091852894689)
      ·
        refine ⟨48059828193927068889671017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64079770925236091852894689 48059828193927068889671017)
        ·
          refine ⟨36044871145445301667253263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48059828193927068889671017 36044871145445301667253263)
          ·
            refine ⟨54067306718167952500879895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36044871145445301667253263 54067306718167952500879895)
            ·
              refine ⟨81100960077251928751319843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54067306718167952500879895 81100960077251928751319843)
              ·
                refine ⟨121651440115877893126979765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81100960077251928751319843 121651440115877893126979765)
                ·
                  refine ⟨11404822510863552480654353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121651440115877893126979765 11404822510863552480654353)
                  ·
                    refine ⟨8553616883147664360490765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11404822510863552480654353 8553616883147664360490765)
                    ·
                      refine ⟨3207606331180374135184037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553616883147664360490765 3207606331180374135184037)
                      ·
                        rfl

theorem cell23_6246791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_6246791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246791 prefixEnd_6246791 := by exact prefixLift 6246791
  have htrace : WordTrace (prefixWord ++ tailWord_6246791) baseStart_6246791 baseEnd_6246791 := by
    simpa [prefixWord, tailWord_6246791, baseEnd_6246791] using wordTrace_append hprefix tailTrace_6246791
  have hstable : (prefixWord ++ tailWord_6246791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246791).length < 2 ^ (prefixWord ++ tailWord_6246791).sum := by decide
  have hdescent : baseEnd_6246791 < baseStart_6246791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246798 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_6246798 : Nat := 118140960795 + 6246798 * 2 ^ 59
def prefixEnd_6246798 : Nat := 4983230072969 + 3 ^ 40 * 6246798 * 2
def baseEnd_6246798 : Nat := 1069203308514985202598835

theorem tailTrace_6246798 : CollatzResearch.WordTrace tailWord_6246798 prefixEnd_6246798 1069203308514985202598835 := by
  unfold tailWord_6246798
  simp only [CollatzResearch.WordTrace]
  refine ⟨28479930102865648625724631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151892960548616792670531365 28479930102865648625724631)
  ·
    refine ⟨42719895154298472938586947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28479930102865648625724631 42719895154298472938586947)
    ·
      refine ⟨64079842731447709407880421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42719895154298472938586947 64079842731447709407880421)
      ·
        refine ⟨12014970512146445513977579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64079842731447709407880421 12014970512146445513977579)
        ·
          refine ⟨18022455768219668270966369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12014970512146445513977579 18022455768219668270966369)
          ·
            refine ⟨13516841826164751203224777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18022455768219668270966369 13516841826164751203224777)
            ·
              refine ⟨10137631369623563402418583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13516841826164751203224777 10137631369623563402418583)
              ·
                refine ⟨15206447054435345103627875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137631369623563402418583 15206447054435345103627875)
                ·
                  refine ⟨22809670581653017655441813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15206447054435345103627875 22809670581653017655441813)
                  ·
                    refine ⟨1069203308514985202598835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22809670581653017655441813 1069203308514985202598835)
                    ·
                      rfl

theorem cell23_6246798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_6246798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246798 prefixEnd_6246798 := by exact prefixLift 6246798
  have htrace : WordTrace (prefixWord ++ tailWord_6246798) baseStart_6246798 baseEnd_6246798 := by
    simpa [prefixWord, tailWord_6246798, baseEnd_6246798] using wordTrace_append hprefix tailTrace_6246798
  have hstable : (prefixWord ++ tailWord_6246798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246798).length < 2 ^ (prefixWord ++ tailWord_6246798).sum := by decide
  have hdescent : baseEnd_6246798 < baseStart_6246798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246808 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6246808 : Nat := 118140960795 + 6246808 * 2 ^ 59
def prefixEnd_6246808 : Nat := 4983230072969 + 3 ^ 40 * 6246808 * 2
def baseEnd_6246808 : Nat := 3207615060351500568671459

theorem tailTrace_6246808 : CollatzResearch.WordTrace tailWord_6246808 prefixEnd_6246808 3207615060351500568671459 := by
  unfold tailWord_6246808
  simp only [CollatzResearch.WordTrace]
  refine ⟨113919902776444480356830539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151893203701925973809107385 113919902776444480356830539)
  ·
    refine ⟨170879854164666720535245809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113919902776444480356830539 170879854164666720535245809)
    ·
      refine ⟨128159890623500040401434357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170879854164666720535245809 128159890623500040401434357)
      ·
        refine ⟨12014989745953128787634471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128159890623500040401434357 12014989745953128787634471)
        ·
          refine ⟨18022484618929693181451707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12014989745953128787634471 18022484618929693181451707)
          ·
            refine ⟨27033726928394539772177561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18022484618929693181451707 27033726928394539772177561)
            ·
              refine ⟨20275295196295904829133171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27033726928394539772177561 20275295196295904829133171)
              ·
                refine ⟨30412942794443857243699757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20275295196295904829133171 30412942794443857243699757)
                ·
                  refine ⟨11404853547916446466387409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30412942794443857243699757 11404853547916446466387409)
                  ·
                    refine ⟨8553640160937334849790557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11404853547916446466387409 8553640160937334849790557)
                    ·
                      refine ⟨3207615060351500568671459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553640160937334849790557 3207615060351500568671459)
                      ·
                        rfl

theorem cell23_6246808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6246808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246808 prefixEnd_6246808 := by exact prefixLift 6246808
  have htrace : WordTrace (prefixWord ++ tailWord_6246808) baseStart_6246808 baseEnd_6246808 := by
    simpa [prefixWord, tailWord_6246808, baseEnd_6246808] using wordTrace_append hprefix tailTrace_6246808
  have hstable : (prefixWord ++ tailWord_6246808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246808).length < 2 ^ (prefixWord ++ tailWord_6246808).sum := by decide
  have hdescent : baseEnd_6246808 < baseStart_6246808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246821 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_6246821 : Nat := 118140960795 + 6246821 * 2 ^ 59
def prefixEnd_6246821 : Nat := 4983230072969 + 3 ^ 40 * 6246821 * 2
def baseEnd_6246821 : Nat := 3207621735600009017808899

theorem tailTrace_6246821 : CollatzResearch.WordTrace tailWord_6246821 prefixEnd_6246821 3207621735600009017808899 := by
  unfold tailWord_6246821
  simp only [CollatzResearch.WordTrace]
  refine ⟨227840279701841863933884317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151893519801227909289256211 227840279701841863933884317)
  ·
    refine ⟨85440104888190698975206619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227840279701841863933884317 85440104888190698975206619)
    ·
      refine ⟨128160157332286048462809929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85440104888190698975206619 128160157332286048462809929)
      ·
        refine ⟨96120117999214536347107447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128160157332286048462809929 96120117999214536347107447)
        ·
          refine ⟨144180176998821804520661171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96120117999214536347107447 144180176998821804520661171)
          ·
            refine ⟨216270265498232706780991757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144180176998821804520661171 216270265498232706780991757)
            ·
              refine ⟨81101349561837265042871909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216270265498232706780991757 81101349561837265042871909)
              ·
                refine ⟨15206503042844487195538483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81101349561837265042871909 15206503042844487195538483)
                ·
                  refine ⟨22809754564266730793307725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15206503042844487195538483 22809754564266730793307725)
                  ·
                    refine ⟨8553657961600024047490397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22809754564266730793307725 8553657961600024047490397)
                    ·
                      refine ⟨3207621735600009017808899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553657961600024047490397 3207621735600009017808899)
                      ·
                        rfl

theorem cell23_6246821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_6246821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246821 prefixEnd_6246821 := by exact prefixLift 6246821
  have htrace : WordTrace (prefixWord ++ tailWord_6246821) baseStart_6246821 baseEnd_6246821 := by
    simpa [prefixWord, tailWord_6246821, baseEnd_6246821] using wordTrace_append hprefix tailTrace_6246821
  have hstable : (prefixWord ++ tailWord_6246821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246821).length < 2 ^ (prefixWord ++ tailWord_6246821).sum := by decide
  have hdescent : baseEnd_6246821 < baseStart_6246821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246849 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6246849 : Nat := 118140960795 + 6246849 * 2 ^ 59
def prefixEnd_6246849 : Nat := 4983230072969 + 3 ^ 40 * 6246849 * 2
def baseEnd_6246849 : Nat := 1069212037686111636086257

theorem tailTrace_6246849 : CollatzResearch.WordTrace tailWord_6246849 prefixEnd_6246849 1069212037686111636086257 := by
  unfold tailWord_6246849
  simp only [CollatzResearch.WordTrace]
  refine ⟨227841300945740424715903601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151894200630493616477269067 227841300945740424715903601)
  ·
    refine ⟨170880975709305318536927701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227841300945740424715903601 170880975709305318536927701)
    ·
      refine ⟨4005022868186843403209243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 170880975709305318536927701 4005022868186843403209243)
      ·
        refine ⟨6007534302280265104813865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005022868186843403209243 6007534302280265104813865)
        ·
          refine ⟨4505650726710198828610399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6007534302280265104813865 4505650726710198828610399)
          ·
            refine ⟨6758476090065298242915599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505650726710198828610399 6758476090065298242915599)
            ·
              refine ⟨10137714135097947364373399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758476090065298242915599 10137714135097947364373399)
              ·
                refine ⟨15206571202646921046560099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137714135097947364373399 15206571202646921046560099)
                ·
                  refine ⟨22809856803970381569840149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15206571202646921046560099 22809856803970381569840149)
                  ·
                    refine ⟨1069212037686111636086257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22809856803970381569840149 1069212037686111636086257)
                    ·
                      rfl

theorem cell23_6246849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6246849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246849 prefixEnd_6246849 := by exact prefixLift 6246849
  have htrace : WordTrace (prefixWord ++ tailWord_6246849) baseStart_6246849 baseEnd_6246849 := by
    simpa [prefixWord, tailWord_6246849, baseEnd_6246849] using wordTrace_append hprefix tailTrace_6246849
  have hstable : (prefixWord ++ tailWord_6246849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246849).length < 2 ^ (prefixWord ++ tailWord_6246849).sum := by decide
  have hdescent : baseEnd_6246849 < baseStart_6246849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246852 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6246852 : Nat := 118140960795 + 6246852 * 2 ^ 59
def prefixEnd_6246852 : Nat := 4983230072969 + 3 ^ 40 * 6246852 * 2
def baseEnd_6246852 : Nat := 3207637653500298396521257

theorem tailTrace_6246852 : CollatzResearch.WordTrace tailWord_6246852 prefixEnd_6246852 3207637653500298396521257 := by
  unfold tailWord_6246852
  simp only [CollatzResearch.WordTrace]
  refine ⟨113920705182364778114131405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151894273576486370818841873 113920705182364778114131405)
  ·
    refine ⟨42720264443386791792799277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113920705182364778114131405 42720264443386791792799277)
    ·
      refine ⟨16020099166270046922299729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42720264443386791792799277 16020099166270046922299729)
      ·
        refine ⟨12015074374702535191724797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16020099166270046922299729 12015074374702535191724797)
        ·
          refine ⟨4505652890513450696896799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12015074374702535191724797 4505652890513450696896799)
          ·
            refine ⟨6758479335770176045345199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505652890513450696896799 6758479335770176045345199)
            ·
              refine ⟨10137719003655264068017799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758479335770176045345199 10137719003655264068017799)
              ·
                refine ⟨15206578505482896102026699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137719003655264068017799 15206578505482896102026699)
                ·
                  refine ⟨22809867758224344153040049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15206578505482896102026699 22809867758224344153040049)
                  ·
                    refine ⟨17107400818668258114780037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22809867758224344153040049 17107400818668258114780037)
                    ·
                      refine ⟨3207637653500298396521257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17107400818668258114780037 3207637653500298396521257)
                      ·
                        rfl

theorem cell23_6246852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6246852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246852 prefixEnd_6246852 := by exact prefixLift 6246852
  have htrace : WordTrace (prefixWord ++ tailWord_6246852) baseStart_6246852 baseEnd_6246852 := by
    simpa [prefixWord, tailWord_6246852, baseEnd_6246852] using wordTrace_append hprefix tailTrace_6246852
  have hstable : (prefixWord ++ tailWord_6246852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246852).length < 2 ^ (prefixWord ++ tailWord_6246852).sum := by decide
  have hdescent : baseEnd_6246852 < baseStart_6246852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246881 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_6246881 : Nat := 118140960795 + 6246881 * 2 ^ 59
def prefixEnd_6246881 : Nat := 4983230072969 + 3 ^ 40 * 6246881 * 2
def baseEnd_6246881 : Nat := 3207652544439278783058623

theorem tailTrace_6246881 : CollatzResearch.WordTrace tailWord_6246881 prefixEnd_6246881 3207652544439278783058623 := by
  unfold tailWord_6246881
  simp only [CollatzResearch.WordTrace]
  refine ⟨227842468081624494181068497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151894978721082996120712331 227842468081624494181068497)
  ·
    refine ⟨170881851061218370635801373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227842468081624494181068497 170881851061218370635801373)
    ·
      refine ⟨64080694147956888988425515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170881851061218370635801373 64080694147956888988425515)
      ·
        refine ⟨96121041221935333482638273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64080694147956888988425515 96121041221935333482638273)
        ·
          refine ⟨72090780916451500111978705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96121041221935333482638273 72090780916451500111978705)
          ·
            refine ⟨54068085687338625083984029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72090780916451500111978705 54068085687338625083984029)
            ·
              refine ⟨20275532132751984406494011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54068085687338625083984029 20275532132751984406494011)
              ·
                refine ⟨30413298199127976609741017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20275532132751984406494011 30413298199127976609741017)
                ·
                  refine ⟨22809973649345982457305763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30413298199127976609741017 22809973649345982457305763)
                  ·
                    refine ⟨34214960474018973685958645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22809973649345982457305763 34214960474018973685958645)
                    ·
                      refine ⟨3207652544439278783058623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34214960474018973685958645 3207652544439278783058623)
                      ·
                        rfl

theorem cell23_6246881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_6246881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246881 prefixEnd_6246881 := by exact prefixLift 6246881
  have htrace : WordTrace (prefixWord ++ tailWord_6246881) baseStart_6246881 baseEnd_6246881 := by
    simpa [prefixWord, tailWord_6246881, baseEnd_6246881] using wordTrace_append hprefix tailTrace_6246881
  have hstable : (prefixWord ++ tailWord_6246881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246881).length < 2 ^ (prefixWord ++ tailWord_6246881).sum := by decide
  have hdescent : baseEnd_6246881 < baseStart_6246881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246895 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 2, 2, 2]
def baseStart_6246895 : Nat := 118140960795 + 6246895 * 2 ^ 59
def prefixEnd_6246895 : Nat := 4983230072969 + 3 ^ 40 * 6246895 * 2
def baseEnd_6246895 : Nat := 3207659733168441728283559

theorem tailTrace_6246895 : CollatzResearch.WordTrace tailWord_6246895 prefixEnd_6246895 3207659733168441728283559 := by
  unfold tailWord_6246895
  simp only [CollatzResearch.WordTrace]
  refine ⟨227842978703573774572078139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151895319135715849714718759 227842978703573774572078139)
  ·
    refine ⟨341764468055360661858117209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227842978703573774572078139 341764468055360661858117209)
    ·
      refine ⟨256323351041520496393587907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341764468055360661858117209 256323351041520496393587907)
      ·
        refine ⟨384485026562280744590381861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256323351041520496393587907 384485026562280744590381861)
        ·
          refine ⟨72090942480427639610696599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384485026562280744590381861 72090942480427639610696599)
          ·
            refine ⟨108136413720641459416044899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72090942480427639610696599 108136413720641459416044899)
            ·
              refine ⟨162204620580962189124067349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108136413720641459416044899 162204620580962189124067349)
              ·
                refine ⟨7603341589732602615190657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162204620580962189124067349 7603341589732602615190657)
                ·
                  refine ⟨5702506192299451961392993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7603341589732602615190657 5702506192299451961392993)
                  ·
                    refine ⟨4276879644224588971044745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5702506192299451961392993 4276879644224588971044745)
                    ·
                      refine ⟨3207659733168441728283559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276879644224588971044745 3207659733168441728283559)
                      ·
                        rfl

theorem cell23_6246895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2, 2].length) (baseStart_6246895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246895 prefixEnd_6246895 := by exact prefixLift 6246895
  have htrace : WordTrace (prefixWord ++ tailWord_6246895) baseStart_6246895 baseEnd_6246895 := by
    simpa [prefixWord, tailWord_6246895, baseEnd_6246895] using wordTrace_append hprefix tailTrace_6246895
  have hstable : (prefixWord ++ tailWord_6246895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246895).length < 2 ^ (prefixWord ++ tailWord_6246895).sum := by decide
  have hdescent : baseEnd_6246895 < baseStart_6246895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246911 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_6246911 : Nat := 118140960795 + 6246911 * 2 ^ 59
def prefixEnd_6246911 : Nat := 4983230072969 + 3 ^ 40 * 6246911 * 2
def baseEnd_6246911 : Nat := 3207667948858913665683485

theorem tailTrace_6246911 : CollatzResearch.WordTrace tailWord_6246911 prefixEnd_6246911 3207667948858913665683485 := by
  unfold tailWord_6246911
  simp only [CollatzResearch.WordTrace]
  refine ⟨227843562271515809304660587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151895708181010539536440391 227843562271515809304660587)
  ·
    refine ⟨341765343407273713956990881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227843562271515809304660587 341765343407273713956990881)
    ·
      refine ⟨256324007555455285467743161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341765343407273713956990881 256324007555455285467743161)
      ·
        refine ⟨192243005666591464100807371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256324007555455285467743161 192243005666591464100807371)
        ·
          refine ⟨288364508499887196151211057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192243005666591464100807371 288364508499887196151211057)
          ·
            refine ⟨216273381374915397113408293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288364508499887196151211057 216273381374915397113408293)
            ·
              refine ⟨40551259007796636958764055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216273381374915397113408293 40551259007796636958764055)
              ·
                refine ⟨60826888511694955438146083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40551259007796636958764055 60826888511694955438146083)
                ·
                  refine ⟨91240332767542433157219125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60826888511694955438146083 91240332767542433157219125)
                  ·
                    refine ⟨8553781196957103108489293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91240332767542433157219125 8553781196957103108489293)
                    ·
                      refine ⟨3207667948858913665683485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553781196957103108489293 3207667948858913665683485)
                      ·
                        rfl

theorem cell23_6246911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_6246911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246911 prefixEnd_6246911 := by exact prefixLift 6246911
  have htrace : WordTrace (prefixWord ++ tailWord_6246911) baseStart_6246911 baseEnd_6246911 := by
    simpa [prefixWord, tailWord_6246911, baseEnd_6246911] using wordTrace_append hprefix tailTrace_6246911
  have hstable : (prefixWord ++ tailWord_6246911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246911).length < 2 ^ (prefixWord ++ tailWord_6246911).sum := by decide
  have hdescent : baseEnd_6246911 < baseStart_6246911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246952 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 5]
def baseStart_6246952 : Nat := 118140960795 + 6246952 * 2 ^ 59
def prefixEnd_6246952 : Nat := 4983230072969 + 3 ^ 40 * 6246952 * 2
def baseEnd_6246952 : Nat := 356409889062860889474533

theorem tailTrace_6246952 : CollatzResearch.WordTrace tailWord_6246952 prefixEnd_6246952 356409889062860889474533 := by
  unfold tailWord_6246952
  simp only [CollatzResearch.WordTrace]
  refine ⟨113922528832183636653451555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151896705109578182204602073 113922528832183636653451555)
  ·
    refine ⟨170883793248275454980177333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113922528832183636653451555 170883793248275454980177333)
    ·
      refine ⟨16020355617025823904391625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170883793248275454980177333 16020355617025823904391625)
      ·
        refine ⟨12015266712769367928293719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16020355617025823904391625 12015266712769367928293719)
        ·
          refine ⟨18022900069154051892440579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015266712769367928293719 18022900069154051892440579)
          ·
            refine ⟨27034350103731077838660869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18022900069154051892440579 27034350103731077838660869)
            ·
              refine ⟨5068940644449577094748913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27034350103731077838660869 5068940644449577094748913)
              ·
                refine ⟨3801705483337182821061685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068940644449577094748913 3801705483337182821061685)
                ·
                  refine ⟨356409889062860889474533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3801705483337182821061685 356409889062860889474533)
                  ·
                    rfl

theorem cell23_6246952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 5].length) (baseStart_6246952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246952 prefixEnd_6246952 := by exact prefixLift 6246952
  have htrace : WordTrace (prefixWord ++ tailWord_6246952) baseStart_6246952 baseEnd_6246952 := by
    simpa [prefixWord, tailWord_6246952, baseEnd_6246952] using wordTrace_append hprefix tailTrace_6246952
  have hstable : (prefixWord ++ tailWord_6246952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246952).length < 2 ^ (prefixWord ++ tailWord_6246952).sum := by decide
  have hdescent : baseEnd_6246952 < baseStart_6246952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3]
def baseStart_6246971 : Nat := 118140960795 + 6246971 * 2 ^ 59
def prefixEnd_6246971 : Nat := 4983230072969 + 3 ^ 40 * 6246971 * 2
def baseEnd_6246971 : Nat := 3207698757698183430933209

theorem tailTrace_6246971 : CollatzResearch.WordTrace tailWord_6246971 prefixEnd_6246971 3207698757698183430933209 := by
  unfold tailWord_6246971
  simp only [CollatzResearch.WordTrace]
  refine ⟨227845750651298439551844767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151897167100865626367896511 227845750651298439551844767)
  ·
    refine ⟨341768625976947659327767151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227845750651298439551844767 341768625976947659327767151)
    ·
      refine ⟨512652938965421488991650727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341768625976947659327767151 512652938965421488991650727)
      ·
        refine ⟨768979408448132233487476091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512652938965421488991650727 768979408448132233487476091)
        ·
          refine ⟨1153469112672198350231214137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768979408448132233487476091 1153469112672198350231214137)
          ·
            refine ⟨865101834504148762673410603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153469112672198350231214137 865101834504148762673410603)
            ·
              refine ⟨1297652751756223144010115905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865101834504148762673410603 1297652751756223144010115905)
              ·
                refine ⟨973239563817167358007586929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297652751756223144010115905 973239563817167358007586929)
                ·
                  refine ⟨729929672862875518505690197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973239563817167358007586929 729929672862875518505690197)
                  ·
                    refine ⟨8553863353861822482488557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 729929672862875518505690197 8553863353861822482488557)
                    ·
                      refine ⟨3207698757698183430933209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553863353861822482488557 3207698757698183430933209)
                      ·
                        rfl

theorem cell23_6246971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 3].length) (baseStart_6246971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246971 prefixEnd_6246971 := by exact prefixLift 6246971
  have htrace : WordTrace (prefixWord ++ tailWord_6246971) baseStart_6246971 baseEnd_6246971 := by
    simpa [prefixWord, tailWord_6246971, baseEnd_6246971] using wordTrace_append hprefix tailTrace_6246971
  have hstable : (prefixWord ++ tailWord_6246971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246971).length < 2 ^ (prefixWord ++ tailWord_6246971).sum := by decide
  have hdescent : baseEnd_6246971 < baseStart_6246971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246982 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_6246982 : Nat := 118140960795 + 6246982 * 2 ^ 59
def prefixEnd_6246982 : Nat := 4983230072969 + 3 ^ 40 * 6246982 * 2
def baseEnd_6246982 : Nat := 1069234801995127629298553

theorem tailTrace_6246982 : CollatzResearch.WordTrace tailWord_6246982 prefixEnd_6246982 1069234801995127629298553 := by
  unfold tailWord_6246982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120192245445580888452975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151897434569505725620330133 7120192245445580888452975)
  ·
    refine ⟨10680288368168371332679463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7120192245445580888452975 10680288368168371332679463)
    ·
      refine ⟨16020432552252556999019195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10680288368168371332679463 16020432552252556999019195)
      ·
        refine ⟨24030648828378835498528793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16020432552252556999019195 24030648828378835498528793)
        ·
          refine ⟨18022986621284126623896595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24030648828378835498528793 18022986621284126623896595)
          ·
            refine ⟨27034479931926189935844893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18022986621284126623896595 27034479931926189935844893)
            ·
              refine ⟨10137929974472321225941835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27034479931926189935844893 10137929974472321225941835)
              ·
                refine ⟨15206894961708481838912753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137929974472321225941835 15206894961708481838912753)
                ·
                  refine ⟨11405171221281361379184565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15206894961708481838912753 11405171221281361379184565)
                  ·
                    refine ⟨1069234801995127629298553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11405171221281361379184565 1069234801995127629298553)
                    ·
                      rfl

theorem cell23_6246982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_6246982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246982 prefixEnd_6246982 := by exact prefixLift 6246982
  have htrace : WordTrace (prefixWord ++ tailWord_6246982) baseStart_6246982 baseEnd_6246982 := by
    simpa [prefixWord, tailWord_6246982, baseEnd_6246982] using wordTrace_append hprefix tailTrace_6246982
  have hstable : (prefixWord ++ tailWord_6246982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246982).length < 2 ^ (prefixWord ++ tailWord_6246982).sum := by decide
  have hdescent : baseEnd_6246982 < baseStart_6246982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246988 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6246988 : Nat := 118140960795 + 6246988 * 2 ^ 59
def prefixEnd_6246988 : Nat := 4983230072969 + 3 ^ 40 * 6246988 * 2
def baseEnd_6246988 : Nat := 3207707486869309864420631

theorem tailTrace_6246988 : CollatzResearch.WordTrace tailWord_6246988 prefixEnd_6246988 3207707486869309864420631 := by
  unfold tailWord_6246988
  simp only [CollatzResearch.WordTrace]
  refine ⟨113923185346118425727606809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151897580461491234303475745 113923185346118425727606809)
  ·
    refine ⟨85442389009588819295705107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113923185346118425727606809 85442389009588819295705107)
    ·
      refine ⟨128163583514383228943557661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85442389009588819295705107 128163583514383228943557661)
      ·
        refine ⟨48061343817893710853834123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128163583514383228943557661 48061343817893710853834123)
        ·
          refine ⟨72092015726840566280751185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48061343817893710853834123 72092015726840566280751185)
          ·
            refine ⟨54069011795130424710563389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72092015726840566280751185 54069011795130424710563389)
            ·
              refine ⟨20275879423173909266461271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54069011795130424710563389 20275879423173909266461271)
              ·
                refine ⟨30413819134760863899691907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20275879423173909266461271 30413819134760863899691907)
                ·
                  refine ⟨45620728702141295849537861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30413819134760863899691907 45620728702141295849537861)
                  ·
                    refine ⟨8553886631651492971788349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45620728702141295849537861 8553886631651492971788349)
                    ·
                      refine ⟨3207707486869309864420631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553886631651492971788349 3207707486869309864420631)
                      ·
                        rfl

theorem cell23_6246988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6246988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246988 prefixEnd_6246988 := by exact prefixLift 6246988
  have htrace : WordTrace (prefixWord ++ tailWord_6246988) baseStart_6246988 baseEnd_6246988 := by
    simpa [prefixWord, tailWord_6246988, baseEnd_6246988] using wordTrace_append hprefix tailTrace_6246988
  have hstable : (prefixWord ++ tailWord_6246988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246988).length < 2 ^ (prefixWord ++ tailWord_6246988).sum := by decide
  have hdescent : baseEnd_6246988 < baseStart_6246988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247008 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 6]
def baseStart_6247008 : Nat := 118140960795 + 6247008 * 2 ^ 59
def prefixEnd_6247008 : Nat := 4983230072969 + 3 ^ 40 * 6247008 * 2
def baseEnd_6247008 : Nat := 356413084053599976241171

theorem tailTrace_6247008 : CollatzResearch.WordTrace tailWord_6247008 prefixEnd_6247008 356413084053599976241171 := by
  unfold tailWord_6247008
  simp only [CollatzResearch.WordTrace]
  refine ⟨113923550076082197435470839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151898066768109596580627785 113923550076082197435470839)
  ·
    refine ⟨170885325114123296153206259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113923550076082197435470839 170885325114123296153206259)
    ·
      refine ⟨256327987671184944229809389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170885325114123296153206259 256327987671184944229809389)
      ·
        refine ⟨96122995376694354086178521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256327987671184944229809389 96122995376694354086178521)
        ·
          refine ⟨72092246532520765564633891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96122995376694354086178521 72092246532520765564633891)
          ·
            refine ⟨108138369798781148346950837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72092246532520765564633891 108138369798781148346950837)
            ·
              refine ⟨10137972168635732657526641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108138369798781148346950837 10137972168635732657526641)
              ·
                refine ⟨7603479126476799493144981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10137972168635732657526641 7603479126476799493144981)
                ·
                  refine ⟨356413084053599976241171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7603479126476799493144981 356413084053599976241171)
                  ·
                    rfl

theorem cell23_6247008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_6247008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247008 prefixEnd_6247008 := by exact prefixLift 6247008
  have htrace : WordTrace (prefixWord ++ tailWord_6247008) baseStart_6247008 baseEnd_6247008 := by
    simpa [prefixWord, tailWord_6247008, baseEnd_6247008] using wordTrace_append hprefix tailTrace_6247008
  have hstable : (prefixWord ++ tailWord_6247008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247008).length < 2 ^ (prefixWord ++ tailWord_6247008).sum := by decide
  have hdescent : baseEnd_6247008 < baseStart_6247008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247011 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6247011 : Nat := 118140960795 + 6247011 * 2 ^ 59
def prefixEnd_6247011 : Nat := 4983230072969 + 3 ^ 40 * 6247011 * 2
def baseEnd_6247011 : Nat := 3207719296924363274433025

theorem tailTrace_6247011 : CollatzResearch.WordTrace tailWord_6247011 prefixEnd_6247011 3207719296924363274433025 := by
  unfold tailWord_6247011
  simp only [CollatzResearch.WordTrace]
  refine ⟨227847209571153526383300887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151898139714102350922200591 227847209571153526383300887)
  ·
    refine ⟨341770814356730289574951331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227847209571153526383300887 341770814356730289574951331)
    ·
      refine ⟨512656221535095434362426997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341770814356730289574951331 512656221535095434362426997)
      ·
        refine ⟨48061520768915196971477531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 512656221535095434362426997 48061520768915196971477531)
        ·
          refine ⟨72092281153372795457216297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48061520768915196971477531 72092281153372795457216297)
          ·
            refine ⟨54069210865029596592912223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72092281153372795457216297 54069210865029596592912223)
            ·
              refine ⟨81103816297544394889368335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54069210865029596592912223 81103816297544394889368335)
              ·
                refine ⟨121655724446316592334052503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81103816297544394889368335 121655724446316592334052503)
                ·
                  refine ⟨182483586669474888501078755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121655724446316592334052503 182483586669474888501078755)
                  ·
                    refine ⟨273725380004212332751618133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182483586669474888501078755 273725380004212332751618133)
                    ·
                      refine ⟨3207719296924363274433025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 273725380004212332751618133 3207719296924363274433025)
                      ·
                        rfl

theorem cell23_6247011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6247011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247011 prefixEnd_6247011 := by exact prefixLift 6247011
  have htrace : WordTrace (prefixWord ++ tailWord_6247011) baseStart_6247011 baseEnd_6247011 := by
    simpa [prefixWord, tailWord_6247011, baseEnd_6247011] using wordTrace_append hprefix tailTrace_6247011
  have hstable : (prefixWord ++ tailWord_6247011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247011).length < 2 ^ (prefixWord ++ tailWord_6247011).sum := by decide
  have hdescent : baseEnd_6247011 < baseStart_6247011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247031 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_6247031 : Nat := 118140960795 + 6247031 * 2 ^ 59
def prefixEnd_6247031 : Nat := 4983230072969 + 3 ^ 40 * 6247031 * 2
def baseEnd_6247031 : Nat := 3207729566537453196182933

theorem tailTrace_6247031 : CollatzResearch.WordTrace tailWord_6247031 prefixEnd_6247031 3207729566537453196182933 := by
  unfold tailWord_6247031
  simp only [CollatzResearch.WordTrace]
  refine ⟨227847939031081069799028947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151898626020720713199352631 227847939031081069799028947)
  ·
    refine ⟨341771908546621604698543421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227847939031081069799028947 341771908546621604698543421)
    ·
      refine ⟨128164465704983101761953783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341771908546621604698543421 128164465704983101761953783)
      ·
        refine ⟨192246698557474652642930675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128164465704983101761953783 192246698557474652642930675)
        ·
          refine ⟨288370047836211978964396013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192246698557474652642930675 288370047836211978964396013)
          ·
            refine ⟨108138767938579492111648505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288370047836211978964396013 108138767938579492111648505)
            ·
              refine ⟨81104075953934619083736379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108138767938579492111648505 81104075953934619083736379)
              ·
                refine ⟨121656113930901928625604569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81104075953934619083736379 121656113930901928625604569)
                ·
                  refine ⟨91242085448176446469203427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121656113930901928625604569 91242085448176446469203427)
                  ·
                    refine ⟨136863128172264669703805141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91242085448176446469203427 136863128172264669703805141)
                    ·
                      refine ⟨3207729566537453196182933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136863128172264669703805141 3207729566537453196182933)
                      ·
                        rfl

theorem cell23_6247031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_6247031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247031 prefixEnd_6247031 := by exact prefixLift 6247031
  have htrace : WordTrace (prefixWord ++ tailWord_6247031) baseStart_6247031 baseEnd_6247031 := by
    simpa [prefixWord, tailWord_6247031, baseEnd_6247031] using wordTrace_append hprefix tailTrace_6247031
  have hstable : (prefixWord ++ tailWord_6247031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247031).length < 2 ^ (prefixWord ++ tailWord_6247031).sum := by decide
  have hdescent : baseEnd_6247031 < baseStart_6247031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247045 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_6247045 : Nat := 118140960795 + 6247045 * 2 ^ 59
def prefixEnd_6247045 : Nat := 4983230072969 + 3 ^ 40 * 6247045 * 2
def baseEnd_6247045 : Nat := 3207736755266616141407869

theorem tailTrace_6247045 : CollatzResearch.WordTrace tailWord_6247045 prefixEnd_6247045 3207736755266616141407869 := by
  unfold tailWord_6247045
  simp only [CollatzResearch.WordTrace]
  refine ⟨227848449653030350190038589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151898966435353566793359059 227848449653030350190038589)
  ·
    refine ⟨85443168619886381321264471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227848449653030350190038589 85443168619886381321264471)
    ·
      refine ⟨128164752929829571981896707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85443168619886381321264471 128164752929829571981896707)
      ·
        refine ⟨192247129394744357972845061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128164752929829571981896707 192247129394744357972845061)
        ·
          refine ⟨36046336761514567119908449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192247129394744357972845061 36046336761514567119908449)
          ·
            refine ⟨27034752571135925339931337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36046336761514567119908449 27034752571135925339931337)
            ·
              refine ⟨20276064428351944004948503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27034752571135925339931337 20276064428351944004948503)
              ·
                refine ⟨30414096642527916007422755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20276064428351944004948503 30414096642527916007422755)
                ·
                  refine ⟨45621144963791874011134133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30414096642527916007422755 45621144963791874011134133)
                  ·
                    refine ⟨4276982340355488188543825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45621144963791874011134133 4276982340355488188543825)
                    ·
                      refine ⟨3207736755266616141407869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276982340355488188543825 3207736755266616141407869)
                      ·
                        rfl

theorem cell23_6247045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_6247045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247045 prefixEnd_6247045 := by exact prefixLift 6247045
  have htrace : WordTrace (prefixWord ++ tailWord_6247045) baseStart_6247045 baseEnd_6247045 := by
    simpa [prefixWord, tailWord_6247045, baseEnd_6247045] using wordTrace_append hprefix tailTrace_6247045
  have hstable : (prefixWord ++ tailWord_6247045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247045).length < 2 ^ (prefixWord ++ tailWord_6247045).sum := by decide
  have hdescent : baseEnd_6247045 < baseStart_6247045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247052 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 1, 1, 3]
def baseStart_6247052 : Nat := 118140960795 + 6247052 * 2 ^ 59
def prefixEnd_6247052 : Nat := 4983230072969 + 3 ^ 40 * 6247052 * 2
def baseEnd_6247052 : Nat := 3207740349631197614020337

theorem tailTrace_6247052 : CollatzResearch.WordTrace tailWord_6247052 prefixEnd_6247052 3207740349631197614020337 := by
  unfold tailWord_6247052
  simp only [CollatzResearch.WordTrace]
  refine ⟨113924352482002495192771705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151899136642669993590362273 113924352482002495192771705)
  ·
    refine ⟨85443264361501871394578779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113924352482002495192771705 85443264361501871394578779)
    ·
      refine ⟨128164896542252807091868169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85443264361501871394578779 128164896542252807091868169)
      ·
        refine ⟨96123672406689605318901127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128164896542252807091868169 96123672406689605318901127)
        ·
          refine ⟨144185508610034407978351691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96123672406689605318901127 144185508610034407978351691)
          ·
            refine ⟨216278262915051611967527537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144185508610034407978351691 216278262915051611967527537)
            ·
              refine ⟨162208697186288708975645653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216278262915051611967527537 162208697186288708975645653)
              ·
                refine ⟨3801766340303641616616695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 162208697186288708975645653 3801766340303641616616695)
                ·
                  refine ⟨5702649510455462424925043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801766340303641616616695 5702649510455462424925043)
                  ·
                    refine ⟨8553974265683193637387565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702649510455462424925043 8553974265683193637387565)
                    ·
                      refine ⟨3207740349631197614020337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8553974265683193637387565 3207740349631197614020337)
                      ·
                        rfl

theorem cell23_6247052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_6247052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247052 prefixEnd_6247052 := by exact prefixLift 6247052
  have htrace : WordTrace (prefixWord ++ tailWord_6247052) baseStart_6247052 baseEnd_6247052 := by
    simpa [prefixWord, tailWord_6247052, baseEnd_6247052] using wordTrace_append hprefix tailTrace_6247052
  have hstable : (prefixWord ++ tailWord_6247052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247052).length < 2 ^ (prefixWord ++ tailWord_6247052).sum := by decide
  have hdescent : baseEnd_6247052 < baseStart_6247052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247081 : List Nat := [1, 2, 1, 1, 1, 1, 2, 14]
def baseStart_6247081 : Nat := 118140960795 + 6247081 * 2 ^ 59
def prefixEnd_6247081 : Nat := 4983230072969 + 3 ^ 40 * 6247081 * 2
def baseEnd_6247081 : Nat := 118805749650747333353989

theorem tailTrace_6247081 : CollatzResearch.WordTrace tailWord_6247081 prefixEnd_6247081 118805749650747333353989 := by
  unfold tailWord_6247081
  simp only [CollatzResearch.WordTrace]
  refine ⟨227849762680899928338349097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151899841787266618892232731 227849762680899928338349097)
  ·
    refine ⟨170887322010674946253761823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227849762680899928338349097 170887322010674946253761823)
    ·
      refine ⟨256330983016012419380642735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170887322010674946253761823 256330983016012419380642735)
      ·
        refine ⟨384496474524018629070964103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256330983016012419380642735 384496474524018629070964103)
        ·
          refine ⟨576744711786027943606446155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384496474524018629070964103 576744711786027943606446155)
          ·
            refine ⟨865117067679041915409669233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576744711786027943606446155 865117067679041915409669233)
            ·
              refine ⟨648837800759281436557251925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865117067679041915409669233 648837800759281436557251925)
              ·
                refine ⟨118805749650747333353989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 648837800759281436557251925 118805749650747333353989)
                ·
                  rfl

theorem cell23_6247081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 14].length) (baseStart_6247081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247081 prefixEnd_6247081 := by exact prefixLift 6247081
  have htrace : WordTrace (prefixWord ++ tailWord_6247081) baseStart_6247081 baseEnd_6247081 := by
    simpa [prefixWord, tailWord_6247081, baseEnd_6247081] using wordTrace_append hprefix tailTrace_6247081
  have hstable : (prefixWord ++ tailWord_6247081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247081).length < 2 ^ (prefixWord ++ tailWord_6247081).sum := by decide
  have hdescent : baseEnd_6247081 < baseStart_6247081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247088 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_6247088 : Nat := 118140960795 + 6247088 * 2 ^ 59
def prefixEnd_6247088 : Nat := 4983230072969 + 3 ^ 40 * 6247088 * 2
def baseEnd_6247088 : Nat := 3207758834934759473170171

theorem tailTrace_6247088 : CollatzResearch.WordTrace tailWord_6247088 prefixEnd_6247088 3207758834934759473170171 := by
  unfold tailWord_6247088
  simp only [CollatzResearch.WordTrace]
  refine ⟨113925008995937284266926959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151900011994583045689235945 113925008995937284266926959)
  ·
    refine ⟨170887513493905926400390439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113925008995937284266926959 170887513493905926400390439)
    ·
      refine ⟨256331270240858889600585659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170887513493905926400390439 256331270240858889600585659)
      ·
        refine ⟨384496905361288334400878489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256331270240858889600585659 384496905361288334400878489)
        ·
          refine ⟨288372679020966250800658867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384496905361288334400878489 288372679020966250800658867)
          ·
            refine ⟨432559018531449376200988301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288372679020966250800658867 432559018531449376200988301)
            ·
              refine ⟨162209631949293516075370613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432559018531449376200988301 162209631949293516075370613)
              ·
                refine ⟨15207152995246267132065995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162209631949293516075370613 15207152995246267132065995)
                ·
                  refine ⟨22810729492869400698098993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15207152995246267132065995 22810729492869400698098993)
                  ·
                    refine ⟨17108047119652050523574245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22810729492869400698098993 17108047119652050523574245)
                    ·
                      refine ⟨3207758834934759473170171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17108047119652050523574245 3207758834934759473170171)
                      ·
                        rfl

theorem cell23_6247088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_6247088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247088 prefixEnd_6247088 := by exact prefixLift 6247088
  have htrace : WordTrace (prefixWord ++ tailWord_6247088) baseStart_6247088 baseEnd_6247088 := by
    simpa [prefixWord, tailWord_6247088, baseEnd_6247088] using wordTrace_append hprefix tailTrace_6247088
  have hstable : (prefixWord ++ tailWord_6247088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247088).length < 2 ^ (prefixWord ++ tailWord_6247088).sum := by decide
  have hdescent : baseEnd_6247088 < baseStart_6247088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247089 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_6247089 : Nat := 118140960795 + 6247089 * 2 ^ 59
def prefixEnd_6247089 : Nat := 4983230072969 + 3 ^ 40 * 6247089 * 2
def baseEnd_6247089 : Nat := 1069253116138471323085889

theorem tailTrace_6247089 : CollatzResearch.WordTrace tailWord_6247089 prefixEnd_6247089 1069253116138471323085889 := by
  unfold tailWord_6247089
  simp only [CollatzResearch.WordTrace]
  refine ⟨227850054464870945704640321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151900036309913963803093547 227850054464870945704640321)
  ·
    refine ⟨170887540848653209278480241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227850054464870945704640321 170887540848653209278480241)
    ·
      refine ⟨128165655636489906958860181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170887540848653209278480241 128165655636489906958860181)
      ·
        refine ⟨6007765107960464388696571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128165655636489906958860181 6007765107960464388696571)
        ·
          refine ⟨9011647661940696583044857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6007765107960464388696571 9011647661940696583044857)
          ·
            refine ⟨6758735746455522437283643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9011647661940696583044857 6758735746455522437283643)
            ·
              refine ⟨10138103619683283655925465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758735746455522437283643 10138103619683283655925465)
              ·
                refine ⟨7603577714762462741944099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10138103619683283655925465 7603577714762462741944099)
                ·
                  refine ⟨11405366572143694112916149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7603577714762462741944099 11405366572143694112916149)
                  ·
                    refine ⟨1069253116138471323085889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11405366572143694112916149 1069253116138471323085889)
                    ·
                      rfl

theorem cell23_6247089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_6247089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247089 prefixEnd_6247089 := by exact prefixLift 6247089
  have htrace : WordTrace (prefixWord ++ tailWord_6247089) baseStart_6247089 baseEnd_6247089 := by
    simpa [prefixWord, tailWord_6247089, baseEnd_6247089] using wordTrace_append hprefix tailTrace_6247089
  have hstable : (prefixWord ++ tailWord_6247089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247089).length < 2 ^ (prefixWord ++ tailWord_6247089).sum := by decide
  have hdescent : baseEnd_6247089 < baseStart_6247089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247128 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_6247128 : Nat := 118140960795 + 6247128 * 2 ^ 59
def prefixEnd_6247128 : Nat := 4983230072969 + 3 ^ 40 * 6247128 * 2
def baseEnd_6247128 : Nat := 1069259791386979772223329

theorem tailTrace_6247128 : CollatzResearch.WordTrace tailWord_6247128 prefixEnd_6247128 1069259791386979772223329 := by
  unfold tailWord_6247128
  simp only [CollatzResearch.WordTrace]
  refine ⟨113925738455864827682655019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151900984607819770243540025 113925738455864827682655019)
  ·
    refine ⟨170888607683797241523982529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113925738455864827682655019 170888607683797241523982529)
    ·
      refine ⟨128166455762847931142986897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170888607683797241523982529 128166455762847931142986897)
      ·
        refine ⟨96124841822135948357240173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128166455762847931142986897 96124841822135948357240173)
        ·
          refine ⟨36046815683300980633965065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96124841822135948357240173 36046815683300980633965065)
          ·
            refine ⟨27035111762475735475473799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36046815683300980633965065 27035111762475735475473799)
            ·
              refine ⟨40552667643713603213210699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27035111762475735475473799 40552667643713603213210699)
              ·
                refine ⟨60829001465570404819816049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40552667643713603213210699 60829001465570404819816049)
                ·
                  refine ⟨45621751099177803614862037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60829001465570404819816049 45621751099177803614862037)
                  ·
                    refine ⟨1069259791386979772223329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45621751099177803614862037 1069259791386979772223329)
                    ·
                      rfl

theorem cell23_6247128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_6247128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247128 prefixEnd_6247128 := by exact prefixLift 6247128
  have htrace : WordTrace (prefixWord ++ tailWord_6247128) baseStart_6247128 baseEnd_6247128 := by
    simpa [prefixWord, tailWord_6247128, baseEnd_6247128] using wordTrace_append hprefix tailTrace_6247128
  have hstable : (prefixWord ++ tailWord_6247128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247128).length < 2 ^ (prefixWord ++ tailWord_6247128).sum := by decide
  have hdescent : baseEnd_6247128 < baseStart_6247128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247132 : List Nat := [2, 2, 5, 1, 1, 3, 1, 8]
def baseStart_6247132 : Nat := 118140960795 + 6247132 * 2 ^ 59
def prefixEnd_6247132 : Nat := 4983230072969 + 3 ^ 40 * 6247132 * 2
def baseEnd_6247132 : Nat := 118806719558650270408147

theorem tailTrace_6247132 : CollatzResearch.WordTrace tailWord_6247132 prefixEnd_6247132 118806719558650270408147 := by
  unfold tailWord_6247132
  simp only [CollatzResearch.WordTrace]
  refine ⟨113925811401857582024227825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151901081869143442698970433 113925811401857582024227825)
  ·
    refine ⟨85444358551393186518170869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113925811401857582024227825 85444358551393186518170869)
    ·
      refine ⟨8010408614193111236078519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85444358551393186518170869 8010408614193111236078519)
      ·
        refine ⟨12015612921289666854117779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010408614193111236078519 12015612921289666854117779)
        ·
          refine ⟨18023419381934500281176669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015612921289666854117779 18023419381934500281176669)
          ·
            refine ⟨6758782268225437605441251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18023419381934500281176669 6758782268225437605441251)
            ·
              refine ⟨10138173402338156408161877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758782268225437605441251 10138173402338156408161877)
              ·
                refine ⟨118806719558650270408147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10138173402338156408161877 118806719558650270408147)
                ·
                  rfl

theorem cell23_6247132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 8].length) (baseStart_6247132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247132 prefixEnd_6247132 := by exact prefixLift 6247132
  have htrace : WordTrace (prefixWord ++ tailWord_6247132) baseStart_6247132 baseEnd_6247132 := by
    simpa [prefixWord, tailWord_6247132, baseEnd_6247132] using wordTrace_append hprefix tailTrace_6247132
  have hstable : (prefixWord ++ tailWord_6247132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247132).length < 2 ^ (prefixWord ++ tailWord_6247132).sum := by decide
  have hdescent : baseEnd_6247132 < baseStart_6247132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247148 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_6247148 : Nat := 118140960795 + 6247148 * 2 ^ 59
def prefixEnd_6247148 : Nat := 4983230072969 + 3 ^ 40 * 6247148 * 2
def baseEnd_6247148 : Nat := 3207789643774029238419895

theorem tailTrace_6247148 : CollatzResearch.WordTrace tailWord_6247148 prefixEnd_6247148 3207789643774029238419895 := by
  unfold tailWord_6247148
  simp only [CollatzResearch.WordTrace]
  refine ⟨113926103185828599390519049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151901470914438132520692065 113926103185828599390519049)
  ·
    refine ⟨85444577389371449542889287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113926103185828599390519049 85444577389371449542889287)
    ·
      refine ⟨128166866084057174314333931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85444577389371449542889287 128166866084057174314333931)
      ·
        refine ⟨192250299126085761471500897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128166866084057174314333931 192250299126085761471500897)
        ·
          refine ⟨144187724344564321103625673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192250299126085761471500897 144187724344564321103625673)
          ·
            refine ⟨108140793258423240827719255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144187724344564321103625673 108140793258423240827719255)
            ·
              refine ⟨162211189887634861241578883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108140793258423240827719255 162211189887634861241578883)
              ·
                refine ⟨243316784831452291862368325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162211189887634861241578883 243316784831452291862368325)
                ·
                  refine ⟨45621897155897304724194061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243316784831452291862368325 45621897155897304724194061)
                  ·
                    refine ⟨17108211433461489271572773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45621897155897304724194061 17108211433461489271572773)
                    ·
                      refine ⟨3207789643774029238419895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17108211433461489271572773 3207789643774029238419895)
                      ·
                        rfl

theorem cell23_6247148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_6247148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247148 prefixEnd_6247148 := by exact prefixLift 6247148
  have htrace : WordTrace (prefixWord ++ tailWord_6247148) baseStart_6247148 baseEnd_6247148 := by
    simpa [prefixWord, tailWord_6247148, baseEnd_6247148] using wordTrace_append hprefix tailTrace_6247148
  have hstable : (prefixWord ++ tailWord_6247148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247148).length < 2 ^ (prefixWord ++ tailWord_6247148).sum := by decide
  have hdescent : baseEnd_6247148 < baseStart_6247148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247152 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2]
def baseStart_6247152 : Nat := 118140960795 + 6247152 * 2 ^ 59
def prefixEnd_6247152 : Nat := 4983230072969 + 3 ^ 40 * 6247152 * 2
def baseEnd_6247152 : Nat := 3207791697696647222769877

theorem tailTrace_6247152 : CollatzResearch.WordTrace tailWord_6247152 prefixEnd_6247152 3207791697696647222769877 := by
  unfold tailWord_6247152
  simp only [CollatzResearch.WordTrace]
  refine ⟨113926176131821353732091855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151901568175761804976122473 113926176131821353732091855)
  ·
    refine ⟨170889264197732030598137783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113926176131821353732091855 170889264197732030598137783)
    ·
      refine ⟨256333896296598045897206675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170889264197732030598137783 256333896296598045897206675)
      ·
        refine ⟨384500844444897068845810013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256333896296598045897206675 384500844444897068845810013)
        ·
          refine ⟨144187816666836400817178755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384500844444897068845810013 144187816666836400817178755)
          ·
            refine ⟨216281725000254601225768133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144187816666836400817178755 216281725000254601225768133)
            ·
              refine ⟨40552823437547737729831525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216281725000254601225768133 40552823437547737729831525)
              ·
                refine ⟨7603654394540200824343411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40552823437547737729831525 7603654394540200824343411)
                ·
                  refine ⟨11405481591810301236515117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7603654394540200824343411 11405481591810301236515117)
                  ·
                    refine ⟨4277055596928862963693169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11405481591810301236515117 4277055596928862963693169)
                    ·
                      refine ⟨3207791697696647222769877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277055596928862963693169 3207791697696647222769877)
                      ·
                        rfl

theorem cell23_6247152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2].length) (baseStart_6247152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247152 prefixEnd_6247152 := by exact prefixLift 6247152
  have htrace : WordTrace (prefixWord ++ tailWord_6247152) baseStart_6247152 baseEnd_6247152 := by
    simpa [prefixWord, tailWord_6247152, baseEnd_6247152] using wordTrace_append hprefix tailTrace_6247152
  have hstable : (prefixWord ++ tailWord_6247152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247152).length < 2 ^ (prefixWord ++ tailWord_6247152).sum := by decide
  have hdescent : baseEnd_6247152 < baseStart_6247152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247175 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 2, 6]
def baseStart_6247175 : Nat := 118140960795 + 6247175 * 2 ^ 59
def prefixEnd_6247175 : Nat := 4983230072969 + 3 ^ 40 * 6247175 * 2
def baseEnd_6247175 : Nat := 1069267835917233544260757

theorem tailTrace_6247175 : CollatzResearch.WordTrace tailWord_6247175 prefixEnd_6247175 1069267835917233544260757 := by
  unfold tailWord_6247175
  simp only [CollatzResearch.WordTrace]
  refine ⟨227853191142559382392270979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151902127428372921594847319 227853191142559382392270979)
  ·
    refine ⟨341779786713839073588406469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227853191142559382392270979 341779786713839073588406469)
    ·
      refine ⟨64083710008844826297826213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341779786713839073588406469 64083710008844826297826213)
      ·
        refine ⟨12015695626658404930842415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64083710008844826297826213 12015695626658404930842415)
        ·
          refine ⟨18023543439987607396263623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015695626658404930842415 18023543439987607396263623)
          ·
            refine ⟨27035315159981411094395435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18023543439987607396263623 27035315159981411094395435)
            ·
              refine ⟨40552972739972116641593153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27035315159981411094395435 40552972739972116641593153)
              ·
                refine ⟨30414729554979087481194865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40552972739972116641593153 30414729554979087481194865)
                ·
                  refine ⟨22811047166234315610896149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30414729554979087481194865 22811047166234315610896149)
                  ·
                    refine ⟨1069267835917233544260757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22811047166234315610896149 1069267835917233544260757)
                    ·
                      rfl

theorem cell23_6247175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_6247175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247175 prefixEnd_6247175 := by exact prefixLift 6247175
  have htrace : WordTrace (prefixWord ++ tailWord_6247175) baseStart_6247175 baseEnd_6247175 := by
    simpa [prefixWord, tailWord_6247175, baseEnd_6247175] using wordTrace_append hprefix tailTrace_6247175
  have hstable : (prefixWord ++ tailWord_6247175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247175).length < 2 ^ (prefixWord ++ tailWord_6247175).sum := by decide
  have hdescent : baseEnd_6247175 < baseStart_6247175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247199 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 1, 4, 2]
def baseStart_6247199 : Nat := 118140960795 + 6247199 * 2 ^ 59
def prefixEnd_6247199 : Nat := 4983230072969 + 3 ^ 40 * 6247199 * 2
def baseEnd_6247199 : Nat := 3207815831287408538882161

theorem tailTrace_6247199 : CollatzResearch.WordTrace tailWord_6247199 prefixEnd_6247199 3207815831287408538882161 := by
  unfold tailWord_6247199
  simp only [CollatzResearch.WordTrace]
  refine ⟨227854066494472434491144651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151902710996314956327429767 227854066494472434491144651)
  ·
    refine ⟨341781099741708651736716977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227854066494472434491144651 341781099741708651736716977)
    ·
      refine ⟨256335824806281488802537733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341781099741708651736716977 256335824806281488802537733)
      ·
        refine ⟨48062967151177779150475825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256335824806281488802537733 48062967151177779150475825)
        ·
          refine ⟨36047225363383334362856869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48062967151177779150475825 36047225363383334362856869)
          ·
            refine ⟨6758854755634375193035663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36047225363383334362856869 6758854755634375193035663)
            ·
              refine ⟨10138282133451562789553495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758854755634375193035663 10138282133451562789553495)
              ·
                refine ⟨15207423200177344184330243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138282133451562789553495 15207423200177344184330243)
                ·
                  refine ⟨22811134800266016276495365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15207423200177344184330243 22811134800266016276495365)
                  ·
                    refine ⟨4277087775049878051842881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22811134800266016276495365 4277087775049878051842881)
                    ·
                      refine ⟨3207815831287408538882161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277087775049878051842881 3207815831287408538882161)
                      ·
                        rfl

theorem cell23_6247199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_6247199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247199 prefixEnd_6247199 := by exact prefixLift 6247199
  have htrace : WordTrace (prefixWord ++ tailWord_6247199) baseStart_6247199 baseEnd_6247199 := by
    simpa [prefixWord, tailWord_6247199, baseEnd_6247199] using wordTrace_append hprefix tailTrace_6247199
  have hstable : (prefixWord ++ tailWord_6247199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247199).length < 2 ^ (prefixWord ++ tailWord_6247199).sum := by decide
  have hdescent : baseEnd_6247199 < baseStart_6247199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247235 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 2, 5]
def baseStart_6247235 : Nat := 118140960795 + 6247235 * 2 ^ 59
def prefixEnd_6247235 : Nat := 4983230072969 + 3 ^ 40 * 6247235 * 2
def baseEnd_6247235 : Nat := 1069278105530323466010665

theorem tailTrace_6247235 : CollatzResearch.WordTrace tailWord_6247235 prefixEnd_6247235 1069278105530323466010665 := by
  unfold tailWord_6247235
  simp only [CollatzResearch.WordTrace]
  refine ⟨227855379522342012639455159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151903586348228008426303439 227855379522342012639455159)
  ·
    refine ⟨341783069283513018959182739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227855379522342012639455159 341783069283513018959182739)
    ·
      refine ⟨512674603925269528438774109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341783069283513018959182739 512674603925269528438774109)
      ·
        refine ⟨192252976471976073164540291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512674603925269528438774109 192252976471976073164540291)
        ·
          refine ⟨288379464707964109746810437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192252976471976073164540291 288379464707964109746810437)
          ·
            refine ⟨54071149632743270577526957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288379464707964109746810437 54071149632743270577526957)
            ·
              refine ⟨20276681112278726466572609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54071149632743270577526957 20276681112278726466572609)
              ·
                refine ⟨15207510834209044849929457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20276681112278726466572609 15207510834209044849929457)
                ·
                  refine ⟨11405633125656783637447093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15207510834209044849929457 11405633125656783637447093)
                  ·
                    refine ⟨1069278105530323466010665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11405633125656783637447093 1069278105530323466010665)
                    ·
                      rfl

theorem cell23_6247235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 5].length) (baseStart_6247235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247235 prefixEnd_6247235 := by exact prefixLift 6247235
  have htrace : WordTrace (prefixWord ++ tailWord_6247235) baseStart_6247235 baseEnd_6247235 := by
    simpa [prefixWord, tailWord_6247235, baseEnd_6247235] using wordTrace_append hprefix tailTrace_6247235
  have hstable : (prefixWord ++ tailWord_6247235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247235).length < 2 ^ (prefixWord ++ tailWord_6247235).sum := by decide
  have hdescent : baseEnd_6247235 < baseStart_6247235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247272 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6247272 : Nat := 118140960795 + 6247272 * 2 ^ 59
def prefixEnd_6247272 : Nat := 4983230072969 + 3 ^ 40 * 6247272 * 2
def baseEnd_6247272 : Nat := 3207853315375186753269325

theorem tailTrace_6247272 : CollatzResearch.WordTrace tailWord_6247272 prefixEnd_6247272 3207853315375186753269325 := by
  unfold tailWord_6247272
  simp only [CollatzResearch.WordTrace]
  refine ⟨113928364511603983979276035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151904486015471978639034713 113928364511603983979276035)
  ·
    refine ⟨170892546767405975968914053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113928364511603983979276035 170892546767405975968914053)
    ·
      refine ⟨32042352518888620494171385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170892546767405975968914053 32042352518888620494171385)
      ·
        refine ⟨24031764389166465370628539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32042352518888620494171385 24031764389166465370628539)
        ·
          refine ⟨36047646583749698055942809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24031764389166465370628539 36047646583749698055942809)
          ·
            refine ⟨27035734937812273541957107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36047646583749698055942809 27035734937812273541957107)
            ·
              refine ⟨40553602406718410312935661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27035734937812273541957107 40553602406718410312935661)
              ·
                refine ⟨15207600902519403867350873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40553602406718410312935661 15207600902519403867350873)
                ·
                  refine ⟨11405700676889552900513155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15207600902519403867350873 11405700676889552900513155)
                  ·
                    refine ⟨17108551015334329350769733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11405700676889552900513155 17108551015334329350769733)
                    ·
                      refine ⟨3207853315375186753269325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17108551015334329350769733 3207853315375186753269325)
                      ·
                        rfl

theorem cell23_6247272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6247272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247272 prefixEnd_6247272 := by exact prefixLift 6247272
  have htrace : WordTrace (prefixWord ++ tailWord_6247272) baseStart_6247272 baseEnd_6247272 := by
    simpa [prefixWord, tailWord_6247272, baseEnd_6247272] using wordTrace_append hprefix tailTrace_6247272
  have hstable : (prefixWord ++ tailWord_6247272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247272).length < 2 ^ (prefixWord ++ tailWord_6247272).sum := by decide
  have hdescent : baseEnd_6247272 < baseStart_6247272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247275 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3]
def baseStart_6247275 : Nat := 118140960795 + 6247275 * 2 ^ 59
def prefixEnd_6247275 : Nat := 4983230072969 + 3 ^ 40 * 6247275 * 2
def baseEnd_6247275 : Nat := 3207854855817150241531811

theorem tailTrace_6247275 : CollatzResearch.WordTrace tailWord_6247275 prefixEnd_6247275 3207854855817150241531811 := by
  unfold tailWord_6247275
  simp only [CollatzResearch.WordTrace]
  refine ⟨227856838442197099470911279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151904558961464732980607519 227856838442197099470911279)
  ·
    refine ⟨341785257663295649206366919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227856838442197099470911279 341785257663295649206366919)
    ·
      refine ⟨512677886494943473809550379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341785257663295649206366919 512677886494943473809550379)
      ·
        refine ⟨769016829742415210714325569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512677886494943473809550379 769016829742415210714325569)
        ·
          refine ⟨576762622306811408035744177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769016829742415210714325569 576762622306811408035744177)
          ·
            refine ⟨432571966730108556026808133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576762622306811408035744177 432571966730108556026808133)
            ·
              refine ⟨81107243761895354255026525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 432571966730108556026808133 81107243761895354255026525)
              ·
                refine ⟨30415216410710757845634947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81107243761895354255026525 30415216410710757845634947)
                ·
                  refine ⟨45622824616066136768452421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30415216410710757845634947 45622824616066136768452421)
                  ·
                    refine ⟨8554279615512400644084829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45622824616066136768452421 8554279615512400644084829)
                    ·
                      refine ⟨3207854855817150241531811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554279615512400644084829 3207854855817150241531811)
                      ·
                        rfl

theorem cell23_6247275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3].length) (baseStart_6247275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247275 prefixEnd_6247275 := by exact prefixLift 6247275
  have htrace : WordTrace (prefixWord ++ tailWord_6247275) baseStart_6247275 baseEnd_6247275 := by
    simpa [prefixWord, tailWord_6247275, baseEnd_6247275] using wordTrace_append hprefix tailTrace_6247275
  have hstable : (prefixWord ++ tailWord_6247275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247275).length < 2 ^ (prefixWord ++ tailWord_6247275).sum := by decide
  have hdescent : baseEnd_6247275 < baseStart_6247275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247295 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 6]
def baseStart_6247295 : Nat := 118140960795 + 6247295 * 2 ^ 59
def prefixEnd_6247295 : Nat := 4983230072969 + 3 ^ 40 * 6247295 * 2
def baseEnd_6247295 : Nat := 356429458381137795920191

theorem tailTrace_6247295 : CollatzResearch.WordTrace tailWord_6247295 prefixEnd_6247295 356429458381137795920191 := by
  unfold tailWord_6247295
  simp only [CollatzResearch.WordTrace]
  refine ⟨227857567902124642886639339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151905045268083095257759559 227857567902124642886639339)
  ·
    refine ⟨341786351853186964329959009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227857567902124642886639339 341786351853186964329959009)
    ·
      refine ⟨256339763889890223247469257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341786351853186964329959009 256339763889890223247469257)
      ·
        refine ⟨192254822917417667435601943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256339763889890223247469257 192254822917417667435601943)
        ·
          refine ⟨288382234376126501153402915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192254822917417667435601943 288382234376126501153402915)
          ·
            refine ⟨432573351564189751730104373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288382234376126501153402915 432573351564189751730104373)
            ·
              refine ⟨40553751709142789224697285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 432573351564189751730104373 40553751709142789224697285)
              ·
                refine ⟨7603828445464272979630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40553751709142789224697285 7603828445464272979630741)
                ·
                  refine ⟨356429458381137795920191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7603828445464272979630741 356429458381137795920191)
                  ·
                    rfl

theorem cell23_6247295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 6].length) (baseStart_6247295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247295 prefixEnd_6247295 := by exact prefixLift 6247295
  have htrace : WordTrace (prefixWord ++ tailWord_6247295) baseStart_6247295 baseEnd_6247295 := by
    simpa [prefixWord, tailWord_6247295, baseEnd_6247295] using wordTrace_append hprefix tailTrace_6247295
  have hstable : (prefixWord ++ tailWord_6247295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247295).length < 2 ^ (prefixWord ++ tailWord_6247295).sum := by decide
  have hdescent : baseEnd_6247295 < baseStart_6247295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247299 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 1, 4]
def baseStart_6247299 : Nat := 118140960795 + 6247299 * 2 ^ 59
def prefixEnd_6247299 : Nat := 4983230072969 + 3 ^ 40 * 6247299 * 2
def baseEnd_6247299 : Nat := 1069289059784286049210567

theorem tailTrace_6247299 : CollatzResearch.WordTrace tailWord_6247299 prefixEnd_6247299 1069289059784286049210567 := by
  unfold tailWord_6247299
  simp only [CollatzResearch.WordTrace]
  refine ⟨227857713794110151569784951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151905142529406767713189967 227857713794110151569784951)
  ·
    refine ⟨341786570691165227354677427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227857713794110151569784951 341786570691165227354677427)
    ·
      refine ⟨512679856036747841032016141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341786570691165227354677427 512679856036747841032016141)
      ·
        refine ⟨192254946013780440387006053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512679856036747841032016141 192254946013780440387006053)
        ·
          refine ⟨36047802377583832572563635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192254946013780440387006053 36047802377583832572563635)
          ·
            refine ⟨54071703566375748858845453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36047802377583832572563635 54071703566375748858845453)
            ·
              refine ⟨20276888837390905822067045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54071703566375748858845453 20276888837390905822067045)
              ·
                refine ⟨3801916657010794841637571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20276888837390905822067045 3801916657010794841637571)
                ·
                  refine ⟨5702874985516192262456357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801916657010794841637571 5702874985516192262456357)
                  ·
                    refine ⟨1069289059784286049210567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702874985516192262456357 1069289059784286049210567)
                    ·
                      rfl

theorem cell23_6247299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 4].length) (baseStart_6247299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247299 prefixEnd_6247299 := by exact prefixLift 6247299
  have htrace : WordTrace (prefixWord ++ tailWord_6247299) baseStart_6247299 baseEnd_6247299 := by
    simpa [prefixWord, tailWord_6247299, baseEnd_6247299] using wordTrace_append hprefix tailTrace_6247299
  have hstable : (prefixWord ++ tailWord_6247299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247299).length < 2 ^ (prefixWord ++ tailWord_6247299).sum := by decide
  have hdescent : baseEnd_6247299 < baseStart_6247299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247349 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_6247349 : Nat := 118140960795 + 6247349 * 2 ^ 59
def prefixEnd_6247349 : Nat := 4983230072969 + 3 ^ 40 * 6247349 * 2
def baseEnd_6247349 : Nat := 3207892853385582952006471

theorem tailTrace_6247349 : CollatzResearch.WordTrace tailWord_6247349 prefixEnd_6247349 3207892853385582952006471 := by
  unfold tailWord_6247349
  simp only [CollatzResearch.WordTrace]
  refine ⟨227859537443929010109105101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151906358295952673406070067 227859537443929010109105101)
  ·
    refine ⟨85447326541473378790914413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227859537443929010109105101 85447326541473378790914413)
    ·
      refine ⟨32042747453052517046592905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85447326541473378790914413 32042747453052517046592905)
      ·
        refine ⟨24032060589789387784944679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32042747453052517046592905 24032060589789387784944679)
        ·
          refine ⟨36048090884684081677417019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24032060589789387784944679 36048090884684081677417019)
          ·
            refine ⟨54072136327026122516125529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36048090884684081677417019 54072136327026122516125529)
            ·
              refine ⟨40554102245269591887094147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54072136327026122516125529 40554102245269591887094147)
              ·
                refine ⟨60831153367904387830641221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40554102245269591887094147 60831153367904387830641221)
                ·
                  refine ⟨11405841256482072718245229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60831153367904387830641221 11405841256482072718245229)
                  ·
                    refine ⟨4277190471180777269341961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11405841256482072718245229 4277190471180777269341961)
                    ·
                      refine ⟨3207892853385582952006471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277190471180777269341961 3207892853385582952006471)
                      ·
                        rfl

theorem cell23_6247349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_6247349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247349 prefixEnd_6247349 := by exact prefixLift 6247349
  have htrace : WordTrace (prefixWord ++ tailWord_6247349) baseStart_6247349 baseEnd_6247349 := by
    simpa [prefixWord, tailWord_6247349, baseEnd_6247349] using wordTrace_append hprefix tailTrace_6247349
  have hstable : (prefixWord ++ tailWord_6247349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247349).length < 2 ^ (prefixWord ++ tailWord_6247349).sum := by decide
  have hdescent : baseEnd_6247349 < baseStart_6247349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247350 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6247350 : Nat := 118140960795 + 6247350 * 2 ^ 59
def prefixEnd_6247350 : Nat := 4983230072969 + 3 ^ 40 * 6247350 * 2
def baseEnd_6247350 : Nat := 1069297788955412482697989

theorem tailTrace_6247350 : CollatzResearch.WordTrace tailWord_6247350 prefixEnd_6247350 1069297788955412482697989 := by
  unfold tailWord_6247350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241223369807836704993219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151906382611283591519927669 14241223369807836704993219)
  ·
    refine ⟨21361835054711755057489829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14241223369807836704993219 21361835054711755057489829)
    ·
      refine ⟨4005344072758454073279343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21361835054711755057489829 4005344072758454073279343)
      ·
        refine ⟨6008016109137681109919015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005344072758454073279343 6008016109137681109919015)
        ·
          refine ⟨9012024163706521664878523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008016109137681109919015 9012024163706521664878523)
          ·
            refine ⟨13518036245559782497317785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9012024163706521664878523 13518036245559782497317785)
            ·
              refine ⟨10138527184169836872988339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13518036245559782497317785 10138527184169836872988339)
              ·
                refine ⟨15207790776254755309482509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138527184169836872988339 15207790776254755309482509)
                ·
                  refine ⟨5702921541095533241055941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15207790776254755309482509 5702921541095533241055941)
                  ·
                    refine ⟨1069297788955412482697989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702921541095533241055941 1069297788955412482697989)
                    ·
                      rfl

theorem cell23_6247350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6247350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247350 prefixEnd_6247350 := by exact prefixLift 6247350
  have htrace : WordTrace (prefixWord ++ tailWord_6247350) baseStart_6247350 baseEnd_6247350 := by
    simpa [prefixWord, tailWord_6247350, baseEnd_6247350] using wordTrace_append hprefix tailTrace_6247350
  have hstable : (prefixWord ++ tailWord_6247350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247350).length < 2 ^ (prefixWord ++ tailWord_6247350).sum := by decide
  have hdescent : baseEnd_6247350 < baseStart_6247350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247389 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6247389 : Nat := 118140960795 + 6247389 * 2 ^ 59
def prefixEnd_6247389 : Nat := 4983230072969 + 3 ^ 40 * 6247389 * 2
def baseEnd_6247389 : Nat := 1069304464203920931835429

theorem tailTrace_6247389 : CollatzResearch.WordTrace tailWord_6247389 prefixEnd_6247389 1069304464203920931835429 := by
  unfold tailWord_6247389
  simp only [CollatzResearch.WordTrace]
  refine ⟨227860996363784096940561221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151907330909189397960374147 227860996363784096940561221)
  ·
    refine ⟨42723936818209518176355229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227860996363784096940561221 42723936818209518176355229)
    ·
      refine ⟨16021476306828569316133211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42723936818209518176355229 16021476306828569316133211)
      ·
        refine ⟨24032214460242853974199817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16021476306828569316133211 24032214460242853974199817)
        ·
          refine ⟨18024160845182140480649863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24032214460242853974199817 18024160845182140480649863)
          ·
            refine ⟨27036241267773210720974795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18024160845182140480649863 27036241267773210720974795)
            ·
              refine ⟨40554361901659816081462193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27036241267773210720974795 40554361901659816081462193)
              ·
                refine ⟨30415771426244862061096645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40554361901659816081462193 30415771426244862061096645)
                ·
                  refine ⟨5702957142420911636455621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30415771426244862061096645 5702957142420911636455621)
                  ·
                    refine ⟨1069304464203920931835429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702957142420911636455621 1069304464203920931835429)
                    ·
                      rfl

theorem cell23_6247389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6247389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247389 prefixEnd_6247389 := by exact prefixLift 6247389
  have htrace : WordTrace (prefixWord ++ tailWord_6247389) baseStart_6247389 baseEnd_6247389 := by
    simpa [prefixWord, tailWord_6247389, baseEnd_6247389] using wordTrace_append hprefix tailTrace_6247389
  have hstable : (prefixWord ++ tailWord_6247389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247389).length < 2 ^ (prefixWord ++ tailWord_6247389).sum := by decide
  have hdescent : baseEnd_6247389 < baseStart_6247389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247399 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6247399 : Nat := 118140960795 + 6247399 * 2 ^ 59
def prefixEnd_6247399 : Nat := 4983230072969 + 3 ^ 40 * 6247399 * 2
def baseEnd_6247399 : Nat := 3207918527418307756381241

theorem tailTrace_6247399 : CollatzResearch.WordTrace tailWord_6247399 prefixEnd_6247399 3207918527418307756381241 := by
  unfold tailWord_6247399
  simp only [CollatzResearch.WordTrace]
  refine ⟨227861361093747868648425251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151907574062498579098950167 227861361093747868648425251)
  ·
    refine ⟨341792041640621802972637877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227861361093747868648425251 341792041640621802972637877)
    ·
      refine ⟨32043003903808294028684801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341792041640621802972637877 32043003903808294028684801)
      ·
        refine ⟨24032252927856220521513601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32043003903808294028684801 24032252927856220521513601)
        ·
          refine ⟨18024189695892165391135201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24032252927856220521513601 18024189695892165391135201)
          ·
            refine ⟨13518142271919124043351401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18024189695892165391135201 13518142271919124043351401)
            ·
              refine ⟨10138606703939343032513551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13518142271919124043351401 10138606703939343032513551)
              ·
                refine ⟨15207910055909014548770327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138606703939343032513551 15207910055909014548770327)
                ·
                  refine ⟨22811865083863521823155491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15207910055909014548770327 22811865083863521823155491)
                  ·
                    refine ⟨34217797625795282734733237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22811865083863521823155491 34217797625795282734733237)
                    ·
                      refine ⟨3207918527418307756381241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34217797625795282734733237 3207918527418307756381241)
                      ·
                        rfl

theorem cell23_6247399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6247399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247399 prefixEnd_6247399 := by exact prefixLift 6247399
  have htrace : WordTrace (prefixWord ++ tailWord_6247399) baseStart_6247399 baseEnd_6247399 := by
    simpa [prefixWord, tailWord_6247399, baseEnd_6247399] using wordTrace_append hprefix tailTrace_6247399
  have hstable : (prefixWord ++ tailWord_6247399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247399).length < 2 ^ (prefixWord ++ tailWord_6247399).sum := by decide
  have hdescent : baseEnd_6247399 < baseStart_6247399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247402 : List Nat := [3, 1, 3, 1, 2, 4, 9]
def baseStart_6247402 : Nat := 118140960795 + 6247402 * 2 ^ 59
def prefixEnd_6247402 : Nat := 4983230072969 + 3 ^ 40 * 6247402 * 2
def baseEnd_6247402 : Nat := 39603951455065077094367

theorem tailTrace_6247402 : CollatzResearch.WordTrace tailWord_6247402 prefixEnd_6247402 39603951455065077094367 := by
  unfold tailWord_6247402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56965367628184250040196115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151907647008491333440522973 56965367628184250040196115)
  ·
    refine ⟨85448051442276375060294173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56965367628184250040196115 85448051442276375060294173)
    ·
      refine ⟨32043019290853640647610315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85448051442276375060294173 32043019290853640647610315)
      ·
        refine ⟨48064528936280460971415473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32043019290853640647610315 48064528936280460971415473)
        ·
          refine ⟨36048396702210345728561605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48064528936280460971415473 36048396702210345728561605)
          ·
            refine ⟨6759074381664439824105301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36048396702210345728561605 6759074381664439824105301)
            ·
              refine ⟨39603951455065077094367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6759074381664439824105301 39603951455065077094367)
              ·
                rfl

theorem cell23_6247402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 9].length) (baseStart_6247402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247402 prefixEnd_6247402 := by exact prefixLift 6247402
  have htrace : WordTrace (prefixWord ++ tailWord_6247402) baseStart_6247402 baseEnd_6247402 := by
    simpa [prefixWord, tailWord_6247402, baseEnd_6247402] using wordTrace_append hprefix tailTrace_6247402
  have hstable : (prefixWord ++ tailWord_6247402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247402).length < 2 ^ (prefixWord ++ tailWord_6247402).sum := by decide
  have hdescent : baseEnd_6247402 < baseStart_6247402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247463 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6247463 : Nat := 118140960795 + 6247463 * 2 ^ 59
def prefixEnd_6247463 : Nat := 4983230072969 + 3 ^ 40 * 6247463 * 2
def baseEnd_6247463 : Nat := 3207951390180195505980947

theorem tailTrace_6247463 : CollatzResearch.WordTrace tailWord_6247463 prefixEnd_6247463 3207951390180195505980947 := by
  unfold tailWord_6247463
  simp only [CollatzResearch.WordTrace]
  refine ⟨227863695365516007578755043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151909130243677338385836695 227863695365516007578755043)
  ·
    refine ⟨341795543048274011368132565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227863695365516007578755043 341795543048274011368132565)
    ·
      refine ⟨8010833040193922141440607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 341795543048274011368132565 8010833040193922141440607)
      ·
        refine ⟨12016249560290883212160911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010833040193922141440607 12016249560290883212160911)
        ·
          refine ⟨18024374340436324818241367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016249560290883212160911 18024374340436324818241367)
          ·
            refine ⟨27036561510654487227362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18024374340436324818241367 27036561510654487227362051)
            ·
              refine ⟨40554842265981730841043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27036561510654487227362051 40554842265981730841043077)
              ·
                refine ⟨7604032924871574532695577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40554842265981730841043077 7604032924871574532695577)
                ·
                  refine ⟨5703024693653680899521683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7604032924871574532695577 5703024693653680899521683)
                  ·
                    refine ⟨8554537040480521349282525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703024693653680899521683 8554537040480521349282525)
                    ·
                      refine ⟨3207951390180195505980947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554537040480521349282525 3207951390180195505980947)
                      ·
                        rfl

theorem cell23_6247463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6247463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247463 prefixEnd_6247463 := by exact prefixLift 6247463
  have htrace : WordTrace (prefixWord ++ tailWord_6247463) baseStart_6247463 baseEnd_6247463 := by
    simpa [prefixWord, tailWord_6247463, baseEnd_6247463] using wordTrace_append hprefix tailTrace_6247463
  have hstable : (prefixWord ++ tailWord_6247463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247463).length < 2 ^ (prefixWord ++ tailWord_6247463).sum := by decide
  have hdescent : baseEnd_6247463 < baseStart_6247463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247472 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_6247472 : Nat := 118140960795 + 6247472 * 2 ^ 59
def prefixEnd_6247472 : Nat := 4983230072969 + 3 ^ 40 * 6247472 * 2
def baseEnd_6247472 : Nat := 3207956011506085970768405

theorem tailTrace_6247472 : CollatzResearch.WordTrace tailWord_6247472 prefixEnd_6247472 3207956011506085970768405 := by
  unfold tailWord_6247472
  simp only [CollatzResearch.WordTrace]
  refine ⟨113932011811241701057916335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151909349081655601410555113 113932011811241701057916335)
  ·
    refine ⟨170898017716862551586874503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113932011811241701057916335 170898017716862551586874503)
    ·
      refine ⟨256347026575293827380311755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170898017716862551586874503 256347026575293827380311755)
      ·
        refine ⟨384520539862940741070467633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256347026575293827380311755 384520539862940741070467633)
        ·
          refine ⟨288390404897205555802850725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384520539862940741070467633 288390404897205555802850725)
          ·
            refine ⟨54073200918226041713034511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288390404897205555802850725 54073200918226041713034511)
            ·
              refine ⟨81109801377339062569551767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54073200918226041713034511 81109801377339062569551767)
              ·
                refine ⟨121664702066008593854327651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81109801377339062569551767 121664702066008593854327651)
                ·
                  refine ⟨182497053099012890781491477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121664702066008593854327651 182497053099012890781491477)
                  ·
                    refine ⟨8554549364016229255382413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182497053099012890781491477 8554549364016229255382413)
                    ·
                      refine ⟨3207956011506085970768405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554549364016229255382413 3207956011506085970768405)
                      ·
                        rfl

theorem cell23_6247472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_6247472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247472 prefixEnd_6247472 := by exact prefixLift 6247472
  have htrace : WordTrace (prefixWord ++ tailWord_6247472) baseStart_6247472 baseEnd_6247472 := by
    simpa [prefixWord, tailWord_6247472, baseEnd_6247472] using wordTrace_append hprefix tailTrace_6247472
  have hstable : (prefixWord ++ tailWord_6247472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247472).length < 2 ^ (prefixWord ++ tailWord_6247472).sum := by decide
  have hdescent : baseEnd_6247472 < baseStart_6247472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247482 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_6247482 : Nat := 118140960795 + 6247482 * 2 ^ 59
def prefixEnd_6247482 : Nat := 4983230072969 + 3 ^ 40 * 6247482 * 2
def baseEnd_6247482 : Nat := 3207961146312630931643359

theorem tailTrace_6247482 : CollatzResearch.WordTrace tailWord_6247482 prefixEnd_6247482 3207961146312630931643359 := by
  unfold tailWord_6247482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56966097088111793455924175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151909592234964782549131133 56966097088111793455924175)
  ·
    refine ⟨85449145632167690183886263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56966097088111793455924175 85449145632167690183886263)
    ·
      refine ⟨128173718448251535275829395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85449145632167690183886263 128173718448251535275829395)
      ·
        refine ⟨192260577672377302913744093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128173718448251535275829395 192260577672377302913744093)
        ·
          refine ⟨72097716627141488592654035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192260577672377302913744093 72097716627141488592654035)
          ·
            refine ⟨108146574940712232888981053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72097716627141488592654035 108146574940712232888981053)
            ·
              refine ⟨40554965602767087333367895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108146574940712232888981053 40554965602767087333367895)
              ·
                refine ⟨60832448404150631000051843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40554965602767087333367895 60832448404150631000051843)
                ·
                  refine ⟨91248672606225946500077765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60832448404150631000051843 91248672606225946500077765)
                  ·
                    refine ⟨17109126113667364968764581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91248672606225946500077765 17109126113667364968764581)
                    ·
                      refine ⟨3207961146312630931643359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17109126113667364968764581 3207961146312630931643359)
                      ·
                        rfl

theorem cell23_6247482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_6247482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247482 prefixEnd_6247482 := by exact prefixLift 6247482
  have htrace : WordTrace (prefixWord ++ tailWord_6247482) baseStart_6247482 baseEnd_6247482 := by
    simpa [prefixWord, tailWord_6247482, baseEnd_6247482] using wordTrace_append hprefix tailTrace_6247482
  have hstable : (prefixWord ++ tailWord_6247482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247482).length < 2 ^ (prefixWord ++ tailWord_6247482).sum := by decide
  have hdescent : baseEnd_6247482 < baseStart_6247482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247532 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_6247532 : Nat := 118140960795 + 6247532 * 2 ^ 59
def prefixEnd_6247532 : Nat := 4983230072969 + 3 ^ 40 * 6247532 * 2
def baseEnd_6247532 : Nat := 3207986820345355736018129

theorem tailTrace_6247532 : CollatzResearch.WordTrace tailWord_6247532 prefixEnd_6247532 3207986820345355736018129 := by
  unfold tailWord_6247532
  simp only [CollatzResearch.WordTrace]
  refine ⟨113933106001133016181508425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151910808001510688242011233 113933106001133016181508425)
  ·
    refine ⟨85449829500849762136131319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113933106001133016181508425 85449829500849762136131319)
    ·
      refine ⟨128174744251274643204196979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85449829500849762136131319 128174744251274643204196979)
      ·
        refine ⟨192262116376911964806295469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128174744251274643204196979 192262116376911964806295469)
        ·
          refine ⟨72098293641341986802360801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192262116376911964806295469 72098293641341986802360801)
          ·
            refine ⟨54073720231006490101770601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72098293641341986802360801 54073720231006490101770601)
            ·
              refine ⟨40555290173254867576327951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54073720231006490101770601 40555290173254867576327951)
              ·
                refine ⟨60832935259882301364491927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40555290173254867576327951 60832935259882301364491927)
                ·
                  refine ⟨91249402889823452046737891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60832935259882301364491927 91249402889823452046737891)
                  ·
                    refine ⟨136874104334735178070106837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91249402889823452046737891 136874104334735178070106837)
                    ·
                      refine ⟨3207986820345355736018129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136874104334735178070106837 3207986820345355736018129)
                      ·
                        rfl

theorem cell23_6247532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_6247532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247532 prefixEnd_6247532 := by exact prefixLift 6247532
  have htrace : WordTrace (prefixWord ++ tailWord_6247532) baseStart_6247532 baseEnd_6247532 := by
    simpa [prefixWord, tailWord_6247532, baseEnd_6247532] using wordTrace_append hprefix tailTrace_6247532
  have hstable : (prefixWord ++ tailWord_6247532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247532).length < 2 ^ (prefixWord ++ tailWord_6247532).sum := by decide
  have hdescent : baseEnd_6247532 < baseStart_6247532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247559 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_6247559 : Nat := 118140960795 + 6247559 * 2 ^ 59
def prefixEnd_6247559 : Nat := 4983230072969 + 3 ^ 40 * 6247559 * 2
def baseEnd_6247559 : Nat := 3208000684323027130380505

theorem tailTrace_6247559 : CollatzResearch.WordTrace tailWord_6247559 prefixEnd_6247559 3208000684323027130380505 := by
  unfold tailWord_6247559
  simp only [CollatzResearch.WordTrace]
  refine ⟨227867196773168215974249731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151911464515445477316166487 227867196773168215974249731)
  ·
    refine ⟨341800795159752323961374597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227867196773168215974249731 341800795159752323961374597)
    ·
      refine ⟨64087649092453560742757737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341800795159752323961374597 64087649092453560742757737)
      ·
        refine ⟨48065736819340170557068303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64087649092453560742757737 48065736819340170557068303)
        ·
          refine ⟨72098605229010255835602455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48065736819340170557068303 72098605229010255835602455)
          ·
            refine ⟨108147907843515383753403683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72098605229010255835602455 108147907843515383753403683)
            ·
              refine ⟨162221861765273075630105525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108147907843515383753403683 162221861765273075630105525)
              ·
                refine ⟨15208299540494350840322393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162221861765273075630105525 15208299540494350840322393)
                ·
                  refine ⟨11406224655370763130241795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15208299540494350840322393 11406224655370763130241795)
                  ·
                    refine ⟨17109336983056144695362693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406224655370763130241795 17109336983056144695362693)
                    ·
                      refine ⟨3208000684323027130380505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17109336983056144695362693 3208000684323027130380505)
                      ·
                        rfl

theorem cell23_6247559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_6247559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247559 prefixEnd_6247559 := by exact prefixLift 6247559
  have htrace : WordTrace (prefixWord ++ tailWord_6247559) baseStart_6247559 baseEnd_6247559 := by
    simpa [prefixWord, tailWord_6247559, baseEnd_6247559] using wordTrace_append hprefix tailTrace_6247559
  have hstable : (prefixWord ++ tailWord_6247559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247559).length < 2 ^ (prefixWord ++ tailWord_6247559).sum := by decide
  have hdescent : baseEnd_6247559 < baseStart_6247559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247560 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 5]
def baseStart_6247560 : Nat := 118140960795 + 6247560 * 2 ^ 59
def prefixEnd_6247560 : Nat := 4983230072969 + 3 ^ 40 * 6247560 * 2
def baseEnd_6247560 : Nat := 356444577533742402940889

theorem tailTrace_6247560 : CollatzResearch.WordTrace tailWord_6247560 prefixEnd_6247560 356444577533742402940889 := by
  unfold tailWord_6247560
  simp only [CollatzResearch.WordTrace]
  refine ⟨113933616623082296572518067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151911488830776395430024089 113933616623082296572518067)
  ·
    refine ⟨170900424934623444858777101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113933616623082296572518067 170900424934623444858777101)
    ·
      refine ⟨64087659350483791822041413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170900424934623444858777101 64087659350483791822041413)
      ·
        refine ⟨12016436128215710966632765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64087659350483791822041413 12016436128215710966632765)
        ·
          refine ⟨4506163548080891612487287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12016436128215710966632765 4506163548080891612487287)
          ·
            refine ⟨6759245322121337418730931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506163548080891612487287 6759245322121337418730931)
            ·
              refine ⟨10138867983182006128096397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759245322121337418730931 10138867983182006128096397)
              ·
                refine ⟨3802075493693252298036149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10138867983182006128096397 3802075493693252298036149)
                ·
                  refine ⟨356444577533742402940889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3802075493693252298036149 356444577533742402940889)
                  ·
                    rfl

theorem cell23_6247560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 5].length) (baseStart_6247560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247560 prefixEnd_6247560 := by exact prefixLift 6247560
  have htrace : WordTrace (prefixWord ++ tailWord_6247560) baseStart_6247560 baseEnd_6247560 := by
    simpa [prefixWord, tailWord_6247560, baseEnd_6247560] using wordTrace_append hprefix tailTrace_6247560
  have hstable : (prefixWord ++ tailWord_6247560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247560).length < 2 ^ (prefixWord ++ tailWord_6247560).sum := by decide
  have hdescent : baseEnd_6247560 < baseStart_6247560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247576 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6247576 : Nat := 118140960795 + 6247576 * 2 ^ 59
def prefixEnd_6247576 : Nat := 4983230072969 + 3 ^ 40 * 6247576 * 2
def baseEnd_6247576 : Nat := 3208009413494153563867927

theorem tailTrace_6247576 : CollatzResearch.WordTrace tailWord_6247576 prefixEnd_6247576 3208009413494153563867927 := by
  unfold tailWord_6247576
  simp only [CollatzResearch.WordTrace]
  refine ⟨113933908407053313938809291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151911877876071085251745721 113933908407053313938809291)
  ·
    refine ⟨170900862610579970908213937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113933908407053313938809291 170900862610579970908213937)
    ·
      refine ⟨128175646957934978181160453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170900862610579970908213937 128175646957934978181160453)
      ·
        refine ⟨24032933804612808408967585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128175646957934978181160453 24032933804612808408967585)
        ·
          refine ⟨18024700353459606306725689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24032933804612808408967585 18024700353459606306725689)
          ·
            refine ⟨13518525265094704730044267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18024700353459606306725689 13518525265094704730044267)
            ·
              refine ⟨20277787897642057095066401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13518525265094704730044267 20277787897642057095066401)
              ·
                refine ⟨15208340923231542821299801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20277787897642057095066401 15208340923231542821299801)
                ·
                  refine ⟨11406255692423657115974851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15208340923231542821299801 11406255692423657115974851)
                  ·
                    refine ⟨17109383538635485673962277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406255692423657115974851 17109383538635485673962277)
                    ·
                      refine ⟨3208009413494153563867927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17109383538635485673962277 3208009413494153563867927)
                      ·
                        rfl

theorem cell23_6247576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6247576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247576 prefixEnd_6247576 := by exact prefixLift 6247576
  have htrace : WordTrace (prefixWord ++ tailWord_6247576) baseStart_6247576 baseEnd_6247576 := by
    simpa [prefixWord, tailWord_6247576, baseEnd_6247576] using wordTrace_append hprefix tailTrace_6247576
  have hstable : (prefixWord ++ tailWord_6247576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247576).length < 2 ^ (prefixWord ++ tailWord_6247576).sum := by decide
  have hdescent : baseEnd_6247576 < baseStart_6247576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247637 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_6247637 : Nat := 118140960795 + 6247637 * 2 ^ 59
def prefixEnd_6247637 : Nat := 4983230072969 + 3 ^ 40 * 6247637 * 2
def baseEnd_6247637 : Nat := 1069346911938025941735049

theorem tailTrace_6247637 : CollatzResearch.WordTrace tailWord_6247637 prefixEnd_6247637 1069346911938025941735049 := by
  unfold tailWord_6247637
  simp only [CollatzResearch.WordTrace]
  refine ⟨227870041666885635295589165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151913361111257090197059443 227870041666885635295589165)
  ·
    refine ⟨85451265625082113235845937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227870041666885635295589165 85451265625082113235845937)
    ·
      refine ⟨64088449218811584926884453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85451265625082113235845937 64088449218811584926884453)
      ·
        refine ⟨12016584228527172173790835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64088449218811584926884453 12016584228527172173790835)
        ·
          refine ⟨18024876342790758260686253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016584228527172173790835 18024876342790758260686253)
          ·
            refine ⟨6759328628546534347757345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18024876342790758260686253 6759328628546534347757345)
            ·
              refine ⟨5069496471409900760818009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6759328628546534347757345 5069496471409900760818009)
              ·
                refine ⟨3802122353557425570613507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069496471409900760818009 3802122353557425570613507)
                ·
                  refine ⟨5703183530336138355920261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802122353557425570613507 5703183530336138355920261)
                  ·
                    refine ⟨1069346911938025941735049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703183530336138355920261 1069346911938025941735049)
                    ·
                      rfl

theorem cell23_6247637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_6247637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247637 prefixEnd_6247637 := by exact prefixLift 6247637
  have htrace : WordTrace (prefixWord ++ tailWord_6247637) baseStart_6247637 baseEnd_6247637 := by
    simpa [prefixWord, tailWord_6247637, baseEnd_6247637] using wordTrace_append hprefix tailTrace_6247637
  have hstable : (prefixWord ++ tailWord_6247637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247637).length < 2 ^ (prefixWord ++ tailWord_6247637).sum := by decide
  have hdescent : baseEnd_6247637 < baseStart_6247637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247659 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 1, 6]
def baseStart_6247659 : Nat := 118140960795 + 6247659 * 2 ^ 59
def prefixEnd_6247659 : Nat := 4983230072969 + 3 ^ 40 * 6247659 * 2
def baseEnd_6247659 : Nat := 1069350677462825579710015

theorem tailTrace_6247659 : CollatzResearch.WordTrace tailWord_6247659 prefixEnd_6247659 1069350677462825579710015 := by
  unfold tailWord_6247659
  simp only [CollatzResearch.WordTrace]
  refine ⟨227870844072805933052890031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151913896048537288701926687 227870844072805933052890031)
  ·
    refine ⟨341806266109208899579335047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227870844072805933052890031 341806266109208899579335047)
    ·
      refine ⟨512709399163813349369002571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341806266109208899579335047 512709399163813349369002571)
      ·
        refine ⟨769064098745720024053503857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512709399163813349369002571 769064098745720024053503857)
        ·
          refine ⟨576798074059290018040127893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769064098745720024053503857 576798074059290018040127893)
          ·
            refine ⟨27037409721529219595630995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 576798074059290018040127893 27037409721529219595630995)
            ·
              refine ⟨40556114582293829393446493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27037409721529219595630995 40556114582293829393446493)
              ·
                refine ⟨15208542968360186022542435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40556114582293829393446493 15208542968360186022542435)
                ·
                  refine ⟨22812814452540279033813653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15208542968360186022542435 22812814452540279033813653)
                  ·
                    refine ⟨1069350677462825579710015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22812814452540279033813653 1069350677462825579710015)
                    ·
                      rfl

theorem cell23_6247659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 6].length) (baseStart_6247659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247659 prefixEnd_6247659 := by exact prefixLift 6247659
  have htrace : WordTrace (prefixWord ++ tailWord_6247659) baseStart_6247659 baseEnd_6247659 := by
    simpa [prefixWord, tailWord_6247659, baseEnd_6247659] using wordTrace_append hprefix tailTrace_6247659
  have hstable : (prefixWord ++ tailWord_6247659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247659).length < 2 ^ (prefixWord ++ tailWord_6247659).sum := by decide
  have hdescent : baseEnd_6247659 < baseStart_6247659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247683 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 1, 1, 4]
def baseStart_6247683 : Nat := 118140960795 + 6247683 * 2 ^ 59
def prefixEnd_6247683 : Nat := 4983230072969 + 3 ^ 40 * 6247683 * 2
def baseEnd_6247683 : Nat := 3208064355924184645229935

theorem tailTrace_6247683 : CollatzResearch.WordTrace tailWord_6247683 prefixEnd_6247683 3208064355924184645229935 := by
  unfold tailWord_6247683
  simp only [CollatzResearch.WordTrace]
  refine ⟨227871719424718985151763703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151914479616479323434509135 227871719424718985151763703)
  ·
    refine ⟨341807579137078477727645555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227871719424718985151763703 341807579137078477727645555)
    ·
      refine ⟨512711368705617716591468333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341807579137078477727645555 512711368705617716591468333)
      ·
        refine ⟨192266763264606643721800625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512711368705617716591468333 192266763264606643721800625)
        ·
          refine ⟨144200072448454982791350469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192266763264606643721800625 144200072448454982791350469)
          ·
            refine ⟨27037513584085309273378213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144200072448454982791350469 27037513584085309273378213)
            ·
              refine ⟨5069533797015995488758415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27037513584085309273378213 5069533797015995488758415)
              ·
                refine ⟨7604300695523993233137623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069533797015995488758415 7604300695523993233137623)
                ·
                  refine ⟨11406451043285989849706435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604300695523993233137623 11406451043285989849706435)
                  ·
                    refine ⟨17109676564928984774559653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406451043285989849706435 17109676564928984774559653)
                    ·
                      refine ⟨3208064355924184645229935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17109676564928984774559653 3208064355924184645229935)
                      ·
                        rfl

theorem cell23_6247683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_6247683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247683 prefixEnd_6247683 := by exact prefixLift 6247683
  have htrace : WordTrace (prefixWord ++ tailWord_6247683) baseStart_6247683 baseEnd_6247683 := by
    simpa [prefixWord, tailWord_6247683, baseEnd_6247683] using wordTrace_append hprefix tailTrace_6247683
  have hstable : (prefixWord ++ tailWord_6247683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247683).length < 2 ^ (prefixWord ++ tailWord_6247683).sum := by decide
  have hdescent : baseEnd_6247683 < baseStart_6247683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247699 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3]
def baseStart_6247699 : Nat := 118140960795 + 6247699 * 2 ^ 59
def prefixEnd_6247699 : Nat := 4983230072969 + 3 ^ 40 * 6247699 * 2
def baseEnd_6247699 : Nat := 3208072571614656582629861

theorem tailTrace_6247699 : CollatzResearch.WordTrace tailWord_6247699 prefixEnd_6247699 3208072571614656582629861 := by
  unfold tailWord_6247699
  simp only [CollatzResearch.WordTrace]
  refine ⟨227872302992661019884346151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151914868661774013256230767 227872302992661019884346151)
  ·
    refine ⟨341808454488991529826519227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227872302992661019884346151 341808454488991529826519227)
    ·
      refine ⟨512712681733487294739778841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341808454488991529826519227 512712681733487294739778841)
      ·
        refine ⟨384534511300115471054834131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512712681733487294739778841 384534511300115471054834131)
        ·
          refine ⟨576801766950173206582251197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384534511300115471054834131 576801766950173206582251197)
          ·
            refine ⟨216300662606314952468344199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576801766950173206582251197 216300662606314952468344199)
            ·
              refine ⟨324450993909472428702516299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216300662606314952468344199 324450993909472428702516299)
              ·
                refine ⟨486676490864208643053774449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324450993909472428702516299 486676490864208643053774449)
                ·
                  refine ⟨365007368148156482290330837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486676490864208643053774449 365007368148156482290330837)
                  ·
                    refine ⟨8554860190972417553679629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 365007368148156482290330837 8554860190972417553679629)
                    ·
                      refine ⟨3208072571614656582629861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554860190972417553679629 3208072571614656582629861)
                      ·
                        rfl

theorem cell23_6247699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_6247699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247699 prefixEnd_6247699 := by exact prefixLift 6247699
  have htrace : WordTrace (prefixWord ++ tailWord_6247699) baseStart_6247699 baseEnd_6247699 := by
    simpa [prefixWord, tailWord_6247699, baseEnd_6247699] using wordTrace_append hprefix tailTrace_6247699
  have hstable : (prefixWord ++ tailWord_6247699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247699).length < 2 ^ (prefixWord ++ tailWord_6247699).sum := by decide
  have hdescent : baseEnd_6247699 < baseStart_6247699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247720 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_6247720 : Nat := 118140960795 + 6247720 * 2 ^ 59
def prefixEnd_6247720 : Nat := 4983230072969 + 3 ^ 40 * 6247720 * 2
def baseEnd_6247720 : Nat := 3208083354708401000467265

theorem tailTrace_6247720 : CollatzResearch.WordTrace tailWord_6247720 prefixEnd_6247720 3208083354708401000467265 := by
  unfold tailWord_6247720
  simp only [CollatzResearch.WordTrace]
  refine ⟨113936534462792470235430307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151915379283723293647240409 113936534462792470235430307)
  ·
    refine ⟨170904801694188705353145461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113936534462792470235430307 170904801694188705353145461)
    ·
      refine ⟨16022325158830191126857387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170904801694188705353145461 16022325158830191126857387)
      ·
        refine ⟨24033487738245286690286081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16022325158830191126857387 24033487738245286690286081)
        ·
          refine ⟨18025115803683965017714561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24033487738245286690286081 18025115803683965017714561)
          ·
            refine ⟨13518836852762973763285921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18025115803683965017714561 13518836852762973763285921)
            ·
              refine ⟨10139127639572230322464441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13518836852762973763285921 10139127639572230322464441)
              ·
                refine ⟨7604345729679172741848331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10139127639572230322464441 7604345729679172741848331)
                ·
                  refine ⟨11406518594518759112772497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604345729679172741848331 11406518594518759112772497)
                  ·
                    refine ⟨8554888945889069334579373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11406518594518759112772497 8554888945889069334579373)
                    ·
                      refine ⟨3208083354708401000467265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554888945889069334579373 3208083354708401000467265)
                      ·
                        rfl

theorem cell23_6247720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_6247720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247720 prefixEnd_6247720 := by exact prefixLift 6247720
  have htrace : WordTrace (prefixWord ++ tailWord_6247720) baseStart_6247720 baseEnd_6247720 := by
    simpa [prefixWord, tailWord_6247720, baseEnd_6247720] using wordTrace_append hprefix tailTrace_6247720
  have hstable : (prefixWord ++ tailWord_6247720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247720).length < 2 ^ (prefixWord ++ tailWord_6247720).sum := by decide
  have hdescent : baseEnd_6247720 < baseStart_6247720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247733 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_6247733 : Nat := 118140960795 + 6247733 * 2 ^ 59
def prefixEnd_6247733 : Nat := 4983230072969 + 3 ^ 40 * 6247733 * 2
def baseEnd_6247733 : Nat := 3208090029956909449604705

theorem tailTrace_6247733 : CollatzResearch.WordTrace tailWord_6247733 prefixEnd_6247733 3208090029956909449604705 := by
  unfold tailWord_6247733
  simp only [CollatzResearch.WordTrace]
  refine ⟨227873543074537843691083853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151915695383025229127389235 227873543074537843691083853)
  ·
    refine ⟨85452578652951691384156445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227873543074537843691083853 85452578652951691384156445)
    ·
      refine ⟨32044716994856884269058667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85452578652951691384156445 32044716994856884269058667)
      ·
        refine ⟨48067075492285326403588001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32044716994856884269058667 48067075492285326403588001)
        ·
          refine ⟨36050306619213994802691001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48067075492285326403588001 36050306619213994802691001)
          ·
            refine ⟨27037729964410496102018251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36050306619213994802691001 27037729964410496102018251)
            ·
              refine ⟨40556594946615744153027377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27037729964410496102018251 40556594946615744153027377)
              ·
                refine ⟨30417446209961808114770533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40556594946615744153027377 30417446209961808114770533)
                ·
                  refine ⟨5703271164367839021519475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30417446209961808114770533 5703271164367839021519475)
                  ·
                    refine ⟨8554906746551758532279213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703271164367839021519475 8554906746551758532279213)
                    ·
                      refine ⟨3208090029956909449604705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554906746551758532279213 3208090029956909449604705)
                      ·
                        rfl

theorem cell23_6247733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_6247733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247733 prefixEnd_6247733 := by exact prefixLift 6247733
  have htrace : WordTrace (prefixWord ++ tailWord_6247733) baseStart_6247733 baseEnd_6247733 := by
    simpa [prefixWord, tailWord_6247733, baseEnd_6247733] using wordTrace_append hprefix tailTrace_6247733
  have hstable : (prefixWord ++ tailWord_6247733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247733).length < 2 ^ (prefixWord ++ tailWord_6247733).sum := by decide
  have hdescent : baseEnd_6247733 < baseStart_6247733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247749 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_6247749 : Nat := 118140960795 + 6247749 * 2 ^ 59
def prefixEnd_6247749 : Nat := 4983230072969 + 3 ^ 40 * 6247749 * 2
def baseEnd_6247749 : Nat := 1069366081882460462334877

theorem tailTrace_6247749 : CollatzResearch.WordTrace tailWord_6247749 prefixEnd_6247749 1069366081882460462334877 := by
  unfold tailWord_6247749
  simp only [CollatzResearch.WordTrace]
  refine ⟨227874126642479878423666301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151916084428319918949110867 227874126642479878423666301)
  ·
    refine ⟨85452797490929954408874863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227874126642479878423666301 85452797490929954408874863)
    ·
      refine ⟨128179196236394931613312295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85452797490929954408874863 128179196236394931613312295)
      ·
        refine ⟨192268794354592397419968443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128179196236394931613312295 192268794354592397419968443)
        ·
          refine ⟨288403191531888596129952665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192268794354592397419968443 288403191531888596129952665)
          ·
            refine ⟨216302393648916447097464499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288403191531888596129952665 216302393648916447097464499)
            ·
              refine ⟨324453590473374670646196749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216302393648916447097464499 324453590473374670646196749)
              ·
                refine ⟨121670096427515501492323781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324453590473374670646196749 121670096427515501492323781)
                ·
                  refine ⟨22813143080159156529810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121670096427515501492323781 22813143080159156529810709)
                  ·
                    refine ⟨1069366081882460462334877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22813143080159156529810709 1069366081882460462334877)
                    ·
                      rfl

theorem cell23_6247749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_6247749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247749 prefixEnd_6247749 := by exact prefixLift 6247749
  have htrace : WordTrace (prefixWord ++ tailWord_6247749) baseStart_6247749 baseEnd_6247749 := by
    simpa [prefixWord, tailWord_6247749, baseEnd_6247749] using wordTrace_append hprefix tailTrace_6247749
  have hstable : (prefixWord ++ tailWord_6247749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247749).length < 2 ^ (prefixWord ++ tailWord_6247749).sum := by decide
  have hdescent : baseEnd_6247749 < baseStart_6247749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247767 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_6247767 : Nat := 118140960795 + 6247767 * 2 ^ 59
def prefixEnd_6247767 : Nat := 4983230072969 + 3 ^ 40 * 6247767 * 2
def baseEnd_6247767 : Nat := 3208107488299162316579549

theorem tailTrace_6247767 : CollatzResearch.WordTrace tailWord_6247767 prefixEnd_6247767 3208107488299162316579549 := by
  unfold tailWord_6247767
  simp only [CollatzResearch.WordTrace]
  refine ⟨227874783156414667497821555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151916522104276444998547703 227874783156414667497821555)
  ·
    refine ⟨341812174734622001246732333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227874783156414667497821555 341812174734622001246732333)
    ·
      refine ⟨128179565525483250467524625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341812174734622001246732333 128179565525483250467524625)
      ·
        refine ⟨96134674144112437850643469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128179565525483250467524625 96134674144112437850643469)
        ·
          refine ⟨36050502804042164193991301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96134674144112437850643469 36050502804042164193991301)
          ·
            refine ⟨6759469275757905786373369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36050502804042164193991301 6759469275757905786373369)
            ·
              refine ⟨5069601956818429339780027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6759469275757905786373369 5069601956818429339780027)
              ·
                refine ⟨7604402935227644009670041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069601956818429339780027 7604402935227644009670041)
                ·
                  refine ⟨5703302201420733007252531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7604402935227644009670041 5703302201420733007252531)
                  ·
                    refine ⟨8554953302131099510878797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703302201420733007252531 8554953302131099510878797)
                    ·
                      refine ⟨3208107488299162316579549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8554953302131099510878797 3208107488299162316579549)
                      ·
                        rfl

theorem cell23_6247767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_6247767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247767 prefixEnd_6247767 := by exact prefixLift 6247767
  have htrace : WordTrace (prefixWord ++ tailWord_6247767) baseStart_6247767 baseEnd_6247767 := by
    simpa [prefixWord, tailWord_6247767, baseEnd_6247767] using wordTrace_append hprefix tailTrace_6247767
  have hstable : (prefixWord ++ tailWord_6247767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247767).length < 2 ^ (prefixWord ++ tailWord_6247767).sum := by decide
  have hdescent : baseEnd_6247767 < baseStart_6247767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247776 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_6247776 : Nat := 118140960795 + 6247776 * 2 ^ 59
def prefixEnd_6247776 : Nat := 4983230072969 + 3 ^ 40 * 6247776 * 2
def baseEnd_6247776 : Nat := 3208112109625052781367007

theorem tailTrace_6247776 : CollatzResearch.WordTrace tailWord_6247776 prefixEnd_6247776 3208112109625052781367007 := by
  unfold tailWord_6247776
  simp only [CollatzResearch.WordTrace]
  refine ⟨113937555706691031017449591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151916740942254708023266121 113937555706691031017449591)
  ·
    refine ⟨170906333560036546526174387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113937555706691031017449591 170906333560036546526174387)
    ·
      refine ⟨256359500340054819789261581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170906333560036546526174387 256359500340054819789261581)
      ·
        refine ⟨96134812627520557420973093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256359500340054819789261581 96134812627520557420973093)
        ·
          refine ⟨18025277367660104516432455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96134812627520557420973093 18025277367660104516432455)
          ·
            refine ⟨27037916051490156774648683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18025277367660104516432455 27037916051490156774648683)
            ·
              refine ⟨40556874077235235161973025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27037916051490156774648683 40556874077235235161973025)
              ·
                refine ⟨30417655557926426371479769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40556874077235235161973025 30417655557926426371479769)
                ·
                  refine ⟨22813241668444819778609827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30417655557926426371479769 22813241668444819778609827)
                  ·
                    refine ⟨34219862502667229667914741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22813241668444819778609827 34219862502667229667914741)
                    ·
                      refine ⟨3208112109625052781367007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34219862502667229667914741 3208112109625052781367007)
                      ·
                        rfl

theorem cell23_6247776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_6247776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247776 prefixEnd_6247776 := by exact prefixLift 6247776
  have htrace : WordTrace (prefixWord ++ tailWord_6247776) baseStart_6247776 baseEnd_6247776 := by
    simpa [prefixWord, tailWord_6247776, baseEnd_6247776] using wordTrace_append hprefix tailTrace_6247776
  have hstable : (prefixWord ++ tailWord_6247776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247776).length < 2 ^ (prefixWord ++ tailWord_6247776).sum := by decide
  have hdescent : baseEnd_6247776 < baseStart_6247776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247810 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6247810 : Nat := 118140960795 + 6247810 * 2 ^ 59
def prefixEnd_6247810 : Nat := 4983230072969 + 3 ^ 40 * 6247810 * 2
def baseEnd_6247810 : Nat := 3208129567967305648341851

theorem tailTrace_6247810 : CollatzResearch.WordTrace tailWord_6247810 prefixEnd_6247810 3208129567967305648341851 := by
  unfold tailWord_6247810
  simp only [CollatzResearch.WordTrace]
  refine ⟨56969087873814721460409221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151917567663505923894424589 56969087873814721460409221)
  ·
    refine ⟨10681703976340260273826729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56969087873814721460409221 10681703976340260273826729)
    ·
      refine ⟨8011277982255195205370047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10681703976340260273826729 8011277982255195205370047)
      ·
        refine ⟨12016916973382792808055071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8011277982255195205370047 12016916973382792808055071)
        ·
          refine ⟨18025375460074189212082607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016916973382792808055071 18025375460074189212082607)
          ·
            refine ⟨27038063190111283818123911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18025375460074189212082607 27038063190111283818123911)
            ·
              refine ⟨40557094785166925727185867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27038063190111283818123911 40557094785166925727185867)
              ·
                refine ⟨60835642177750388590778801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40557094785166925727185867 60835642177750388590778801)
                ·
                  refine ⟨45626731633312791443084101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60835642177750388590778801 45626731633312791443084101)
                  ·
                    refine ⟨8555012181246148395578269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45626731633312791443084101 8555012181246148395578269)
                    ·
                      refine ⟨3208129567967305648341851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555012181246148395578269 3208129567967305648341851)
                      ·
                        rfl

theorem cell23_6247810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6247810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247810 prefixEnd_6247810 := by exact prefixLift 6247810
  have htrace : WordTrace (prefixWord ++ tailWord_6247810) baseStart_6247810 baseEnd_6247810 := by
    simpa [prefixWord, tailWord_6247810, baseEnd_6247810] using wordTrace_append hprefix tailTrace_6247810
  have hstable : (prefixWord ++ tailWord_6247810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247810).length < 2 ^ (prefixWord ++ tailWord_6247810).sum := by decide
  have hdescent : baseEnd_6247810 < baseStart_6247810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247863 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_6247863 : Nat := 118140960795 + 6247863 * 2 ^ 59
def prefixEnd_6247863 : Nat := 4983230072969 + 3 ^ 40 * 6247863 * 2
def baseEnd_6247863 : Nat := 3208156782441993940979107

theorem tailTrace_6247863 : CollatzResearch.WordTrace tailWord_6247863 prefixEnd_6247863 3208156782441993940979107 := by
  unfold tailWord_6247863
  simp only [CollatzResearch.WordTrace]
  refine ⟨227878284564066875893316243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151918856376044583928877495 227878284564066875893316243)
  ·
    refine ⟨341817426846100313839974365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227878284564066875893316243 341817426846100313839974365)
    ·
      refine ⟨128181535067287617689990387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341817426846100313839974365 128181535067287617689990387)
      ·
        refine ⟨192272302600931426534985581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128181535067287617689990387 192272302600931426534985581)
        ·
          refine ⟨72102113475349284950619593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192272302600931426534985581 72102113475349284950619593)
          ·
            refine ⟨54076585106511963712964695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72102113475349284950619593 54076585106511963712964695)
            ·
              refine ⟨81114877659767945569447043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54076585106511963712964695 81114877659767945569447043)
              ·
                refine ⟨121672316489651918354170565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81114877659767945569447043 121672316489651918354170565)
                ·
                  refine ⟨22813559341809734691406981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121672316489651918354170565 22813559341809734691406981)
                  ·
                    refine ⟨4277542376589325254638809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22813559341809734691406981 4277542376589325254638809)
                    ·
                      refine ⟨3208156782441993940979107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277542376589325254638809 3208156782441993940979107)
                      ·
                        rfl

theorem cell23_6247863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_6247863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247863 prefixEnd_6247863 := by exact prefixLift 6247863
  have htrace : WordTrace (prefixWord ++ tailWord_6247863) baseStart_6247863 baseEnd_6247863 := by
    simpa [prefixWord, tailWord_6247863, baseEnd_6247863] using wordTrace_append hprefix tailTrace_6247863
  have hstable : (prefixWord ++ tailWord_6247863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247863).length < 2 ^ (prefixWord ++ tailWord_6247863).sum := by decide
  have hdescent : baseEnd_6247863 < baseStart_6247863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247907 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 1, 4]
def baseStart_6247907 : Nat := 118140960795 + 6247907 * 2 ^ 59
def prefixEnd_6247907 : Nat := 4983230072969 + 3 ^ 40 * 6247907 * 2
def baseEnd_6247907 : Nat := 1069393125196930589609635

theorem tailTrace_6247907 : CollatzResearch.WordTrace tailWord_6247907 prefixEnd_6247907 1069393125196930589609635 := by
  unfold tailWord_6247907
  simp only [CollatzResearch.WordTrace]
  refine ⟨227879889375907471407917975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151919926250604980938611983 227879889375907471407917975)
  ·
    refine ⟨341819834063861207111876963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227879889375907471407917975 341819834063861207111876963)
    ·
      refine ⟨512729751095791810667815445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341819834063861207111876963 512729751095791810667815445)
      ·
        refine ⟨24034207082615241125053849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 512729751095791810667815445 24034207082615241125053849)
        ·
          refine ⟨18025655311961430843790387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24034207082615241125053849 18025655311961430843790387)
          ·
            refine ⟨27038482967942146265685581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18025655311961430843790387 27038482967942146265685581)
            ·
              refine ⟨10139431112978304849632093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27038482967942146265685581 10139431112978304849632093)
              ·
                refine ⟨3802286667366864318612035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10139431112978304849632093 3802286667366864318612035)
                ·
                  refine ⟨5703430001050296477918053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802286667366864318612035 5703430001050296477918053)
                  ·
                    refine ⟨1069393125196930589609635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703430001050296477918053 1069393125196930589609635)
                    ·
                      rfl

theorem cell23_6247907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 4].length) (baseStart_6247907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247907 prefixEnd_6247907 := by exact prefixLift 6247907
  have htrace : WordTrace (prefixWord ++ tailWord_6247907) baseStart_6247907 baseEnd_6247907 := by
    simpa [prefixWord, tailWord_6247907, baseEnd_6247907] using wordTrace_append hprefix tailTrace_6247907
  have hstable : (prefixWord ++ tailWord_6247907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247907).length < 2 ^ (prefixWord ++ tailWord_6247907).sum := by decide
  have hdescent : baseEnd_6247907 < baseStart_6247907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247917 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6247917 : Nat := 118140960795 + 6247917 * 2 ^ 59
def prefixEnd_6247917 : Nat := 4983230072969 + 3 ^ 40 * 6247917 * 2
def baseEnd_6247917 : Nat := 3208184510397336729703859

theorem tailTrace_6247917 : CollatzResearch.WordTrace tailWord_6247917 prefixEnd_6247917 3208184510397336729703859 := by
  unfold tailWord_6247917
  simp only [CollatzResearch.WordTrace]
  refine ⟨227880254105871243115782005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151920169403914162077188003 227880254105871243115782005)
  ·
    refine ⟨21363773822425429042104563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227880254105871243115782005 21363773822425429042104563)
    ·
      refine ⟨32045660733638143563156845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21363773822425429042104563 32045660733638143563156845)
      ·
        refine ⟨12017122775114303836183817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32045660733638143563156845 12017122775114303836183817)
        ·
          refine ⟨9012842081335727877137863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12017122775114303836183817 9012842081335727877137863)
          ·
            refine ⟨13519263122003591815706795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9012842081335727877137863 13519263122003591815706795)
            ·
              refine ⟨20278894683005387723560193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519263122003591815706795 20278894683005387723560193)
              ·
                refine ⟨15209171012254040792670145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20278894683005387723560193 15209171012254040792670145)
                ·
                  refine ⟨11406878259190530594502609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15209171012254040792670145 11406878259190530594502609)
                  ·
                    refine ⟨8555158694392897945876957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11406878259190530594502609 8555158694392897945876957)
                    ·
                      refine ⟨3208184510397336729703859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555158694392897945876957 3208184510397336729703859)
                      ·
                        rfl

theorem cell23_6247917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6247917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247917 prefixEnd_6247917 := by exact prefixLift 6247917
  have htrace : WordTrace (prefixWord ++ tailWord_6247917) baseStart_6247917 baseEnd_6247917 := by
    simpa [prefixWord, tailWord_6247917, baseEnd_6247917] using wordTrace_append hprefix tailTrace_6247917
  have hstable : (prefixWord ++ tailWord_6247917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247917).length < 2 ^ (prefixWord ++ tailWord_6247917).sum := by decide
  have hdescent : baseEnd_6247917 < baseStart_6247917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247923 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 5, 2]
def baseStart_6247923 : Nat := 118140960795 + 6247923 * 2 ^ 59
def prefixEnd_6247923 : Nat := 4983230072969 + 3 ^ 40 * 6247923 * 2
def baseEnd_6247923 : Nat := 3208187591281263706228831

theorem tailTrace_6247923 : CollatzResearch.WordTrace tailWord_6247923 prefixEnd_6247923 3208187591281263706228831 := by
  unfold tailWord_6247923
  simp only [CollatzResearch.WordTrace]
  refine ⟨227880472943849506140500423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151920315295899670760333615 227880472943849506140500423)
  ·
    refine ⟨341820709415774259210750635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227880472943849506140500423 341820709415774259210750635)
    ·
      refine ⟨512731064123661388816125953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341820709415774259210750635 512731064123661388816125953)
      ·
        refine ⟨384548298092746041612094465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512731064123661388816125953 384548298092746041612094465)
        ·
          refine ⟨288411223569559531209070849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384548298092746041612094465 288411223569559531209070849)
          ·
            refine ⟨216308417677169648406803137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288411223569559531209070849 216308417677169648406803137)
            ·
              refine ⟨162231313257877236305102353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216308417677169648406803137 162231313257877236305102353)
              ·
                refine ⟨121673484943407927228826765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162231313257877236305102353 121673484943407927228826765)
                ·
                  refine ⟨45627556853777972710810037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121673484943407927228826765 45627556853777972710810037)
                  ·
                    refine ⟨4277583455041684941638441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45627556853777972710810037 4277583455041684941638441)
                    ·
                      refine ⟨3208187591281263706228831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277583455041684941638441 3208187591281263706228831)
                      ·
                        rfl

theorem cell23_6247923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5, 2].length) (baseStart_6247923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247923 prefixEnd_6247923 := by exact prefixLift 6247923
  have htrace : WordTrace (prefixWord ++ tailWord_6247923) baseStart_6247923 baseEnd_6247923 := by
    simpa [prefixWord, tailWord_6247923, baseEnd_6247923] using wordTrace_append hprefix tailTrace_6247923
  have hstable : (prefixWord ++ tailWord_6247923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247923).length < 2 ^ (prefixWord ++ tailWord_6247923).sum := by decide
  have hdescent : baseEnd_6247923 < baseStart_6247923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247937 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 6]
def baseStart_6247937 : Nat := 118140960795 + 6247937 * 2 ^ 59
def prefixEnd_6247937 : Nat := 4983230072969 + 3 ^ 40 * 6247937 * 2
def baseEnd_6247937 : Nat := 356466086667825183494863

theorem tailTrace_6247937 : CollatzResearch.WordTrace tailWord_6247937 prefixEnd_6247937 356466086667825183494863 := by
  unfold tailWord_6247937
  simp only [CollatzResearch.WordTrace]
  refine ⟨227880983565798786531510065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151920655710532524354340043 227880983565798786531510065)
  ·
    refine ⟨170910737674349089898632549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227880983565798786531510065 170910737674349089898632549)
    ·
      refine ⟨32045763313940454355993603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170910737674349089898632549 32045763313940454355993603)
      ·
        refine ⟨48068644970910681533990405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32045763313940454355993603 48068644970910681533990405)
        ·
          refine ⟨9012870932045752787623201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48068644970910681533990405 9012870932045752787623201)
          ·
            refine ⟨6759653199034314590717401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9012870932045752787623201 6759653199034314590717401)
            ·
              refine ⟨5069739899275735943038051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6759653199034314590717401 5069739899275735943038051)
              ·
                refine ⟨7604609848913603914557077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069739899275735943038051 7604609848913603914557077)
                ·
                  refine ⟨356466086667825183494863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7604609848913603914557077 356466086667825183494863)
                  ·
                    rfl

theorem cell23_6247937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 6].length) (baseStart_6247937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247937 prefixEnd_6247937 := by exact prefixLift 6247937
  have htrace : WordTrace (prefixWord ++ tailWord_6247937) baseStart_6247937 baseEnd_6247937 := by
    simpa [prefixWord, tailWord_6247937, baseEnd_6247937] using wordTrace_append hprefix tailTrace_6247937
  have hstable : (prefixWord ++ tailWord_6247937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247937).length < 2 ^ (prefixWord ++ tailWord_6247937).sum := by decide
  have hdescent : baseEnd_6247937 < baseStart_6247937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247950 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_6247950 : Nat := 118140960795 + 6247950 * 2 ^ 59
def prefixEnd_6247950 : Nat := 4983230072969 + 3 ^ 40 * 6247950 * 2
def baseEnd_6247950 : Nat := 1069400485086311700197069

theorem tailTrace_6247950 : CollatzResearch.WordTrace tailWord_6247950 prefixEnd_6247950 1069400485086311700197069 := by
  unfold tailWord_6247950
  simp only [CollatzResearch.WordTrace]
  refine ⟨28485182214343961218966663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151920971809834459834488869 28485182214343961218966663)
  ·
    refine ⟨42727773321515941828449995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28485182214343961218966663 42727773321515941828449995)
    ·
      refine ⟨64091659982273912742674993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42727773321515941828449995 64091659982273912742674993)
      ·
        refine ⟨48068744986705434557006245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64091659982273912742674993 48068744986705434557006245)
        ·
          refine ⟨9012889685007268979438671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48068744986705434557006245 9012889685007268979438671)
          ·
            refine ⟨13519334527510903469158007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9012889685007268979438671 13519334527510903469158007)
            ·
              refine ⟨20279001791266355203737011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519334527510903469158007 20279001791266355203737011)
              ·
                refine ⟨30418502686899532805605517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20279001791266355203737011 30418502686899532805605517)
                ·
                  refine ⟨11406938507587324802102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30418502686899532805605517 11406938507587324802102069)
                  ·
                    refine ⟨1069400485086311700197069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11406938507587324802102069 1069400485086311700197069)
                    ·
                      rfl

theorem cell23_6247950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_6247950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247950 prefixEnd_6247950 := by exact prefixLift 6247950
  have htrace : WordTrace (prefixWord ++ tailWord_6247950) baseStart_6247950 baseEnd_6247950 := by
    simpa [prefixWord, tailWord_6247950, baseEnd_6247950] using wordTrace_append hprefix tailTrace_6247950
  have hstable : (prefixWord ++ tailWord_6247950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247950).length < 2 ^ (prefixWord ++ tailWord_6247950).sum := by decide
  have hdescent : baseEnd_6247950 < baseStart_6247950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247953 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_6247953 : Nat := 118140960795 + 6247953 * 2 ^ 59
def prefixEnd_6247953 : Nat := 4983230072969 + 3 ^ 40 * 6247953 * 2
def baseEnd_6247953 : Nat := 3208202995700898588853693

theorem tailTrace_6247953 : CollatzResearch.WordTrace tailWord_6247953 prefixEnd_6247953 3208202995700898588853693 := by
  unfold tailWord_6247953
  simp only [CollatzResearch.WordTrace]
  refine ⟨227881567133740821264092513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151921044755827214176061675 227881567133740821264092513)
  ·
    refine ⟨170911175350305615948069385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227881567133740821264092513 170911175350305615948069385)
    ·
      refine ⟨128183381512729211961052039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170911175350305615948069385 128183381512729211961052039)
      ·
        refine ⟨192275072269093817941578059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128183381512729211961052039 192275072269093817941578059)
        ·
          refine ⟨288412608403640726912367089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192275072269093817941578059 288412608403640726912367089)
          ·
            refine ⟨216309456302730545184275317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288412608403640726912367089 216309456302730545184275317)
            ·
              refine ⟨20279011528380988611025811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216309456302730545184275317 20279011528380988611025811)
              ·
                refine ⟨30418517292571482916538717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20279011528380988611025811 30418517292571482916538717)
                ·
                  refine ⟨11406943984714306093702019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30418517292571482916538717 11406943984714306093702019)
                  ·
                    refine ⟨17110415977071459140553029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406943984714306093702019 17110415977071459140553029)
                    ·
                      refine ⟨3208202995700898588853693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17110415977071459140553029 3208202995700898588853693)
                      ·
                        rfl

theorem cell23_6247953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_6247953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247953 prefixEnd_6247953 := by exact prefixLift 6247953
  have htrace : WordTrace (prefixWord ++ tailWord_6247953) baseStart_6247953 baseEnd_6247953 := by
    simpa [prefixWord, tailWord_6247953, baseEnd_6247953] using wordTrace_append hprefix tailTrace_6247953
  have hstable : (prefixWord ++ tailWord_6247953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247953).length < 2 ^ (prefixWord ++ tailWord_6247953).sum := by decide
  have hdescent : baseEnd_6247953 < baseStart_6247953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247957 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_6247957 : Nat := 118140960795 + 6247957 * 2 ^ 59
def prefixEnd_6247957 : Nat := 4983230072969 + 3 ^ 40 * 6247957 * 2
def baseEnd_6247957 : Nat := 3208205049623516573203675

theorem tailTrace_6247957 : CollatzResearch.WordTrace tailWord_6247957 prefixEnd_6247957 3208205049623516573203675 := by
  unfold tailWord_6247957
  simp only [CollatzResearch.WordTrace]
  refine ⟨227881713025726329947238125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151921142017150886631492083 227881713025726329947238125)
  ·
    refine ⟨85455642384647373730214297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227881713025726329947238125 85455642384647373730214297)
    ·
      refine ⟨64091731788485530297660723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85455642384647373730214297 64091731788485530297660723)
      ·
        refine ⟨96137597682728295446491085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64091731788485530297660723 96137597682728295446491085)
        ·
          refine ⟨36051599131023110792434157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96137597682728295446491085 36051599131023110792434157)
          ·
            refine ⟨13519349674133666547162809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36051599131023110792434157 13519349674133666547162809)
            ·
              refine ⟨10139512255600249910372107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13519349674133666547162809 10139512255600249910372107)
              ·
                refine ⟨15209268383400374865558161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139512255600249910372107 15209268383400374865558161)
                ·
                  refine ⟨11406951287550281149168621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15209268383400374865558161 11406951287550281149168621)
                  ·
                    refine ⟨4277606732831355430938233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11406951287550281149168621 4277606732831355430938233)
                    ·
                      refine ⟨3208205049623516573203675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277606732831355430938233 3208205049623516573203675)
                      ·
                        rfl

theorem cell23_6247957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_6247957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247957 prefixEnd_6247957 := by exact prefixLift 6247957
  have htrace : WordTrace (prefixWord ++ tailWord_6247957) baseStart_6247957 baseEnd_6247957 := by
    simpa [prefixWord, tailWord_6247957, baseEnd_6247957] using wordTrace_append hprefix tailTrace_6247957
  have hstable : (prefixWord ++ tailWord_6247957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247957).length < 2 ^ (prefixWord ++ tailWord_6247957).sum := by decide
  have hdescent : baseEnd_6247957 < baseStart_6247957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247970 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_6247970 : Nat := 118140960795 + 6247970 * 2 ^ 59
def prefixEnd_6247970 : Nat := 4983230072969 + 3 ^ 40 * 6247970 * 2
def baseEnd_6247970 : Nat := 3208211724872025022341115

theorem tailTrace_6247970 : CollatzResearch.WordTrace tailWord_6247970 prefixEnd_6247970 3208211724872025022341115 := by
  unfold tailWord_6247970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56970546793669808291865341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151921458116452822111640909 56970546793669808291865341)
  ·
    refine ⟨21363955047626178109449503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56970546793669808291865341 21363955047626178109449503)
    ·
      refine ⟨32045932571439267164174255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21363955047626178109449503 32045932571439267164174255)
      ·
        refine ⟨48068898857158900746261383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32045932571439267164174255 48068898857158900746261383)
        ·
          refine ⟨72103348285738351119392075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48068898857158900746261383 72103348285738351119392075)
          ·
            refine ⟨108155022428607526679088113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72103348285738351119392075 108155022428607526679088113)
            ·
              refine ⟨81116266821455645009316085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108155022428607526679088113 81116266821455645009316085)
              ·
                refine ⟨7604650014511466719623383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81116266821455645009316085 7604650014511466719623383)
                ·
                  refine ⟨11406975021767200079435075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604650014511466719623383 11406975021767200079435075)
                  ·
                    refine ⟨17110462532650800119152613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406975021767200079435075 17110462532650800119152613)
                    ·
                      refine ⟨3208211724872025022341115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17110462532650800119152613 3208211724872025022341115)
                      ·
                        rfl

theorem cell23_6247970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_6247970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247970 prefixEnd_6247970 := by exact prefixLift 6247970
  have htrace : WordTrace (prefixWord ++ tailWord_6247970) baseStart_6247970 baseEnd_6247970 := by
    simpa [prefixWord, tailWord_6247970, baseEnd_6247970] using wordTrace_append hprefix tailTrace_6247970
  have hstable : (prefixWord ++ tailWord_6247970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247970).length < 2 ^ (prefixWord ++ tailWord_6247970).sum := by decide
  have hdescent : baseEnd_6247970 < baseStart_6247970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6247993 : List Nat := [1, 2, 1, 5, 1, 2, 3, 8]
def baseStart_6247993 : Nat := 118140960795 + 6247993 * 2 ^ 59
def prefixEnd_6247993 : Nat := 4983230072969 + 3 ^ 40 * 6247993 * 2
def baseEnd_6247993 : Nat := 118823093886188090087167

theorem tailTrace_6247993 : CollatzResearch.WordTrace tailWord_6247993 prefixEnd_6247993 118823093886188090087167 := by
  unfold tailWord_6247993
  simp only [CollatzResearch.WordTrace]
  refine ⟨227883026053595908095548633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151922017369063938730365755 227883026053595908095548633)
  ·
    refine ⟨170912269540196931071661475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227883026053595908095548633 170912269540196931071661475)
    ·
      refine ⟨256368404310295396607492213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170912269540196931071661475 256368404310295396607492213)
      ·
        refine ⟨24034537904090193431952395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256368404310295396607492213 24034537904090193431952395)
        ·
          refine ⟨36051806856135290147928593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24034537904090193431952395 36051806856135290147928593)
          ·
            refine ⟨27038855142101467610946445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36051806856135290147928593 27038855142101467610946445)
            ·
              refine ⟨10139570678288050354104917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27038855142101467610946445 10139570678288050354104917)
              ·
                refine ⟨118823093886188090087167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10139570678288050354104917 118823093886188090087167)
                ·
                  rfl

theorem cell23_6247993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 8].length) (baseStart_6247993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6247993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6247993 prefixEnd_6247993 := by exact prefixLift 6247993
  have htrace : WordTrace (prefixWord ++ tailWord_6247993) baseStart_6247993 baseEnd_6247993 := by
    simpa [prefixWord, tailWord_6247993, baseEnd_6247993] using wordTrace_append hprefix tailTrace_6247993
  have hstable : (prefixWord ++ tailWord_6247993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6247993).length < 2 ^ (prefixWord ++ tailWord_6247993).sum := by decide
  have hdescent : baseEnd_6247993 < baseStart_6247993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6247993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248020 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_6248020 : Nat := 118140960795 + 6248020 * 2 ^ 59
def prefixEnd_6248020 : Nat := 4983230072969 + 3 ^ 40 * 6248020 * 2
def baseEnd_6248020 : Nat := 3208237398904749826715885

theorem tailTrace_6248020 : CollatzResearch.WordTrace tailWord_6248020 prefixEnd_6248020 3208237398904749826715885 := by
  unfold tailWord_6248020
  simp only [CollatzResearch.WordTrace]
  refine ⟨113942005412249045853390757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151922673882998727804521009 113942005412249045853390757)
  ·
    refine ⟨21364126014796696097510767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113942005412249045853390757 21364126014796696097510767)
    ·
      refine ⟨32046189022195044146266151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21364126014796696097510767 32046189022195044146266151)
      ·
        refine ⟨48069283533292566219399227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32046189022195044146266151 48069283533292566219399227)
        ·
          refine ⟨72103925299938849329098841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48069283533292566219399227 72103925299938849329098841)
          ·
            refine ⟨54077943974954136996824131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72103925299938849329098841 54077943974954136996824131)
            ·
              refine ⟨81116915962431205495236197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54077943974954136996824131 81116915962431205495236197)
              ·
                refine ⟨15209421742955851030356787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81116915962431205495236197 15209421742955851030356787)
                ·
                  refine ⟨22814132614433776545535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15209421742955851030356787 22814132614433776545535181)
                  ·
                    refine ⟨8555299730412666204575693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22814132614433776545535181 8555299730412666204575693)
                    ·
                      refine ⟨3208237398904749826715885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555299730412666204575693 3208237398904749826715885)
                      ·
                        rfl

theorem cell23_6248020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_6248020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248020 prefixEnd_6248020 := by exact prefixLift 6248020
  have htrace : WordTrace (prefixWord ++ tailWord_6248020) baseStart_6248020 baseEnd_6248020 := by
    simpa [prefixWord, tailWord_6248020, baseEnd_6248020] using wordTrace_append hprefix tailTrace_6248020
  have hstable : (prefixWord ++ tailWord_6248020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248020).length < 2 ^ (prefixWord ++ tailWord_6248020).sum := by decide
  have hdescent : baseEnd_6248020 < baseStart_6248020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248037 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_6248037 : Nat := 118140960795 + 6248037 * 2 ^ 59
def prefixEnd_6248037 : Nat := 4983230072969 + 3 ^ 40 * 6248037 * 2
def baseEnd_6248037 : Nat := 3208246128075876260203307

theorem tailTrace_6248037 : CollatzResearch.WordTrace tailWord_6248037 prefixEnd_6248037 3208246128075876260203307 := by
  unfold tailWord_6248037
  simp only [CollatzResearch.WordTrace]
  refine ⟨227884630865436503610150365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151923087243624335740100243 227884630865436503610150365)
  ·
    refine ⟨85456736574538688853806387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227884630865436503610150365 85456736574538688853806387)
    ·
      refine ⟨128185104861808033280709581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85456736574538688853806387 128185104861808033280709581)
      ·
        refine ⟨48069414323178012480266093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128185104861808033280709581 48069414323178012480266093)
        ·
          refine ⟨18026030371191754680099785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48069414323178012480266093 18026030371191754680099785)
          ·
            refine ⟨13519522778393816010074839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18026030371191754680099785 13519522778393816010074839)
            ·
              refine ⟨20279284167590724015112259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519522778393816010074839 20279284167590724015112259)
              ·
                refine ⟨30418926251386086022668389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20279284167590724015112259 30418926251386086022668389)
                ·
                  refine ⟨5703548672134891129250323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30418926251386086022668389 5703548672134891129250323)
                  ·
                    refine ⟨8555323008202336693875485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703548672134891129250323 8555323008202336693875485)
                    ·
                      refine ⟨3208246128075876260203307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555323008202336693875485 3208246128075876260203307)
                      ·
                        rfl

theorem cell23_6248037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_6248037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248037 prefixEnd_6248037 := by exact prefixLift 6248037
  have htrace : WordTrace (prefixWord ++ tailWord_6248037) baseStart_6248037 baseEnd_6248037 := by
    simpa [prefixWord, tailWord_6248037, baseEnd_6248037] using wordTrace_append hprefix tailTrace_6248037
  have hstable : (prefixWord ++ tailWord_6248037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248037).length < 2 ^ (prefixWord ++ tailWord_6248037).sum := by decide
  have hdescent : baseEnd_6248037 < baseStart_6248037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248054 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6248054 : Nat := 118140960795 + 6248054 * 2 ^ 59
def prefixEnd_6248054 : Nat := 4983230072969 + 3 ^ 40 * 6248054 * 2
def baseEnd_6248054 : Nat := 3208254857247002693690729

theorem tailTrace_6248054 : CollatzResearch.WordTrace tailWord_6248054 prefixEnd_6248054 3208254857247002693690729 := by
  unfold tailWord_6248054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14242828181648432219594951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151923500604249943675679477 14242828181648432219594951)
  ·
    refine ⟨21364242272472648329392427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14242828181648432219594951 21364242272472648329392427)
    ·
      refine ⟨32046363408708972494088641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21364242272472648329392427 32046363408708972494088641)
      ·
        refine ⟨24034772556531729370566481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32046363408708972494088641 24034772556531729370566481)
        ·
          refine ⟨18026079417398797027924861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24034772556531729370566481 18026079417398797027924861)
          ·
            refine ⟨6759779781524548885471823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18026079417398797027924861 6759779781524548885471823)
            ·
              refine ⟨10139669672286823328207735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759779781524548885471823 10139669672286823328207735)
              ·
                refine ⟨15209504508430234992311603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139669672286823328207735 15209504508430234992311603)
                ·
                  refine ⟨22814256762645352488467405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15209504508430234992311603 22814256762645352488467405)
                  ·
                    refine ⟨8555346285992007183175277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22814256762645352488467405 8555346285992007183175277)
                    ·
                      refine ⟨3208254857247002693690729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555346285992007183175277 3208254857247002693690729)
                      ·
                        rfl

theorem cell23_6248054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6248054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248054 prefixEnd_6248054 := by exact prefixLift 6248054
  have htrace : WordTrace (prefixWord ++ tailWord_6248054) baseStart_6248054 baseEnd_6248054 := by
    simpa [prefixWord, tailWord_6248054, baseEnd_6248054] using wordTrace_append hprefix tailTrace_6248054
  have hstable : (prefixWord ++ tailWord_6248054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248054).length < 2 ^ (prefixWord ++ tailWord_6248054).sum := by decide
  have hdescent : baseEnd_6248054 < baseStart_6248054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248063 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_6248063 : Nat := 118140960795 + 6248063 * 2 ^ 59
def prefixEnd_6248063 : Nat := 4983230072969 + 3 ^ 40 * 6248063 * 2
def baseEnd_6248063 : Nat := 3208259478572893158478187

theorem tailTrace_6248063 : CollatzResearch.WordTrace tailWord_6248063 prefixEnd_6248063 3208259478572893158478187 := by
  unfold tailWord_6248063
  simp only [CollatzResearch.WordTrace]
  refine ⟨227885579163342310050596843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151923719442228206700397895 227885579163342310050596843)
  ·
    refine ⟨341828368745013465075895265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227885579163342310050596843 341828368745013465075895265)
    ·
      refine ⟨256371276558760098806921449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341828368745013465075895265 256371276558760098806921449)
      ·
        refine ⟨192278457419070074105191087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256371276558760098806921449 192278457419070074105191087)
        ·
          refine ⟨288417686128605111157786631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192278457419070074105191087 288417686128605111157786631)
          ·
            refine ⟨432626529192907666736679947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288417686128605111157786631 432626529192907666736679947)
            ·
              refine ⟨648939793789361500105019921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432626529192907666736679947 648939793789361500105019921)
              ·
                refine ⟨486704845342021125078764941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648939793789361500105019921 486704845342021125078764941)
                ·
                  refine ⟨182514317003257921904536853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486704845342021125078764941 182514317003257921904536853)
                  ·
                    refine ⟨8555358609527715089275165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182514317003257921904536853 8555358609527715089275165)
                    ·
                      refine ⟨3208259478572893158478187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555358609527715089275165 3208259478572893158478187)
                      ·
                        rfl

theorem cell23_6248063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_6248063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248063 prefixEnd_6248063 := by exact prefixLift 6248063
  have htrace : WordTrace (prefixWord ++ tailWord_6248063) baseStart_6248063 baseEnd_6248063 := by
    simpa [prefixWord, tailWord_6248063, baseEnd_6248063] using wordTrace_append hprefix tailTrace_6248063
  have hstable : (prefixWord ++ tailWord_6248063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248063).length < 2 ^ (prefixWord ++ tailWord_6248063).sum := by decide
  have hdescent : baseEnd_6248063 < baseStart_6248063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248073 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_6248073 : Nat := 118140960795 + 6248073 * 2 ^ 59
def prefixEnd_6248073 : Nat := 4983230072969 + 3 ^ 40 * 6248073 * 2
def baseEnd_6248073 : Nat := 3208264613379438119353141

theorem tailTrace_6248073 : CollatzResearch.WordTrace tailWord_6248073 prefixEnd_6248073 3208264613379438119353141 := by
  unfold tailWord_6248073
  simp only [CollatzResearch.WordTrace]
  refine ⟨227885943893306081758460873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151923962595537387838973915 227885943893306081758460873)
  ·
    refine ⟨170914457919979561318845655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227885943893306081758460873 170914457919979561318845655)
    ·
      refine ⟨256371686879969341978268483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170914457919979561318845655 256371686879969341978268483)
      ·
        refine ⟨384557530319954012967402725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256371686879969341978268483 384557530319954012967402725)
        ·
          refine ⟨72104536934991377431388011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384557530319954012967402725 72104536934991377431388011)
          ·
            refine ⟨108156805402487066147082017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72104536934991377431388011 108156805402487066147082017)
            ·
              refine ⟨81117604051865299610311513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108156805402487066147082017 81117604051865299610311513)
              ·
                refine ⟨60838203038898974707733635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81117604051865299610311513 60838203038898974707733635)
                ·
                  refine ⟨91257304558348462061600453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60838203038898974707733635 91257304558348462061600453)
                  ·
                    refine ⟨17110744604690336636550085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91257304558348462061600453 17110744604690336636550085)
                    ·
                      refine ⟨3208264613379438119353141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17110744604690336636550085 3208264613379438119353141)
                      ·
                        rfl

theorem cell23_6248073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_6248073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248073 prefixEnd_6248073 := by exact prefixLift 6248073
  have htrace : WordTrace (prefixWord ++ tailWord_6248073) baseStart_6248073 baseEnd_6248073 := by
    simpa [prefixWord, tailWord_6248073, baseEnd_6248073] using wordTrace_append hprefix tailTrace_6248073
  have hstable : (prefixWord ++ tailWord_6248073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248073).length < 2 ^ (prefixWord ++ tailWord_6248073).sum := by decide
  have hdescent : baseEnd_6248073 < baseStart_6248073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248093 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6248093 : Nat := 118140960795 + 6248093 * 2 ^ 59
def prefixEnd_6248093 : Nat := 4983230072969 + 3 ^ 40 * 6248093 * 2
def baseEnd_6248093 : Nat := 3208274882992528041103049

theorem tailTrace_6248093 : CollatzResearch.WordTrace tailWord_6248093 prefixEnd_6248093 3208274882992528041103049 := by
  unfold tailWord_6248093
  simp only [CollatzResearch.WordTrace]
  refine ⟨227886673353233625174188933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151924448902155750116125955 227886673353233625174188933)
  ·
    refine ⟨42728751253731304720160425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227886673353233625174188933 42728751253731304720160425)
    ·
      refine ⟨32046563440298478540120319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42728751253731304720160425 32046563440298478540120319)
      ·
        refine ⟨48069845160447717810180479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32046563440298478540120319 48069845160447717810180479)
        ·
          refine ⟨72104767740671576715270719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48069845160447717810180479 72104767740671576715270719)
          ·
            refine ⟨108157151611007365072906079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72104767740671576715270719 108157151611007365072906079)
            ·
              refine ⟨162235727416511047609359119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108157151611007365072906079 162235727416511047609359119)
              ·
                refine ⟨243353591124766571414038679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162235727416511047609359119 243353591124766571414038679)
                ·
                  refine ⟨365030386687149857121058019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243353591124766571414038679 365030386687149857121058019)
                  ·
                    refine ⟨547545580030724785681587029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365030386687149857121058019 547545580030724785681587029)
                    ·
                      refine ⟨3208274882992528041103049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 547545580030724785681587029 3208274882992528041103049)
                      ·
                        rfl

theorem cell23_6248093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6248093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248093 prefixEnd_6248093 := by exact prefixLift 6248093
  have htrace : WordTrace (prefixWord ++ tailWord_6248093) baseStart_6248093 baseEnd_6248093 := by
    simpa [prefixWord, tailWord_6248093, baseEnd_6248093] using wordTrace_append hprefix tailTrace_6248093
  have hstable : (prefixWord ++ tailWord_6248093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248093).length < 2 ^ (prefixWord ++ tailWord_6248093).sum := by decide
  have hdescent : baseEnd_6248093 < baseStart_6248093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248100 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 7]
def baseStart_6248100 : Nat := 118140960795 + 6248100 * 2 ^ 59
def prefixEnd_6248100 : Nat := 4983230072969 + 3 ^ 40 * 6248100 * 2
def baseEnd_6248100 : Nat := 356475386373012168190613

theorem tailTrace_6248100 : CollatzResearch.WordTrace tailWord_6248100 prefixEnd_6248100 356475386373012168190613 := by
  unfold tailWord_6248100
  simp only [CollatzResearch.WordTrace]
  refine ⟨113943464332104132684846877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151924619109472176913129169 113943464332104132684846877)
  ·
    refine ⟨42728799124539049756817579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113943464332104132684846877 42728799124539049756817579)
    ·
      refine ⟨64093198686808574635226369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42728799124539049756817579 64093198686808574635226369)
      ·
        refine ⟨48069899015106430976419777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64093198686808574635226369 48069899015106430976419777)
        ·
          refine ⟨36052424261329823232314833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48069899015106430976419777 36052424261329823232314833)
          ·
            refine ⟨27039318195997367424236125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36052424261329823232314833 27039318195997367424236125)
            ·
              refine ⟨10139744323499012784088547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27039318195997367424236125 10139744323499012784088547)
              ·
                refine ⟨15209616485248519176132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139744323499012784088547 15209616485248519176132821)
                ·
                  refine ⟨356475386373012168190613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15209616485248519176132821 356475386373012168190613)
                  ·
                    rfl

theorem cell23_6248100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_6248100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248100 prefixEnd_6248100 := by exact prefixLift 6248100
  have htrace : WordTrace (prefixWord ++ tailWord_6248100) baseStart_6248100 baseEnd_6248100 := by
    simpa [prefixWord, tailWord_6248100, baseEnd_6248100] using wordTrace_append hprefix tailTrace_6248100
  have hstable : (prefixWord ++ tailWord_6248100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248100).length < 2 ^ (prefixWord ++ tailWord_6248100).sum := by decide
  have hdescent : baseEnd_6248100 < baseStart_6248100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248177 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_6248177 : Nat := 118140960795 + 6248177 * 2 ^ 59
def prefixEnd_6248177 : Nat := 4983230072969 + 3 ^ 40 * 6248177 * 2
def baseEnd_6248177 : Nat := 1069439338455835237484221

theorem tailTrace_6248177 : CollatzResearch.WordTrace tailWord_6248177 prefixEnd_6248177 1069439338455835237484221 := by
  unfold tailWord_6248177
  simp only [CollatzResearch.WordTrace]
  refine ⟨227889737084929307520246785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151926491389952871680164523 227889737084929307520246785)
  ·
    refine ⟨170917302813696980640185089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227889737084929307520246785 170917302813696980640185089)
    ·
      refine ⟨128187977110272735480138817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170917302813696980640185089 128187977110272735480138817)
      ·
        refine ⟨96140982832704551610104113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128187977110272735480138817 96140982832704551610104113)
        ·
          refine ⟨72105737124528413707578085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96140982832704551610104113 72105737124528413707578085)
          ·
            refine ⟨13519825710849077570170891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72105737124528413707578085 13519825710849077570170891)
            ·
              refine ⟨20279738566273616355256337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519825710849077570170891 20279738566273616355256337)
              ·
                refine ⟨15209803924705212266442253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20279738566273616355256337 15209803924705212266442253)
                ·
                  refine ⟨5703676471764454599915845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15209803924705212266442253 5703676471764454599915845)
                  ·
                    refine ⟨1069439338455835237484221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703676471764454599915845 1069439338455835237484221)
                    ·
                      rfl

theorem cell23_6248177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_6248177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248177 prefixEnd_6248177 := by exact prefixLift 6248177
  have htrace : WordTrace (prefixWord ++ tailWord_6248177) baseStart_6248177 baseEnd_6248177 := by
    simpa [prefixWord, tailWord_6248177, baseEnd_6248177] using wordTrace_append hprefix tailTrace_6248177
  have hstable : (prefixWord ++ tailWord_6248177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248177).length < 2 ^ (prefixWord ++ tailWord_6248177).sum := by decide
  have hdescent : baseEnd_6248177 < baseStart_6248177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248227 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 5, 2]
def baseStart_6248227 : Nat := 118140960795 + 6248227 * 2 ^ 59
def prefixEnd_6248227 : Nat := 4983230072969 + 3 ^ 40 * 6248227 * 2
def baseEnd_6248227 : Nat := 3208343689400230516827433

theorem tailTrace_6248227 : CollatzResearch.WordTrace tailWord_6248227 prefixEnd_6248227 3208343689400230516827433 := by
  unfold tailWord_6248227
  simp only [CollatzResearch.WordTrace]
  refine ⟨227891560734748166059566935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151927707156498777373044623 227891560734748166059566935)
  ·
    refine ⟨341837341102122249089350403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227891560734748166059566935 341837341102122249089350403)
    ·
      refine ⟨512756011653183373634025605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341837341102122249089350403 512756011653183373634025605)
      ·
        refine ⟨96141752184971882556379801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 512756011653183373634025605 96141752184971882556379801)
        ·
          refine ⟨72106314138728911917284851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96141752184971882556379801 72106314138728911917284851)
          ·
            refine ⟨108159471208093367875927277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72106314138728911917284851 108159471208093367875927277)
            ·
              refine ⟨40559801703035012953472729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108159471208093367875927277 40559801703035012953472729)
              ·
                refine ⟨30419851277276259715104547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40559801703035012953472729 30419851277276259715104547)
                ·
                  refine ⟨45629776915914389572656821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30419851277276259715104547 45629776915914389572656821)
                  ·
                    refine ⟨4277791585866974022436577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45629776915914389572656821 4277791585866974022436577)
                    ·
                      refine ⟨3208343689400230516827433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277791585866974022436577 3208343689400230516827433)
                      ·
                        rfl

theorem cell23_6248227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_6248227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248227 prefixEnd_6248227 := by exact prefixLift 6248227
  have htrace : WordTrace (prefixWord ++ tailWord_6248227) baseStart_6248227 baseEnd_6248227 := by
    simpa [prefixWord, tailWord_6248227, baseEnd_6248227] using wordTrace_append hprefix tailTrace_6248227
  have hstable : (prefixWord ++ tailWord_6248227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248227).length < 2 ^ (prefixWord ++ tailWord_6248227).sum := by decide
  have hdescent : baseEnd_6248227 < baseStart_6248227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248254 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_6248254 : Nat := 118140960795 + 6248254 * 2 ^ 59
def prefixEnd_6248254 : Nat := 4983230072969 + 3 ^ 40 * 6248254 * 2
def baseEnd_6248254 : Nat := 1069452517792633970396603

theorem tailTrace_6248254 : CollatzResearch.WordTrace tailWord_6248254 prefixEnd_6248254 1069452517792633970396603 := by
  unfold tailWord_6248254
  simp only [CollatzResearch.WordTrace]
  refine ⟨28486568188206293708849977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151928363670433566447199877 28486568188206293708849977)
  ·
    refine ⟨21364926141154720281637483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28486568188206293708849977 21364926141154720281637483)
    ·
      refine ⟨32047389211732080422456225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21364926141154720281637483 32047389211732080422456225)
      ·
        refine ⟨24035541908799060316842169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32047389211732080422456225 24035541908799060316842169)
        ·
          refine ⟨18026656431599295237631627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24035541908799060316842169 18026656431599295237631627)
          ·
            refine ⟨27039984647398942856447441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18026656431599295237631627 27039984647398942856447441)
            ·
              refine ⟨20279988485549207142335581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27039984647398942856447441 20279988485549207142335581)
              ·
                refine ⟨7604995682080952678375843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20279988485549207142335581 7604995682080952678375843)
                ·
                  refine ⟨11407493523121429017563765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604995682080952678375843 11407493523121429017563765)
                  ·
                    refine ⟨1069452517792633970396603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11407493523121429017563765 1069452517792633970396603)
                    ·
                      rfl

theorem cell23_6248254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_6248254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248254 prefixEnd_6248254 := by exact prefixLift 6248254
  have htrace : WordTrace (prefixWord ++ tailWord_6248254) baseStart_6248254 baseEnd_6248254 := by
    simpa [prefixWord, tailWord_6248254, baseEnd_6248254] using wordTrace_append hprefix tailTrace_6248254
  have hstable : (prefixWord ++ tailWord_6248254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248254).length < 2 ^ (prefixWord ++ tailWord_6248254).sum := by decide
  have hdescent : baseEnd_6248254 < baseStart_6248254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248268 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6248268 : Nat := 118140960795 + 6248268 * 2 ^ 59
def prefixEnd_6248268 : Nat := 4983230072969 + 3 ^ 40 * 6248268 * 2
def baseEnd_6248268 : Nat := 3208364742107064856414745

theorem tailTrace_6248268 : CollatzResearch.WordTrace tailWord_6248268 prefixEnd_6248268 3208364742107064856414745 := by
  unfold tailWord_6248268
  simp only [CollatzResearch.WordTrace]
  refine ⟨113946528063799815030904729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151928704085066420041206305 113946528063799815030904729)
  ·
    refine ⟨85459896047849861273178547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113946528063799815030904729 85459896047849861273178547)
    ·
      refine ⟨128189844071774791909767821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85459896047849861273178547 128189844071774791909767821)
      ·
        refine ⟨48071191526915546966162933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128189844071774791909767821 48071191526915546966162933)
        ·
          refine ⟨4506674205648332528077775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48071191526915546966162933 4506674205648332528077775)
          ·
            refine ⟨6760011308472498792116663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506674205648332528077775 6760011308472498792116663)
            ·
              refine ⟨10140016962708748188174995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760011308472498792116663 10140016962708748188174995)
              ·
                refine ⟨15210025444063122282262493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10140016962708748188174995 15210025444063122282262493)
                ·
                  refine ⟨5703759541523670855848435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15210025444063122282262493 5703759541523670855848435)
                  ·
                    refine ⟨8555639312285506283772653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703759541523670855848435 8555639312285506283772653)
                    ·
                      refine ⟨3208364742107064856414745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555639312285506283772653 3208364742107064856414745)
                      ·
                        rfl

theorem cell23_6248268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6248268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248268 prefixEnd_6248268 := by exact prefixLift 6248268
  have htrace : WordTrace (prefixWord ++ tailWord_6248268) baseStart_6248268 baseEnd_6248268 := by
    simpa [prefixWord, tailWord_6248268, baseEnd_6248268] using wordTrace_append hprefix tailTrace_6248268
  have hstable : (prefixWord ++ tailWord_6248268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248268).length < 2 ^ (prefixWord ++ tailWord_6248268).sum := by decide
  have hdescent : baseEnd_6248268 < baseStart_6248268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248277 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6248277 : Nat := 118140960795 + 6248277 * 2 ^ 59
def prefixEnd_6248277 : Nat := 4983230072969 + 3 ^ 40 * 6248277 * 2
def baseEnd_6248277 : Nat := 3208369363432955321202203

theorem tailTrace_6248277 : CollatzResearch.WordTrace tailWord_6248277 prefixEnd_6248277 3208369363432955321202203 := by
  unfold tailWord_6248277
  simp only [CollatzResearch.WordTrace]
  refine ⟨227893384384567024598887085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151928922923044683065924723 227893384384567024598887085)
  ·
    refine ⟨85460019144212634224582657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227893384384567024598887085 85460019144212634224582657)
    ·
      refine ⟨64095014358159475668436993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85460019144212634224582657 64095014358159475668436993)
      ·
        refine ⟨48071260768619606751327745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64095014358159475668436993 48071260768619606751327745)
        ·
          refine ⟨36053445576464705063495809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48071260768619606751327745 36053445576464705063495809)
          ·
            refine ⟨27040084182348528797621857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36053445576464705063495809 27040084182348528797621857)
            ·
              refine ⟨20280063136761396598216393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27040084182348528797621857 20280063136761396598216393)
              ·
                refine ⟨15210047352571047448662295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20280063136761396598216393 15210047352571047448662295)
                ·
                  refine ⟨22815071028856571172993443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15210047352571047448662295 22815071028856571172993443)
                  ·
                    refine ⟨34222606543284856759490165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22815071028856571172993443 34222606543284856759490165)
                    ·
                      refine ⟨3208369363432955321202203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34222606543284856759490165 3208369363432955321202203)
                      ·
                        rfl

theorem cell23_6248277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6248277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248277 prefixEnd_6248277 := by exact prefixLift 6248277
  have htrace : WordTrace (prefixWord ++ tailWord_6248277) baseStart_6248277 baseEnd_6248277 := by
    simpa [prefixWord, tailWord_6248277, baseEnd_6248277] using wordTrace_append hprefix tailTrace_6248277
  have hstable : (prefixWord ++ tailWord_6248277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248277).length < 2 ^ (prefixWord ++ tailWord_6248277).sum := by decide
  have hdescent : baseEnd_6248277 < baseStart_6248277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248291 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 4]
def baseStart_6248291 : Nat := 118140960795 + 6248291 * 2 ^ 59
def prefixEnd_6248291 : Nat := 4983230072969 + 3 ^ 40 * 6248291 * 2
def baseEnd_6248291 : Nat := 3208376552162118266427139

theorem tailTrace_6248291 : CollatzResearch.WordTrace tailWord_6248291 prefixEnd_6248291 3208376552162118266427139 := by
  unfold tailWord_6248291
  simp only [CollatzResearch.WordTrace]
  refine ⟨227893895006516304989896727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151929263337677536659931151 227893895006516304989896727)
  ·
    refine ⟨341840842509774457484845091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227893895006516304989896727 341840842509774457484845091)
    ·
      refine ⟨512761263764661686227267637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341840842509774457484845091 512761263764661686227267637)
      ·
        refine ⟨48071368477937033083806341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 512761263764661686227267637 48071368477937033083806341)
        ·
          refine ⟨9013381589613193703213689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48071368477937033083806341 9013381589613193703213689)
          ·
            refine ⟨6760036192209895277410267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013381589613193703213689 6760036192209895277410267)
            ·
              refine ⟨10140054288314842916115401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760036192209895277410267 10140054288314842916115401)
              ·
                refine ⟨7605040716236132187086551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10140054288314842916115401 7605040716236132187086551)
                ·
                  refine ⟨11407561074354198280629827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7605040716236132187086551 11407561074354198280629827)
                  ·
                    refine ⟨17111341611531297420944741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11407561074354198280629827 17111341611531297420944741)
                    ·
                      refine ⟨3208376552162118266427139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17111341611531297420944741 3208376552162118266427139)
                      ·
                        rfl

theorem cell23_6248291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_6248291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248291 prefixEnd_6248291 := by exact prefixLift 6248291
  have htrace : WordTrace (prefixWord ++ tailWord_6248291) baseStart_6248291 baseEnd_6248291 := by
    simpa [prefixWord, tailWord_6248291, baseEnd_6248291] using wordTrace_append hprefix tailTrace_6248291
  have hstable : (prefixWord ++ tailWord_6248291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248291).length < 2 ^ (prefixWord ++ tailWord_6248291).sum := by decide
  have hdescent : baseEnd_6248291 < baseStart_6248291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248318 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6248318 : Nat := 118140960795 + 6248318 * 2 ^ 59
def prefixEnd_6248318 : Nat := 4983230072969 + 3 ^ 40 * 6248318 * 2
def baseEnd_6248318 : Nat := 1069463472046596553596505

theorem tailTrace_6248318 : CollatzResearch.WordTrace tailWord_6248318 prefixEnd_6248318 1069463472046596553596505 := by
  unfold tailWord_6248318
  simp only [CollatzResearch.WordTrace]
  refine ⟨28486859972177311075141201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151929919851612325734086405 28486859972177311075141201)
  ·
    refine ⟨21365144979132983306355901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28486859972177311075141201 21365144979132983306355901)
    ·
      refine ⟨8011929367174868739883463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21365144979132983306355901 8011929367174868739883463)
      ·
        refine ⟨12017894050762303109825195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8011929367174868739883463 12017894050762303109825195)
        ·
          refine ⟨18026841076143454664737793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12017894050762303109825195 18026841076143454664737793)
          ·
            refine ⟨13520130807107590998553345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18026841076143454664737793 13520130807107590998553345)
            ·
              refine ⟨10140098105330693248915009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13520130807107590998553345 10140098105330693248915009)
              ·
                refine ⟨7605073578998019936686257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10140098105330693248915009 7605073578998019936686257)
                ·
                  refine ⟨5703805184248514952514693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605073578998019936686257 5703805184248514952514693)
                  ·
                    refine ⟨1069463472046596553596505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703805184248514952514693 1069463472046596553596505)
                    ·
                      rfl

theorem cell23_6248318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6248318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248318 prefixEnd_6248318 := by exact prefixLift 6248318
  have htrace : WordTrace (prefixWord ++ tailWord_6248318) baseStart_6248318 baseEnd_6248318 := by
    simpa [prefixWord, tailWord_6248318, baseEnd_6248318] using wordTrace_append hprefix tailTrace_6248318
  have hstable : (prefixWord ++ tailWord_6248318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248318).length < 2 ^ (prefixWord ++ tailWord_6248318).sum := by decide
  have hdescent : baseEnd_6248318 < baseStart_6248318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248324 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_6248324 : Nat := 118140960795 + 6248324 * 2 ^ 59
def prefixEnd_6248324 : Nat := 4983230072969 + 3 ^ 40 * 6248324 * 2
def baseEnd_6248324 : Nat := 3208393497023716637314487

theorem tailTrace_6248324 : CollatzResearch.WordTrace tailWord_6248324 prefixEnd_6248324 3208393497023716637314487 := by
  unfold tailWord_6248324
  simp only [CollatzResearch.WordTrace]
  refine ⟨113947549307698375812924013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151930065743597834417232017 113947549307698375812924013)
  ·
    refine ⟨42730330990386890929846505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113947549307698375812924013 42730330990386890929846505)
    ·
      refine ⟨32047748242790168197384879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42730330990386890929846505 32047748242790168197384879)
      ·
        refine ⟨48071622364185252296077319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32047748242790168197384879 48071622364185252296077319)
        ·
          refine ⟨72107433546277878444115979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48071622364185252296077319 72107433546277878444115979)
          ·
            refine ⟨108161150319416817666173969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72107433546277878444115979 108161150319416817666173969)
            ·
              refine ⟨81120862739562613249630477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108161150319416817666173969 81120862739562613249630477)
              ·
                refine ⟨30420323527335979968611429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81120862739562613249630477 30420323527335979968611429)
                ·
                  refine ⟨5703810661375496244114643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30420323527335979968611429 5703810661375496244114643)
                  ·
                    refine ⟨8555715992063244366171965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703810661375496244114643 8555715992063244366171965)
                    ·
                      refine ⟨3208393497023716637314487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555715992063244366171965 3208393497023716637314487)
                      ·
                        rfl

theorem cell23_6248324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_6248324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248324 prefixEnd_6248324 := by exact prefixLift 6248324
  have htrace : WordTrace (prefixWord ++ tailWord_6248324) baseStart_6248324 baseEnd_6248324 := by
    simpa [prefixWord, tailWord_6248324, baseEnd_6248324] using wordTrace_append hprefix tailTrace_6248324
  have hstable : (prefixWord ++ tailWord_6248324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248324).length < 2 ^ (prefixWord ++ tailWord_6248324).sum := by decide
  have hdescent : baseEnd_6248324 < baseStart_6248324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248342 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6248342 : Nat := 118140960795 + 6248342 * 2 ^ 59
def prefixEnd_6248342 : Nat := 4983230072969 + 3 ^ 40 * 6248342 * 2
def baseEnd_6248342 : Nat := 3208402739675497566889405

theorem tailTrace_6248342 : CollatzResearch.WordTrace tailWord_6248342 prefixEnd_6248342 3208402739675497566889405 := by
  unfold tailWord_6248342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14243484695583221293750205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151930503419554360466668853 14243484695583221293750205)
  ·
    refine ⟨5341306760843707985156327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14243484695583221293750205 5341306760843707985156327)
    ·
      refine ⟨8011960141265561977734491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5341306760843707985156327 8011960141265561977734491)
      ·
        refine ⟨12017940211898342966601737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8011960141265561977734491 12017940211898342966601737)
        ·
          refine ⟨9013455158923757224951303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12017940211898342966601737 9013455158923757224951303)
          ·
            refine ⟨13520182738385635837426955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013455158923757224951303 13520182738385635837426955)
            ·
              refine ⟨20280274107578453756140433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13520182738385635837426955 20280274107578453756140433)
              ·
                refine ⟨15210205580683840317105325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20280274107578453756140433 15210205580683840317105325)
                ·
                  refine ⟨5703827092756440118914497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15210205580683840317105325 5703827092756440118914497)
                  ·
                    refine ⟨4277870319567330089185873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5703827092756440118914497 4277870319567330089185873)
                    ·
                      refine ⟨3208402739675497566889405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277870319567330089185873 3208402739675497566889405)
                      ·
                        rfl

theorem cell23_6248342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6248342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248342 prefixEnd_6248342 := by exact prefixLift 6248342
  have htrace : WordTrace (prefixWord ++ tailWord_6248342) baseStart_6248342 baseEnd_6248342 := by
    simpa [prefixWord, tailWord_6248342, baseEnd_6248342] using wordTrace_append hprefix tailTrace_6248342
  have hstable : (prefixWord ++ tailWord_6248342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248342).length < 2 ^ (prefixWord ++ tailWord_6248342).sum := by decide
  have hdescent : baseEnd_6248342 < baseStart_6248342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248377 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6248377 : Nat := 118140960795 + 6248377 * 2 ^ 59
def prefixEnd_6248377 : Nat := 4983230072969 + 3 ^ 40 * 6248377 * 2
def baseEnd_6248377 : Nat := 3208420711498404929951743

theorem tailTrace_6248377 : CollatzResearch.WordTrace tailWord_6248377 prefixEnd_6248377 3208420711498404929951743 := by
  unfold tailWord_6248377
  simp only [CollatzResearch.WordTrace]
  refine ⟨227897031684204741677527385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151931354456136494451684923 227897031684204741677527385)
  ·
    refine ⟨170922773763153556258145539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227897031684204741677527385 170922773763153556258145539)
    ·
      refine ⟨256384160644730334387218309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170922773763153556258145539 256384160644730334387218309)
      ·
        refine ⟨48072030120886937697603433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256384160644730334387218309 48072030120886937697603433)
        ·
          refine ⟨36054022590665203273202575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48072030120886937697603433 36054022590665203273202575)
          ·
            refine ⟨54081033885997804909803863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36054022590665203273202575 54081033885997804909803863)
            ·
              refine ⟨81121550828996707364705795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54081033885997804909803863 81121550828996707364705795)
              ·
                refine ⟨121682326243495061047058693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81121550828996707364705795 121682326243495061047058693)
                ·
                  refine ⟨22815436170655323946323505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121682326243495061047058693 22815436170655323946323505)
                  ·
                    refine ⟨17111577127991492959742629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22815436170655323946323505 17111577127991492959742629)
                    ·
                      refine ⟨3208420711498404929951743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17111577127991492959742629 3208420711498404929951743)
                      ·
                        rfl

theorem cell23_6248377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6248377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248377 prefixEnd_6248377 := by exact prefixLift 6248377
  have htrace : WordTrace (prefixWord ++ tailWord_6248377) baseStart_6248377 baseEnd_6248377 := by
    simpa [prefixWord, tailWord_6248377, baseEnd_6248377] using wordTrace_append hprefix tailTrace_6248377
  have hstable : (prefixWord ++ tailWord_6248377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248377).length < 2 ^ (prefixWord ++ tailWord_6248377).sum := by decide
  have hdescent : baseEnd_6248377 < baseStart_6248377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248417 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_6248417 : Nat := 118140960795 + 6248417 * 2 ^ 59
def prefixEnd_6248417 : Nat := 4983230072969 + 3 ^ 40 * 6248417 * 2
def baseEnd_6248417 : Nat := 1069480416908194924483853

theorem tailTrace_6248417 : CollatzResearch.WordTrace tailWord_6248417 prefixEnd_6248417 1069480416908194924483853 := by
  unfold tailWord_6248417
  simp only [CollatzResearch.WordTrace]
  refine ⟨227898490604059828508983505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151932327069373219005989003 227898490604059828508983505)
  ·
    refine ⟨170923867953044871381737629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227898490604059828508983505 170923867953044871381737629)
    ·
      refine ⟨64096450482391826768151611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170923867953044871381737629 64096450482391826768151611)
      ·
        refine ⟨96144675723587740152227417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64096450482391826768151611 96144675723587740152227417)
        ·
          refine ⟨72108506792690805114170563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96144675723587740152227417 72108506792690805114170563)
          ·
            refine ⟨108162760189036207671255845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72108506792690805114170563 108162760189036207671255845)
            ·
              refine ⟨20280517535444288938360471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108162760189036207671255845 20280517535444288938360471)
              ·
                refine ⟨30420776303166433407540707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20280517535444288938360471 30420776303166433407540707)
                ·
                  refine ⟨45631164454749650111311061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30420776303166433407540707 45631164454749650111311061)
                  ·
                    refine ⟨1069480416908194924483853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45631164454749650111311061 1069480416908194924483853)
                    ·
                      rfl

theorem cell23_6248417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_6248417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248417 prefixEnd_6248417 := by exact prefixLift 6248417
  have htrace : WordTrace (prefixWord ++ tailWord_6248417) baseStart_6248417 baseEnd_6248417 := by
    simpa [prefixWord, tailWord_6248417, baseEnd_6248417] using wordTrace_append hprefix tailTrace_6248417
  have hstable : (prefixWord ++ tailWord_6248417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248417).length < 2 ^ (prefixWord ++ tailWord_6248417).sum := by decide
  have hdescent : baseEnd_6248417 < baseStart_6248417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248424 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6248424 : Nat := 118140960795 + 6248424 * 2 ^ 59
def prefixEnd_6248424 : Nat := 4983230072969 + 3 ^ 40 * 6248424 * 2
def baseEnd_6248424 : Nat := 3208444845089166246064027

theorem tailTrace_6248424 : CollatzResearch.WordTrace tailWord_6248424 prefixEnd_6248424 3208444845089166246064027 := by
  unfold tailWord_6248424
  simp only [CollatzResearch.WordTrace]
  refine ⟨113949372957517234352244163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151932497276689645802992217 113949372957517234352244163)
  ·
    refine ⟨170924059436275851528366245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113949372957517234352244163 170924059436275851528366245)
    ·
      refine ⟨32048261144301722161568671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170924059436275851528366245 32048261144301722161568671)
      ·
        refine ⟨48072391716452583242353007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32048261144301722161568671 48072391716452583242353007)
        ·
          refine ⟨72108587574678874863529511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48072391716452583242353007 72108587574678874863529511)
          ·
            refine ⟨108162881362018312295294267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72108587574678874863529511 108162881362018312295294267)
            ·
              refine ⟨162244322043027468442941401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108162881362018312295294267 162244322043027468442941401)
              ·
                refine ⟨121683241532270601332206051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162244322043027468442941401 121683241532270601332206051)
                ·
                  refine ⟨182524862298405901998309077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121683241532270601332206051 182524862298405901998309077)
                  ·
                    refine ⟨4277926460118888328085369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182524862298405901998309077 4277926460118888328085369)
                    ·
                      refine ⟨3208444845089166246064027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4277926460118888328085369 3208444845089166246064027)
                      ·
                        rfl

theorem cell23_6248424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6248424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248424 prefixEnd_6248424 := by exact prefixLift 6248424
  have htrace : WordTrace (prefixWord ++ tailWord_6248424) baseStart_6248424 baseEnd_6248424 := by
    simpa [prefixWord, tailWord_6248424, baseEnd_6248424] using wordTrace_append hprefix tailTrace_6248424
  have hstable : (prefixWord ++ tailWord_6248424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248424).length < 2 ^ (prefixWord ++ tailWord_6248424).sum := by decide
  have hdescent : baseEnd_6248424 < baseStart_6248424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248438 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_6248438 : Nat := 118140960795 + 6248438 * 2 ^ 59
def prefixEnd_6248438 : Nat := 4983230072969 + 3 ^ 40 * 6248438 * 2
def baseEnd_6248438 : Nat := 356494670424258799032107

theorem tailTrace_6248438 : CollatzResearch.WordTrace tailWord_6248438 prefixEnd_6248438 356494670424258799032107 := by
  unfold tailWord_6248438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14243703533561484318468623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151932837691322499396998645 14243703533561484318468623)
  ·
    refine ⟨21365555300342226477702935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14243703533561484318468623 21365555300342226477702935)
    ·
      refine ⟨32048332950513339716554403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21365555300342226477702935 32048332950513339716554403)
      ·
        refine ⟨48072499425770009574831605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32048332950513339716554403 48072499425770009574831605)
        ·
          refine ⟨4506796821165938397640463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48072499425770009574831605 4506796821165938397640463)
          ·
            refine ⟨6760195231748907596460695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506796821165938397640463 6760195231748907596460695)
            ·
              refine ⟨10140292847623361394691043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760195231748907596460695 10140292847623361394691043)
              ·
                refine ⟨15210439271435042092036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10140292847623361394691043 15210439271435042092036565)
                ·
                  refine ⟨356494670424258799032107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15210439271435042092036565 356494670424258799032107)
                  ·
                    rfl

theorem cell23_6248438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_6248438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248438 prefixEnd_6248438 := by exact prefixLift 6248438
  have htrace : WordTrace (prefixWord ++ tailWord_6248438) baseStart_6248438 baseEnd_6248438 := by
    simpa [prefixWord, tailWord_6248438, baseEnd_6248438] using wordTrace_append hprefix tailTrace_6248438
  have hstable : (prefixWord ++ tailWord_6248438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248438).length < 2 ^ (prefixWord ++ tailWord_6248438).sum := by decide
  have hdescent : baseEnd_6248438 < baseStart_6248438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248467 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_6248467 : Nat := 118140960795 + 6248467 * 2 ^ 59
def prefixEnd_6248467 : Nat := 4983230072969 + 3 ^ 40 * 6248467 * 2
def baseEnd_6248467 : Nat := 3208466924757309577826329

theorem tailTrace_6248467 : CollatzResearch.WordTrace tailWord_6248467 prefixEnd_6248467 3208466924757309577826329 := by
  unfold tailWord_6248467
  simp only [CollatzResearch.WordTrace]
  refine ⟨227900314253878687048303655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151933542835919124698869103 227900314253878687048303655)
  ·
    refine ⟨341850471380818030572455483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227900314253878687048303655 341850471380818030572455483)
    ·
      refine ⟨512775707071227045858683225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341850471380818030572455483 512775707071227045858683225)
      ·
        refine ⟨384581780303420284394012419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512775707071227045858683225 384581780303420284394012419)
        ·
          refine ⟨576872670455130426591018629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384581780303420284394012419 576872670455130426591018629)
          ·
            refine ⟨108163625710336954985815993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576872670455130426591018629 108163625710336954985815993)
            ·
              refine ⟨81122719282752716239361995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108163625710336954985815993 81122719282752716239361995)
              ·
                refine ⟨121684078924129074359042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81122719282752716239361995 121684078924129074359042993)
                ·
                  refine ⟨91263059193096805769282245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121684078924129074359042993 91263059193096805769282245)
                  ·
                    refine ⟨17111823598705651081740421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91263059193096805769282245 17111823598705651081740421)
                    ·
                      refine ⟨3208466924757309577826329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17111823598705651081740421 3208466924757309577826329)
                      ·
                        rfl

theorem cell23_6248467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_6248467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248467 prefixEnd_6248467 := by exact prefixLift 6248467
  have htrace : WordTrace (prefixWord ++ tailWord_6248467) baseStart_6248467 baseEnd_6248467 := by
    simpa [prefixWord, tailWord_6248467, baseEnd_6248467] using wordTrace_append hprefix tailTrace_6248467
  have hstable : (prefixWord ++ tailWord_6248467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248467).length < 2 ^ (prefixWord ++ tailWord_6248467).sum := by decide
  have hdescent : baseEnd_6248467 < baseStart_6248467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248498 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_6248498 : Nat := 118140960795 + 6248498 * 2 ^ 59
def prefixEnd_6248498 : Nat := 4983230072969 + 3 ^ 40 * 6248498 * 2
def baseEnd_6248498 : Nat := 1069494280885866318846229

theorem tailTrace_6248498 : CollatzResearch.WordTrace tailWord_6248498 prefixEnd_6248498 1069494280885866318846229 := by
  unfold tailWord_6248498
  simp only [CollatzResearch.WordTrace]
  refine ⟨56975361229191594835670537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151934296611177586228454765 56975361229191594835670537)
  ·
    refine ⟨42731520921893696126752903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56975361229191594835670537 42731520921893696126752903)
    ·
      refine ⟨64097281382840544190129355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42731520921893696126752903 64097281382840544190129355)
      ·
        refine ⟨96145922074260816285194033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64097281382840544190129355 96145922074260816285194033)
        ·
          refine ⟨72109441555695612213895525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96145922074260816285194033 72109441555695612213895525)
          ·
            refine ⟨13520520291692927290105411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72109441555695612213895525 13520520291692927290105411)
            ·
              refine ⟨20280780437539390935158117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13520520291692927290105411 20280780437539390935158117)
              ·
                refine ⟨3802646332038635800342147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20280780437539390935158117 3802646332038635800342147)
                ·
                  refine ⟨5703969498057953700513221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802646332038635800342147 5703969498057953700513221)
                  ·
                    refine ⟨1069494280885866318846229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703969498057953700513221 1069494280885866318846229)
                    ·
                      rfl

theorem cell23_6248498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_6248498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248498 prefixEnd_6248498 := by exact prefixLift 6248498
  have htrace : WordTrace (prefixWord ++ tailWord_6248498) baseStart_6248498 baseEnd_6248498 := by
    simpa [prefixWord, tailWord_6248498, baseEnd_6248498] using wordTrace_append hprefix tailTrace_6248498
  have hstable : (prefixWord ++ tailWord_6248498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248498).length < 2 ^ (prefixWord ++ tailWord_6248498).sum := by decide
  have hdescent : baseEnd_6248498 < baseStart_6248498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248517 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_6248517 : Nat := 118140960795 + 6248517 * 2 ^ 59
def prefixEnd_6248517 : Nat := 4983230072969 + 3 ^ 40 * 6248517 * 2
def baseEnd_6248517 : Nat := 3208492598790034382201099

theorem tailTrace_6248517 : CollatzResearch.WordTrace tailWord_6248517 prefixEnd_6248517 3208492598790034382201099 := by
  unfold tailWord_6248517
  simp only [CollatzResearch.WordTrace]
  refine ⟨227902137903697545587623805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151934758602465030391749203 227902137903697545587623805)
  ·
    refine ⟨85463301713886579595358927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227902137903697545587623805 85463301713886579595358927)
    ·
      refine ⟨128194952570829869393038391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85463301713886579595358927 128194952570829869393038391)
      ·
        refine ⟨192292428856244804089557587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128194952570829869393038391 192292428856244804089557587)
        ·
          refine ⟨288438643284367206134336381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192292428856244804089557587 288438643284367206134336381)
          ·
            refine ⟨108164491231637702300376143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288438643284367206134336381 108164491231637702300376143)
            ·
              refine ⟨162246736847456553450564215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108164491231637702300376143 162246736847456553450564215)
              ·
                refine ⟨243370105271184830175846323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162246736847456553450564215 243370105271184830175846323)
                ·
                  refine ⟨365055157906777245263769485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243370105271184830175846323 365055157906777245263769485)
                  ·
                    refine ⟨136895684215041466973913557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365055157906777245263769485 136895684215041466973913557)
                    ·
                      refine ⟨3208492598790034382201099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136895684215041466973913557 3208492598790034382201099)
                      ·
                        rfl

theorem cell23_6248517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_6248517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248517 prefixEnd_6248517 := by exact prefixLift 6248517
  have htrace : WordTrace (prefixWord ++ tailWord_6248517) baseStart_6248517 baseEnd_6248517 := by
    simpa [prefixWord, tailWord_6248517, baseEnd_6248517] using wordTrace_append hprefix tailTrace_6248517
  have hstable : (prefixWord ++ tailWord_6248517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248517).length < 2 ^ (prefixWord ++ tailWord_6248517).sum := by decide
  have hdescent : baseEnd_6248517 < baseStart_6248517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248521 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 3]
def baseStart_6248521 : Nat := 118140960795 + 6248521 * 2 ^ 59
def prefixEnd_6248521 : Nat := 4983230072969 + 3 ^ 40 * 6248521 * 2
def baseEnd_6248521 : Nat := 3208494652712652366551081

theorem tailTrace_6248521 : CollatzResearch.WordTrace tailWord_6248521 prefixEnd_6248521 3208494652712652366551081 := by
  unfold tailWord_6248521
  simp only [CollatzResearch.WordTrace]
  refine ⟨227902283795683054270769417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151934855863788702847179611 227902283795683054270769417)
  ·
    refine ⟨170926712846762290703077063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227902283795683054270769417 170926712846762290703077063)
    ·
      refine ⟨256390069270143436054615595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170926712846762290703077063 256390069270143436054615595)
      ·
        refine ⟨384585103905215154081923393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256390069270143436054615595 384585103905215154081923393)
        ·
          refine ⟨288438827928911365561442545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384585103905215154081923393 288438827928911365561442545)
          ·
            refine ⟨216329120946683524171081909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288438827928911365561442545 216329120946683524171081909)
            ·
              refine ⟨20280855088751580391038929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216329120946683524171081909 20280855088751580391038929)
              ·
                refine ⟨15210641316563685293279197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20280855088751580391038929 15210641316563685293279197)
                ·
                  refine ⟨5703990493711381984979699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15210641316563685293279197 5703990493711381984979699)
                  ·
                    refine ⟨8555985740567072977469549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703990493711381984979699 8555985740567072977469549)
                    ·
                      refine ⟨3208494652712652366551081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8555985740567072977469549 3208494652712652366551081)
                      ·
                        rfl

theorem cell23_6248521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_6248521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248521 prefixEnd_6248521 := by exact prefixLift 6248521
  have htrace : WordTrace (prefixWord ++ tailWord_6248521) baseStart_6248521 baseEnd_6248521 := by
    simpa [prefixWord, tailWord_6248521, baseEnd_6248521] using wordTrace_append hprefix tailTrace_6248521
  have hstable : (prefixWord ++ tailWord_6248521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248521).length < 2 ^ (prefixWord ++ tailWord_6248521).sum := by decide
  have hdescent : baseEnd_6248521 < baseStart_6248521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248524 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_6248524 : Nat := 118140960795 + 6248524 * 2 ^ 59
def prefixEnd_6248524 : Nat := 4983230072969 + 3 ^ 40 * 6248524 * 2
def baseEnd_6248524 : Nat := 1069498731051538618271189

theorem tailTrace_6248524 : CollatzResearch.WordTrace tailWord_6248524 prefixEnd_6248524 1069498731051538618271189 := by
  unfold tailWord_6248524
  simp only [CollatzResearch.WordTrace]
  refine ⟨113951196607336092891564313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151934928809781457188752417 113951196607336092891564313)
  ·
    refine ⟨85463397455502069668673235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113951196607336092891564313 85463397455502069668673235)
    ·
      refine ⟨128195096183253104503009853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85463397455502069668673235 128195096183253104503009853)
      ·
        refine ⟨48073161068719914188628695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128195096183253104503009853 48073161068719914188628695)
        ·
          refine ⟨72109741603079871282943043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48073161068719914188628695 72109741603079871282943043)
          ·
            refine ⟨108164612404619806924414565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72109741603079871282943043 108164612404619806924414565)
            ·
              refine ⟨20280864825866213798327731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108164612404619806924414565 20280864825866213798327731)
              ·
                refine ⟨30421297238799320697491597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20280864825866213798327731 30421297238799320697491597)
                ·
                  refine ⟨11407986464549745261559349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30421297238799320697491597 11407986464549745261559349)
                  ·
                    refine ⟨1069498731051538618271189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11407986464549745261559349 1069498731051538618271189)
                    ·
                      rfl

theorem cell23_6248524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_6248524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248524 prefixEnd_6248524 := by exact prefixLift 6248524
  have htrace : WordTrace (prefixWord ++ tailWord_6248524) baseStart_6248524 baseEnd_6248524 := by
    simpa [prefixWord, tailWord_6248524, baseEnd_6248524] using wordTrace_append hprefix tailTrace_6248524
  have hstable : (prefixWord ++ tailWord_6248524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248524).length < 2 ^ (prefixWord ++ tailWord_6248524).sum := by decide
  have hdescent : baseEnd_6248524 < baseStart_6248524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248612 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_6248612 : Nat := 118140960795 + 6248612 * 2 ^ 59
def prefixEnd_6248612 : Nat := 4983230072969 + 3 ^ 40 * 6248612 * 2
def baseEnd_6248612 : Nat := 3208541379452211510513163

theorem tailTrace_6248612 : CollatzResearch.WordTrace tailWord_6248612 prefixEnd_6248612 3208541379452211510513163 := by
  unfold tailWord_6248612
  simp only [CollatzResearch.WordTrace]
  refine ⟨113952801419176688406166045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151937068558902251208221393 113952801419176688406166045)
  ·
    refine ⟨42732300532191258152312267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113952801419176688406166045 42732300532191258152312267)
    ·
      refine ⟨64098450798286887228468401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42732300532191258152312267 64098450798286887228468401)
      ·
        refine ⟨48073838098715165421351301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64098450798286887228468401 48073838098715165421351301)
        ·
          refine ⟨9013844643509093516503369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48073838098715165421351301 9013844643509093516503369)
          ·
            refine ⟨6760383482631820137377527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013844643509093516503369 6760383482631820137377527)
            ·
              refine ⟨10140575223947730206066291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760383482631820137377527 10140575223947730206066291)
              ·
                refine ⟨15210862835921595309099437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10140575223947730206066291 15210862835921595309099437)
                ·
                  refine ⟨5704073563470598240912289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15210862835921595309099437 5704073563470598240912289)
                  ·
                    refine ⟨4278055172602948680684217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5704073563470598240912289 4278055172602948680684217)
                    ·
                      refine ⟨3208541379452211510513163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278055172602948680684217 3208541379452211510513163)
                      ·
                        rfl

theorem cell23_6248612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_6248612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248612 prefixEnd_6248612 := by exact prefixLift 6248612
  have htrace : WordTrace (prefixWord ++ tailWord_6248612) baseStart_6248612 baseEnd_6248612 := by
    simpa [prefixWord, tailWord_6248612, baseEnd_6248612] using wordTrace_append hprefix tailTrace_6248612
  have hstable : (prefixWord ++ tailWord_6248612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248612).length < 2 ^ (prefixWord ++ tailWord_6248612).sum := by decide
  have hdescent : baseEnd_6248612 < baseStart_6248612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248618 : List Nat := [3, 1, 5, 1, 2, 1, 2, 8]
def baseStart_6248618 : Nat := 118140960795 + 6248618 * 2 ^ 59
def prefixEnd_6248618 : Nat := 4983230072969 + 3 ^ 40 * 6248618 * 2
def baseEnd_6248618 : Nat := 118834980012449573594005

theorem tailTrace_6248618 : CollatzResearch.WordTrace tailWord_6248618 prefixEnd_6248618 118834980012449573594005 := by
  unfold tailWord_6248618
  simp only [CollatzResearch.WordTrace]
  refine ⟨56976455419082909959262627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151937214450887759891367005 56976455419082909959262627)
  ·
    refine ⟨85464683128624364938893941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56976455419082909959262627 85464683128624364938893941)
    ·
      refine ⟨8012314043308534213021307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85464683128624364938893941 8012314043308534213021307)
      ·
        refine ⟨12018471064962801319531961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8012314043308534213021307 12018471064962801319531961)
        ·
          refine ⟨9013853298722100989648971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12018471064962801319531961 9013853298722100989648971)
          ·
            refine ⟨13520779948083151484473457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013853298722100989648971 13520779948083151484473457)
            ·
              refine ⟨10140584961062363613355093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13520779948083151484473457 10140584961062363613355093)
              ·
                refine ⟨118834980012449573594005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10140584961062363613355093 118834980012449573594005)
                ·
                  rfl

theorem cell23_6248618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_6248618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248618 prefixEnd_6248618 := by exact prefixLift 6248618
  have htrace : WordTrace (prefixWord ++ tailWord_6248618) baseStart_6248618 baseEnd_6248618 := by
    simpa [prefixWord, tailWord_6248618, baseEnd_6248618] using wordTrace_append hprefix tailTrace_6248618
  have hstable : (prefixWord ++ tailWord_6248618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248618).length < 2 ^ (prefixWord ++ tailWord_6248618).sum := by decide
  have hdescent : baseEnd_6248618 < baseStart_6248618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248622 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6248622 : Nat := 118140960795 + 6248622 * 2 ^ 59
def prefixEnd_6248622 : Nat := 4983230072969 + 3 ^ 40 * 6248622 * 2
def baseEnd_6248622 : Nat := 1069515504752918823796039

theorem tailTrace_6248622 : CollatzResearch.WordTrace tailWord_6248622 prefixEnd_6248622 1069515504752918823796039 := by
  unfold tailWord_6248622
  simp only [CollatzResearch.WordTrace]
  refine ⟨28488245946039643565024515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151937311712211432346797413 28488245946039643565024515)
  ·
    refine ⟨42732368919059465347536773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28488245946039643565024515 42732368919059465347536773)
    ·
      refine ⟨8012319172323649752663145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42732368919059465347536773 8012319172323649752663145)
      ·
        refine ⟨6009239379242737314497359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8012319172323649752663145 6009239379242737314497359)
        ·
          refine ⟨9013859068864105971746039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009239379242737314497359 9013859068864105971746039)
          ·
            refine ⟨13520788603296158957619059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013859068864105971746039 13520788603296158957619059)
            ·
              refine ⟨20281182904944238436428589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13520788603296158957619059 20281182904944238436428589)
              ·
                refine ⟨7605443589354089413660721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20281182904944238436428589 7605443589354089413660721)
                ·
                  refine ⟨5704082692015567060245541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605443589354089413660721 5704082692015567060245541)
                  ·
                    refine ⟨1069515504752918823796039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704082692015567060245541 1069515504752918823796039)
                    ·
                      rfl

theorem cell23_6248622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6248622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248622 prefixEnd_6248622 := by exact prefixLift 6248622
  have htrace : WordTrace (prefixWord ++ tailWord_6248622) baseStart_6248622 baseEnd_6248622 := by
    simpa [prefixWord, tailWord_6248622, baseEnd_6248622] using wordTrace_append hprefix tailTrace_6248622
  have hstable : (prefixWord ++ tailWord_6248622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248622).length < 2 ^ (prefixWord ++ tailWord_6248622).sum := by decide
  have hdescent : baseEnd_6248622 < baseStart_6248622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248655 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 1, 3, 2]
def baseStart_6248655 : Nat := 118140960795 + 6248655 * 2 ^ 59
def prefixEnd_6248655 : Nat := 4983230072969 + 3 ^ 40 * 6248655 * 2
def baseEnd_6248655 : Nat := 3208563459120354842275465

theorem tailTrace_6248655 : CollatzResearch.WordTrace tailWord_6248655 prefixEnd_6248655 3208563459120354842275465 := by
  unfold tailWord_6248655
  simp only [CollatzResearch.WordTrace]
  refine ⟨227907171177197595156147419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151938114118131730104098279 227907171177197595156147419)
  ·
    refine ⟨341860756765796392734221129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227907171177197595156147419 341860756765796392734221129)
    ·
      refine ⟨256395567574347294550665847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341860756765796392734221129 256395567574347294550665847)
      ·
        refine ⟨384593351361520941825998771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256395567574347294550665847 384593351361520941825998771)
        ·
          refine ⟨576890027042281412738998157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384593351361520941825998771 576890027042281412738998157)
          ·
            refine ⟨216333760140855529777124309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576890027042281412738998157 216333760140855529777124309)
            ·
              refine ⟨5070322503301301479151351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 216333760140855529777124309 5070322503301301479151351)
              ·
                refine ⟨7605483754951952218727027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070322503301301479151351 7605483754951952218727027)
                ·
                  refine ⟨11408225632427928328090541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7605483754951952218727027 11408225632427928328090541)
                  ·
                    refine ⟨4278084612160473123033953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11408225632427928328090541 4278084612160473123033953)
                    ·
                      refine ⟨3208563459120354842275465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278084612160473123033953 3208563459120354842275465)
                      ·
                        rfl

theorem cell23_6248655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 3, 2].length) (baseStart_6248655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248655 prefixEnd_6248655 := by exact prefixLift 6248655
  have htrace : WordTrace (prefixWord ++ tailWord_6248655) baseStart_6248655 baseEnd_6248655 := by
    simpa [prefixWord, tailWord_6248655, baseEnd_6248655] using wordTrace_append hprefix tailTrace_6248655
  have hstable : (prefixWord ++ tailWord_6248655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248655).length < 2 ^ (prefixWord ++ tailWord_6248655).sum := by decide
  have hdescent : baseEnd_6248655 < baseStart_6248655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248662 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6248662 : Nat := 118140960795 + 6248662 * 2 ^ 59
def prefixEnd_6248662 : Nat := 4983230072969 + 3 ^ 40 * 6248662 * 2
def baseEnd_6248662 : Nat := 3208567053484936314887933

theorem tailTrace_6248662 : CollatzResearch.WordTrace tailWord_6248662 prefixEnd_6248662 3208567053484936314887933 := by
  unfold tailWord_6248662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14244214155510764709478265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151938284325448156901101493 14244214155510764709478265)
  ·
    refine ⟨10683160616633073532108699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14244214155510764709478265 10683160616633073532108699)
    ·
      refine ⟨16024740924949610298163049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683160616633073532108699 16024740924949610298163049)
      ·
        refine ⟨12018555693712207723622287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16024740924949610298163049 12018555693712207723622287)
        ·
          refine ⟨18027833540568311585433431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12018555693712207723622287 18027833540568311585433431)
          ·
            refine ⟨27041750310852467378150147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18027833540568311585433431 27041750310852467378150147)
            ·
              refine ⟨40562625466278701067225221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27041750310852467378150147 40562625466278701067225221)
              ·
                refine ⟨7605492274927256450104729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40562625466278701067225221 7605492274927256450104729)
                ·
                  refine ⟨5704119206195442337578547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605492274927256450104729 5704119206195442337578547)
                  ·
                    refine ⟨8556178809293163506367821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5704119206195442337578547 8556178809293163506367821)
                    ·
                      refine ⟨3208567053484936314887933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8556178809293163506367821 3208567053484936314887933)
                      ·
                        rfl

theorem cell23_6248662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6248662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248662 prefixEnd_6248662 := by exact prefixLift 6248662
  have htrace : WordTrace (prefixWord ++ tailWord_6248662) baseStart_6248662 baseEnd_6248662 := by
    simpa [prefixWord, tailWord_6248662, baseEnd_6248662] using wordTrace_append hprefix tailTrace_6248662
  have hstable : (prefixWord ++ tailWord_6248662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248662).length < 2 ^ (prefixWord ++ tailWord_6248662).sum := by decide
  have hdescent : baseEnd_6248662 < baseStart_6248662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248785 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_6248785 : Nat := 118140960795 + 6248785 * 2 ^ 59
def prefixEnd_6248785 : Nat := 4983230072969 + 3 ^ 40 * 6248785 * 2
def baseEnd_6248785 : Nat := 1069543403868479777883289

theorem tailTrace_6248785 : CollatzResearch.WordTrace tailWord_6248785 prefixEnd_6248785 1069543403868479777883289 := by
  unfold tailWord_6248785
  simp only [CollatzResearch.WordTrace]
  refine ⟨227911912666726627358379809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151941275111151084905586539 227911912666726627358379809)
  ·
    refine ⟨170933934500044970518784857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227911912666726627358379809 170933934500044970518784857)
    ·
      refine ⟨128200450875033727889088643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170933934500044970518784857 128200450875033727889088643)
      ·
        refine ⟨192300676312550591833632965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128200450875033727889088643 192300676312550591833632965)
        ·
          refine ⟨36056376808603235968806181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192300676312550591833632965 36056376808603235968806181)
          ·
            refine ⟨6760570651613106744151159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36056376808603235968806181 6760570651613106744151159)
            ·
              refine ⟨10140855977419660116226739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760570651613106744151159 10140855977419660116226739)
              ·
                refine ⟨15211283966129490174340109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10140855977419660116226739 15211283966129490174340109)
                ·
                  refine ⟨5704231487298558815377541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15211283966129490174340109 5704231487298558815377541)
                  ·
                    refine ⟨1069543403868479777883289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704231487298558815377541 1069543403868479777883289)
                    ·
                      rfl

theorem cell23_6248785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_6248785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248785 prefixEnd_6248785 := by exact prefixLift 6248785
  have htrace : WordTrace (prefixWord ++ tailWord_6248785) baseStart_6248785 baseEnd_6248785 := by
    simpa [prefixWord, tailWord_6248785, baseEnd_6248785] using wordTrace_append hprefix tailTrace_6248785
  have hstable : (prefixWord ++ tailWord_6248785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248785).length < 2 ^ (prefixWord ++ tailWord_6248785).sum := by decide
  have hdescent : baseEnd_6248785 < baseStart_6248785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248811 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 3, 5]
def baseStart_6248811 : Nat := 118140960795 + 6248811 * 2 ^ 59
def prefixEnd_6248811 : Nat := 4983230072969 + 3 ^ 40 * 6248811 * 2
def baseEnd_6248811 : Nat := 1069547854034152077308249

theorem tailTrace_6248811 : CollatzResearch.WordTrace tailWord_6248811 prefixEnd_6248811 1069547854034152077308249 := by
  unfold tailWord_6248811
  simp only [CollatzResearch.WordTrace]
  refine ⟨227912860964632433798826287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151941907309754955865884191 227912860964632433798826287)
  ·
    refine ⟨341869291446948650698239431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227912860964632433798826287 341869291446948650698239431)
    ·
      refine ⟨512803937170422976047359147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341869291446948650698239431 512803937170422976047359147)
      ·
        refine ⟨769205905755634464071038721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512803937170422976047359147 769205905755634464071038721)
        ·
          refine ⟨576904429316725848053279041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769205905755634464071038721 576904429316725848053279041)
          ·
            refine ⟨432678321987544386039959281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576904429316725848053279041 432678321987544386039959281)
            ·
              refine ⟨324508741490658289529969461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432678321987544386039959281 324508741490658289529969461)
              ·
                refine ⟨30422694514749214643434637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324508741490658289529969461 30422694514749214643434637)
                ·
                  refine ⟨11408510443030955491287989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30422694514749214643434637 11408510443030955491287989)
                  ·
                    refine ⟨1069547854034152077308249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11408510443030955491287989 1069547854034152077308249)
                    ·
                      rfl

theorem cell23_6248811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 5].length) (baseStart_6248811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248811 prefixEnd_6248811 := by exact prefixLift 6248811
  have htrace : WordTrace (prefixWord ++ tailWord_6248811) baseStart_6248811 baseEnd_6248811 := by
    simpa [prefixWord, tailWord_6248811, baseEnd_6248811] using wordTrace_append hprefix tailTrace_6248811
  have hstable : (prefixWord ++ tailWord_6248811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248811).length < 2 ^ (prefixWord ++ tailWord_6248811).sum := by decide
  have hdescent : baseEnd_6248811 < baseStart_6248811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248858 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_6248858 : Nat := 118140960795 + 6248858 * 2 ^ 59
def prefixEnd_6248858 : Nat := 4983230072969 + 3 ^ 40 * 6248858 * 2
def baseEnd_6248858 : Nat := 1069555898564405849345677

theorem tailTrace_6248858 : CollatzResearch.WordTrace tailWord_6248858 prefixEnd_6248858 1069555898564405849345677 := by
  unfold tailWord_6248858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56978643798865540206446807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151943050130308107217191485 56978643798865540206446807)
  ·
    refine ⟨85467965698298310309670211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56978643798865540206446807 85467965698298310309670211)
    ·
      refine ⟨128201948547447465464505317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85467965698298310309670211 128201948547447465464505317)
      ·
        refine ⟨24037865352646399774594747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128201948547447465464505317 24037865352646399774594747)
        ·
          refine ⟨36056798028969599661892121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24037865352646399774594747 36056798028969599661892121)
          ·
            refine ⟨27042598521727199746419091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36056798028969599661892121 27042598521727199746419091)
            ·
              refine ⟨40563897782590799619628637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27042598521727199746419091 40563897782590799619628637)
              ·
                refine ⟨15211461668471549857360739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40563897782590799619628637 15211461668471549857360739)
                ·
                  refine ⟨22817192502707324786041109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15211461668471549857360739 22817192502707324786041109)
                  ·
                    refine ⟨1069555898564405849345677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22817192502707324786041109 1069555898564405849345677)
                    ·
                      rfl

theorem cell23_6248858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_6248858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248858 prefixEnd_6248858 := by exact prefixLift 6248858
  have htrace : WordTrace (prefixWord ++ tailWord_6248858) baseStart_6248858 baseEnd_6248858 := by
    simpa [prefixWord, tailWord_6248858, baseEnd_6248858] using wordTrace_append hprefix tailTrace_6248858
  have hstable : (prefixWord ++ tailWord_6248858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248858).length < 2 ^ (prefixWord ++ tailWord_6248858).sum := by decide
  have hdescent : baseEnd_6248858 < baseStart_6248858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248892 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_6248892 : Nat := 118140960795 + 6248892 * 2 ^ 59
def prefixEnd_6248892 : Nat := 4983230072969 + 3 ^ 40 * 6248892 * 2
def baseEnd_6248892 : Nat := 1069561718011823471670625

theorem tailTrace_6248892 : CollatzResearch.WordTrace tailWord_6248892 prefixEnd_6248892 1069561718011823471670625 := by
  unfold tailWord_6248892
  simp only [CollatzResearch.WordTrace]
  refine ⟨113957907638669492316262465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151943876851559323088349953 113957907638669492316262465)
  ·
    refine ⟨85468430729002119237196849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113957907638669492316262465 85468430729002119237196849)
    ·
      refine ⟨64101323046751589427897637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85468430729002119237196849 64101323046751589427897637)
      ·
        refine ⟨12018998071265923017730807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64101323046751589427897637 12018998071265923017730807)
        ·
          refine ⟨18028497106898884526596211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12018998071265923017730807 18028497106898884526596211)
          ·
            refine ⟨27042745660348326789894317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18028497106898884526596211 27042745660348326789894317)
            ·
              refine ⟨10141029622630622546210369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27042745660348326789894317 10141029622630622546210369)
              ·
                refine ⟨7605772216972966909657777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10141029622630622546210369 7605772216972966909657777)
                ·
                  refine ⟨5704329162729725182243333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605772216972966909657777 5704329162729725182243333)
                  ·
                    refine ⟨1069561718011823471670625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704329162729725182243333 1069561718011823471670625)
                    ·
                      rfl

theorem cell23_6248892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_6248892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248892 prefixEnd_6248892 := by exact prefixLift 6248892
  have htrace : WordTrace (prefixWord ++ tailWord_6248892) baseStart_6248892 baseEnd_6248892 := by
    simpa [prefixWord, tailWord_6248892, baseEnd_6248892] using wordTrace_append hprefix tailTrace_6248892
  have hstable : (prefixWord ++ tailWord_6248892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248892).length < 2 ^ (prefixWord ++ tailWord_6248892).sum := by decide
  have hdescent : baseEnd_6248892 < baseStart_6248892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248933 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6248933 : Nat := 118140960795 + 6248933 * 2 ^ 59
def prefixEnd_6248933 : Nat := 4983230072969 + 3 ^ 40 * 6248933 * 2
def baseEnd_6248933 : Nat := 3208706206742304754599187

theorem tailTrace_6248933 : CollatzResearch.WordTrace tailWord_6248933 prefixEnd_6248933 3208706206742304754599187 := by
  unfold tailWord_6248933
  simp only [CollatzResearch.WordTrace]
  refine ⟨227917310670190448634767453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151944873780126965756511635 227917310670190448634767453)
  ·
    refine ⟨85468991501321418238037795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227917310670190448634767453 85468991501321418238037795)
    ·
      refine ⟨128203487251982127357056693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85468991501321418238037795 128203487251982127357056693)
      ·
        refine ⟨12019076929873324439724065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128203487251982127357056693 12019076929873324439724065)
        ·
          refine ⟨9014307697404993329793049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12019076929873324439724065 9014307697404993329793049)
          ·
            refine ⟨6760730773053744997344787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014307697404993329793049 6760730773053744997344787)
            ·
              refine ⟨10141096159580617496017181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760730773053744997344787 10141096159580617496017181)
              ·
                refine ⟨3802911059842731561006443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10141096159580617496017181 3802911059842731561006443)
                ·
                  refine ⟨5704366589764097341509665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802911059842731561006443 5704366589764097341509665)
                  ·
                    refine ⟨4278274942323073006132249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5704366589764097341509665 4278274942323073006132249)
                    ·
                      refine ⟨3208706206742304754599187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278274942323073006132249 3208706206742304754599187)
                      ·
                        rfl

theorem cell23_6248933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6248933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248933 prefixEnd_6248933 := by exact prefixLift 6248933
  have htrace : WordTrace (prefixWord ++ tailWord_6248933) baseStart_6248933 baseEnd_6248933 := by
    simpa [prefixWord, tailWord_6248933, baseEnd_6248933] using wordTrace_append hprefix tailTrace_6248933
  have hstable : (prefixWord ++ tailWord_6248933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248933).length < 2 ^ (prefixWord ++ tailWord_6248933).sum := by decide
  have hdescent : baseEnd_6248933 < baseStart_6248933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6248968 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6248968 : Nat := 118140960795 + 6248968 * 2 ^ 59
def prefixEnd_6248968 : Nat := 4983230072969 + 3 ^ 40 * 6248968 * 2
def baseEnd_6248968 : Nat := 3208724178565212117661525

theorem tailTrace_6248968 : CollatzResearch.WordTrace tailWord_6248968 prefixEnd_6248968 3208724178565212117661525 := by
  unfold tailWord_6248968
  simp only [CollatzResearch.WordTrace]
  refine ⟨113959293612531824806145779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151945724816709099741527705 113959293612531824806145779)
  ·
    refine ⟨170938940418797737209218669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113959293612531824806145779 170938940418797737209218669)
    ·
      refine ⟨64102102657049151453457001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170938940418797737209218669 64102102657049151453457001)
      ·
        refine ⟨48076576992786863590092751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64102102657049151453457001 48076576992786863590092751)
        ·
          refine ⟨72114865489180295385139127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48076576992786863590092751 72114865489180295385139127)
          ·
            refine ⟨108172298233770443077708691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72114865489180295385139127 108172298233770443077708691)
            ·
              refine ⟨162258447350655664616563037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108172298233770443077708691 162258447350655664616563037)
              ·
                refine ⟨60846917756495874231211139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162258447350655664616563037 60846917756495874231211139)
                ·
                  refine ⟨91270376634743811346816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60846917756495874231211139 91270376634743811346816709)
                  ·
                    refine ⟨17113195619014464627528133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91270376634743811346816709 17113195619014464627528133)
                    ·
                      refine ⟨3208724178565212117661525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17113195619014464627528133 3208724178565212117661525)
                      ·
                        rfl

theorem cell23_6248968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6248968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6248968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6248968 prefixEnd_6248968 := by exact prefixLift 6248968
  have htrace : WordTrace (prefixWord ++ tailWord_6248968) baseStart_6248968 baseEnd_6248968 := by
    simpa [prefixWord, tailWord_6248968, baseEnd_6248968] using wordTrace_append hprefix tailTrace_6248968
  have hstable : (prefixWord ++ tailWord_6248968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6248968).length < 2 ^ (prefixWord ++ tailWord_6248968).sum := by decide
  have hdescent : baseEnd_6248968 < baseStart_6248968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6248968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249015 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_6249015 : Nat := 118140960795 + 6249015 * 2 ^ 59
def prefixEnd_6249015 : Nat := 4983230072969 + 3 ^ 40 * 6249015 * 2
def baseEnd_6249015 : Nat := 3208748312155973433773809

theorem tailTrace_6249015 : CollatzResearch.WordTrace tailWord_6249015 prefixEnd_6249015 3208748312155973433773809 := by
  unfold tailWord_6249015
  simp only [CollatzResearch.WordTrace]
  refine ⟨227920301455893376639252499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151946867637262251092834999 227920301455893376639252499)
  ·
    refine ⟨341880452183840064958878749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227920301455893376639252499 341880452183840064958878749)
    ·
      refine ⟨128205169568940024359579531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341880452183840064958878749 128205169568940024359579531)
      ·
        refine ⟨192307754353410036539369297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128205169568940024359579531 192307754353410036539369297)
        ·
          refine ⟨144230815765057527404526973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192307754353410036539369297 144230815765057527404526973)
          ·
            refine ⟨54086555911896572776697615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144230815765057527404526973 54086555911896572776697615)
            ·
              refine ⟨81129833867844859165046423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54086555911896572776697615 81129833867844859165046423)
              ·
                refine ⟨121694750801767288747569635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81129833867844859165046423 121694750801767288747569635)
                ·
                  refine ⟨182542126202650933121354453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121694750801767288747569635 182542126202650933121354453)
                  ·
                    refine ⟨4278331082874631245031745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182542126202650933121354453 4278331082874631245031745)
                    ·
                      refine ⟨3208748312155973433773809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278331082874631245031745 3208748312155973433773809)
                      ·
                        rfl

theorem cell23_6249015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_6249015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249015 prefixEnd_6249015 := by exact prefixLift 6249015
  have htrace : WordTrace (prefixWord ++ tailWord_6249015) baseStart_6249015 baseEnd_6249015 := by
    simpa [prefixWord, tailWord_6249015, baseEnd_6249015] using wordTrace_append hprefix tailTrace_6249015
  have hstable : (prefixWord ++ tailWord_6249015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249015).length < 2 ^ (prefixWord ++ tailWord_6249015).sum := by decide
  have hdescent : baseEnd_6249015 < baseStart_6249015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249065 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_6249065 : Nat := 118140960795 + 6249065 * 2 ^ 59
def prefixEnd_6249065 : Nat := 4983230072969 + 3 ^ 40 * 6249065 * 2
def baseEnd_6249065 : Nat := 3208773986188698238148579

theorem tailTrace_6249065 : CollatzResearch.WordTrace tailWord_6249065 prefixEnd_6249065 3208773986188698238148579 := by
  unfold tailWord_6249065
  simp only [CollatzResearch.WordTrace]
  refine ⟨227922125105712235178572649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151948083403808156785715099 227922125105712235178572649)
  ·
    refine ⟨170941593829284176383929487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227922125105712235178572649 170941593829284176383929487)
    ·
      refine ⟨256412390743926264575894231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170941593829284176383929487 256412390743926264575894231)
      ·
        refine ⟨384618586115889396863841347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256412390743926264575894231 384618586115889396863841347)
        ·
          refine ⟨576927879173834095295762021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384618586115889396863841347 576927879173834095295762021)
          ·
            refine ⟨108173977345093892867955379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576927879173834095295762021 108173977345093892867955379)
            ·
              refine ⟨162260966017640839301933069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108173977345093892867955379 162260966017640839301933069)
              ·
                refine ⟨60847862256615314738224901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162260966017640839301933069 60847862256615314738224901)
                ·
                  refine ⟨11408974173115371513417169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60847862256615314738224901 11408974173115371513417169)
                  ·
                    refine ⟨8556730629836528635062877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11408974173115371513417169 8556730629836528635062877)
                    ·
                      refine ⟨3208773986188698238148579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8556730629836528635062877 3208773986188698238148579)
                      ·
                        rfl

theorem cell23_6249065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_6249065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249065 prefixEnd_6249065 := by exact prefixLift 6249065
  have htrace : WordTrace (prefixWord ++ tailWord_6249065) baseStart_6249065 baseEnd_6249065 := by
    simpa [prefixWord, tailWord_6249065, baseEnd_6249065] using wordTrace_append hprefix tailTrace_6249065
  have hstable : (prefixWord ++ tailWord_6249065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249065).length < 2 ^ (prefixWord ++ tailWord_6249065).sum := by decide
  have hdescent : baseEnd_6249065 < baseStart_6249065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249095 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_6249095 : Nat := 118140960795 + 6249095 * 2 ^ 59
def prefixEnd_6249095 : Nat := 4983230072969 + 3 ^ 40 * 6249095 * 2
def baseEnd_6249095 : Nat := 3208789390608333120773441

theorem tailTrace_6249095 : CollatzResearch.WordTrace tailWord_6249095 prefixEnd_6249095 3208789390608333120773441 := by
  unfold tailWord_6249095
  simp only [CollatzResearch.WordTrace]
  refine ⟨227923219295603550302164739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151948812863735700201443159 227923219295603550302164739)
  ·
    refine ⟨341884828943405325453247109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227923219295603550302164739 341884828943405325453247109)
    ·
      refine ⟨64103405426888498522483833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341884828943405325453247109 64103405426888498522483833)
      ·
        refine ⟨48077554070166373891862875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64103405426888498522483833 48077554070166373891862875)
        ·
          refine ⟨72116331105249560837794313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48077554070166373891862875 72116331105249560837794313)
          ·
            refine ⟨54087248328937170628345735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72116331105249560837794313 54087248328937170628345735)
            ·
              refine ⟨81130872493405755942518603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54087248328937170628345735 81130872493405755942518603)
              ·
                refine ⟨121696308740108633913777905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81130872493405755942518603 121696308740108633913777905)
                ·
                  refine ⟨91272231555081475435333429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121696308740108633913777905 91272231555081475435333429)
                  ·
                    refine ⟨8556771708288888322062509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91272231555081475435333429 8556771708288888322062509)
                    ·
                      refine ⟨3208789390608333120773441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8556771708288888322062509 3208789390608333120773441)
                      ·
                        rfl

theorem cell23_6249095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_6249095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249095 prefixEnd_6249095 := by exact prefixLift 6249095
  have htrace : WordTrace (prefixWord ++ tailWord_6249095) baseStart_6249095 baseEnd_6249095 := by
    simpa [prefixWord, tailWord_6249095, baseEnd_6249095] using wordTrace_append hprefix tailTrace_6249095
  have hstable : (prefixWord ++ tailWord_6249095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249095).length < 2 ^ (prefixWord ++ tailWord_6249095).sum := by decide
  have hdescent : baseEnd_6249095 < baseStart_6249095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249106 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6249106 : Nat := 118140960795 + 6249106 * 2 ^ 59
def prefixEnd_6249106 : Nat := 4983230072969 + 3 ^ 40 * 6249106 * 2
def baseEnd_6249106 : Nat := 1069598346298510859245297

theorem tailTrace_6249106 : CollatzResearch.WordTrace tailWord_6249106 prefixEnd_6249106 1069598346298510859245297 := by
  unfold tailWord_6249106
  simp only [CollatzResearch.WordTrace]
  refine ⟨56980905124640924795203793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151949080332375799453876781 56980905124640924795203793)
  ·
    refine ⟨42735678843480693596402845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56980905124640924795203793 42735678843480693596402845)
    ·
      refine ⟨16025879566305260098651067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42735678843480693596402845 16025879566305260098651067)
      ·
        refine ⟨24038819349457890147976601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16025879566305260098651067 24038819349457890147976601)
        ·
          refine ⟨18029114512093417610982451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24038819349457890147976601 18029114512093417610982451)
          ·
            refine ⟨27043671768140126416473677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029114512093417610982451 27043671768140126416473677)
            ·
              refine ⟨10141376913052547406177629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27043671768140126416473677 10141376913052547406177629)
              ·
                refine ⟨3803016342394705277316611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10141376913052547406177629 3803016342394705277316611)
                ·
                  refine ⟨5704524513592057915974917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803016342394705277316611 5704524513592057915974917)
                  ·
                    refine ⟨1069598346298510859245297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704524513592057915974917 1069598346298510859245297)
                    ·
                      rfl

theorem cell23_6249106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6249106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249106 prefixEnd_6249106 := by exact prefixLift 6249106
  have htrace : WordTrace (prefixWord ++ tailWord_6249106) baseStart_6249106 baseEnd_6249106 := by
    simpa [prefixWord, tailWord_6249106, baseEnd_6249106] using wordTrace_append hprefix tailTrace_6249106
  have hstable : (prefixWord ++ tailWord_6249106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249106).length < 2 ^ (prefixWord ++ tailWord_6249106).sum := by decide
  have hdescent : baseEnd_6249106 < baseStart_6249106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249145 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_6249145 : Nat := 118140960795 + 6249145 * 2 ^ 59
def prefixEnd_6249145 : Nat := 4983230072969 + 3 ^ 40 * 6249145 * 2
def baseEnd_6249145 : Nat := 1069605021547019308382737

theorem tailTrace_6249145 : CollatzResearch.WordTrace tailWord_6249145 prefixEnd_6249145 1069605021547019308382737 := by
  unfold tailWord_6249145
  simp only [CollatzResearch.WordTrace]
  refine ⟨227925042945422408841484889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151950028630281605894323259 227925042945422408841484889)
  ·
    refine ⟨170943782209066806631113667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227925042945422408841484889 170943782209066806631113667)
    ·
      refine ⟨256415673313600209946670501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170943782209066806631113667 256415673313600209946670501)
      ·
        refine ⟨48077938746300039365000719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256415673313600209946670501 48077938746300039365000719)
        ·
          refine ⟨72116908119450059047501079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48077938746300039365000719 72116908119450059047501079)
          ·
            refine ⟨108175362179175088571251619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72116908119450059047501079 108175362179175088571251619)
            ·
              refine ⟨162263043268762632856877429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108175362179175088571251619 162263043268762632856877429)
              ·
                refine ⟨15212160306446496830332259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162263043268762632856877429 15212160306446496830332259)
                ·
                  refine ⟨22818240459669745245498389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15212160306446496830332259 22818240459669745245498389)
                  ·
                    refine ⟨1069605021547019308382737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22818240459669745245498389 1069605021547019308382737)
                    ·
                      rfl

theorem cell23_6249145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_6249145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249145 prefixEnd_6249145 := by exact prefixLift 6249145
  have htrace : WordTrace (prefixWord ++ tailWord_6249145) baseStart_6249145 baseEnd_6249145 := by
    simpa [prefixWord, tailWord_6249145, baseEnd_6249145] using wordTrace_append hprefix tailTrace_6249145
  have hstable : (prefixWord ++ tailWord_6249145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249145).length < 2 ^ (prefixWord ++ tailWord_6249145).sum := by decide
  have hdescent : baseEnd_6249145 < baseStart_6249145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249149 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_6249149 : Nat := 118140960795 + 6249149 * 2 ^ 59
def prefixEnd_6249149 : Nat := 4983230072969 + 3 ^ 40 * 6249149 * 2
def baseEnd_6249149 : Nat := 1069605706187891969832731

theorem tailTrace_6249149 : CollatzResearch.WordTrace tailWord_6249149 prefixEnd_6249149 1069605706187891969832731 := by
  unfold tailWord_6249149
  simp only [CollatzResearch.WordTrace]
  refine ⟨227925188837407917524630501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151950125891605278349753667 227925188837407917524630501)
  ·
    refine ⟨42735972907013984535868219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227925188837407917524630501 42735972907013984535868219)
    ·
      refine ⟨64103959360520976803802329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42735972907013984535868219 64103959360520976803802329)
      ·
        refine ⟨48077969520390732602851747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64103959360520976803802329 48077969520390732602851747)
        ·
          refine ⟨72116954280586098904277621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48077969520390732602851747 72116954280586098904277621)
          ·
            refine ⟨6760964463804946772276027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72116954280586098904277621 6760964463804946772276027)
            ·
              refine ⟨10141446695707420158414041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760964463804946772276027 10141446695707420158414041)
              ·
                refine ⟨7606085021780565118810531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10141446695707420158414041 7606085021780565118810531)
                ·
                  refine ⟨11409127532670847678215797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606085021780565118810531 11409127532670847678215797)
                  ·
                    refine ⟨1069605706187891969832731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11409127532670847678215797 1069605706187891969832731)
                    ·
                      rfl

theorem cell23_6249149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_6249149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249149 prefixEnd_6249149 := by exact prefixLift 6249149
  have htrace : WordTrace (prefixWord ++ tailWord_6249149) baseStart_6249149 baseEnd_6249149 := by
    simpa [prefixWord, tailWord_6249149, baseEnd_6249149] using wordTrace_append hprefix tailTrace_6249149
  have hstable : (prefixWord ++ tailWord_6249149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249149).length < 2 ^ (prefixWord ++ tailWord_6249149).sum := by decide
  have hdescent : baseEnd_6249149 < baseStart_6249149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249152 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_6249152 : Nat := 118140960795 + 6249152 * 2 ^ 59
def prefixEnd_6249152 : Nat := 4983230072969 + 3 ^ 40 * 6249152 * 2
def baseEnd_6249152 : Nat := 3208818659005639397760679

theorem tailTrace_6249152 : CollatzResearch.WordTrace tailWord_6249152 prefixEnd_6249152 3208818659005639397760679 := by
  unfold tailWord_6249152
  simp only [CollatzResearch.WordTrace]
  refine ⟨113962649128198524518494855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151950198837598032691326473 113962649128198524518494855)
  ·
    refine ⟨170943973692297786777742283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113962649128198524518494855 170943973692297786777742283)
    ·
      refine ⟨256415960538446680166613425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170943973692297786777742283 256415960538446680166613425)
      ·
        refine ⟨192311970403835010124960069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256415960538446680166613425 192311970403835010124960069)
        ·
          refine ⟨36058494450719064398430013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192311970403835010124960069 36058494450719064398430013)
          ·
            refine ⟨13521935419019649149411255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36058494450719064398430013 13521935419019649149411255)
            ·
              refine ⟨20282903128529473724116883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13521935419019649149411255 20282903128529473724116883)
              ·
                refine ⟨30424354692794210586175325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20282903128529473724116883 30424354692794210586175325)
                ·
                  refine ⟨11409133009797828969815747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30424354692794210586175325 11409133009797828969815747)
                  ·
                    refine ⟨17113699514696743454723621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11409133009797828969815747 17113699514696743454723621)
                    ·
                      refine ⟨3208818659005639397760679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17113699514696743454723621 3208818659005639397760679)
                      ·
                        rfl

theorem cell23_6249152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_6249152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249152 prefixEnd_6249152 := by exact prefixLift 6249152
  have htrace : WordTrace (prefixWord ++ tailWord_6249152) baseStart_6249152 baseEnd_6249152 := by
    simpa [prefixWord, tailWord_6249152, baseEnd_6249152] using wordTrace_append hprefix tailTrace_6249152
  have hstable : (prefixWord ++ tailWord_6249152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249152).length < 2 ^ (prefixWord ++ tailWord_6249152).sum := by decide
  have hdescent : baseEnd_6249152 < baseStart_6249152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249156 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_6249156 : Nat := 118140960795 + 6249156 * 2 ^ 59
def prefixEnd_6249156 : Nat := 4983230072969 + 3 ^ 40 * 6249156 * 2
def baseEnd_6249156 : Nat := 3208820712928257382110661

theorem tailTrace_6249156 : CollatzResearch.WordTrace tailWord_6249156 prefixEnd_6249156 3208820712928257382110661 := by
  unfold tailWord_6249156
  simp only [CollatzResearch.WordTrace]
  refine ⟨113962722074191278860067661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151950296098921705146756881 113962722074191278860067661)
  ·
    refine ⟨42736020777821729572525373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113962722074191278860067661 42736020777821729572525373)
    ·
      refine ⟨16026007791683148589697015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42736020777821729572525373 16026007791683148589697015)
      ·
        refine ⟨24039011687524722884545523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16026007791683148589697015 24039011687524722884545523)
        ·
          refine ⟨36058517531287084326818285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24039011687524722884545523 36058517531287084326818285)
          ·
            refine ⟨13521944074232656622556857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36058517531287084326818285 13521944074232656622556857)
            ·
              refine ⟨10141458055674492466917643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13521944074232656622556857 10141458055674492466917643)
              ·
                refine ⟨15212187083511738700376465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10141458055674492466917643 15212187083511738700376465)
                ·
                  refine ⟨11409140312633804025282349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15212187083511738700376465 11409140312633804025282349)
                  ·
                    refine ⟨4278427617237676509480881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11409140312633804025282349 4278427617237676509480881)
                    ·
                      refine ⟨3208820712928257382110661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278427617237676509480881 3208820712928257382110661)
                      ·
                        rfl

theorem cell23_6249156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_6249156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249156 prefixEnd_6249156 := by exact prefixLift 6249156
  have htrace : WordTrace (prefixWord ++ tailWord_6249156) baseStart_6249156 baseEnd_6249156 := by
    simpa [prefixWord, tailWord_6249156, baseEnd_6249156] using wordTrace_append hprefix tailTrace_6249156
  have hstable : (prefixWord ++ tailWord_6249156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249156).length < 2 ^ (prefixWord ++ tailWord_6249156).sum := by decide
  have hdescent : baseEnd_6249156 < baseStart_6249156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249162 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_6249162 : Nat := 118140960795 + 6249162 * 2 ^ 59
def prefixEnd_6249162 : Nat := 4983230072969 + 3 ^ 40 * 6249162 * 2
def baseEnd_6249162 : Nat := 1069607931270728119545211

theorem tailTrace_6249162 : CollatzResearch.WordTrace tailWord_6249162 prefixEnd_6249162 1069607931270728119545211 := by
  unfold tailWord_6249162
  simp only [CollatzResearch.WordTrace]
  refine ⟨56981415746590205186213435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151950441990907213829902493 56981415746590205186213435)
  ·
    refine ⟨85472123619885307779320153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56981415746590205186213435 85472123619885307779320153)
    ·
      refine ⟨64104092714913980834490115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85472123619885307779320153 64104092714913980834490115)
      ·
        refine ⟨96156139072370971251735173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64104092714913980834490115 96156139072370971251735173)
        ·
          refine ⟨18029276076069557109700345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96156139072370971251735173 18029276076069557109700345)
          ·
            refine ⟨13521957057052167832275259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18029276076069557109700345 13521957057052167832275259)
            ·
              refine ⟨20282935585578251748412889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13521957057052167832275259 20282935585578251748412889)
              ·
                refine ⟨15212201689183688811309667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20282935585578251748412889 15212201689183688811309667)
                ·
                  refine ⟨22818302533775533216964501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15212201689183688811309667 22818302533775533216964501)
                  ·
                    refine ⟨1069607931270728119545211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22818302533775533216964501 1069607931270728119545211)
                    ·
                      rfl

theorem cell23_6249162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_6249162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249162 prefixEnd_6249162 := by exact prefixLift 6249162
  have htrace : WordTrace (prefixWord ++ tailWord_6249162) baseStart_6249162 baseEnd_6249162 := by
    simpa [prefixWord, tailWord_6249162, baseEnd_6249162] using wordTrace_append hprefix tailTrace_6249162
  have hstable : (prefixWord ++ tailWord_6249162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249162).length < 2 ^ (prefixWord ++ tailWord_6249162).sum := by decide
  have hdescent : baseEnd_6249162 < baseStart_6249162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249169 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_6249169 : Nat := 118140960795 + 6249169 * 2 ^ 59
def prefixEnd_6249169 : Nat := 4983230072969 + 3 ^ 40 * 6249169 * 2
def baseEnd_6249169 : Nat := 3208827388176765831248101

theorem tailTrace_6249169 : CollatzResearch.WordTrace tailWord_6249169 prefixEnd_6249169 3208827388176765831248101 := by
  unfold tailWord_6249169
  simp only [CollatzResearch.WordTrace]
  refine ⟨227925918297335460940358561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151950612198223640626905707 227925918297335460940358561)
  ·
    refine ⟨170944438723001595705268921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227925918297335460940358561 170944438723001595705268921)
    ·
      refine ⟨128208329042251196778951691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170944438723001595705268921 128208329042251196778951691)
      ·
        refine ⟨192312493563376795168427537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128208329042251196778951691 192312493563376795168427537)
        ·
          refine ⟨144234370172532596376320653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192312493563376795168427537 144234370172532596376320653)
          ·
            refine ⟨54087888814699723641120245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144234370172532596376320653 54087888814699723641120245)
            ·
              refine ⟨5070739576378099091355023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54087888814699723641120245 5070739576378099091355023)
              ·
                refine ⟨7606109364567148637032535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070739576378099091355023 7606109364567148637032535)
                ·
                  refine ⟨11409164046850722955548803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606109364567148637032535 11409164046850722955548803)
                  ·
                    refine ⟨17113746070276084433323205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11409164046850722955548803 17113746070276084433323205)
                    ·
                      refine ⟨3208827388176765831248101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17113746070276084433323205 3208827388176765831248101)
                      ·
                        rfl

theorem cell23_6249169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_6249169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249169 prefixEnd_6249169 := by exact prefixLift 6249169
  have htrace : WordTrace (prefixWord ++ tailWord_6249169) baseStart_6249169 baseEnd_6249169 := by
    simpa [prefixWord, tailWord_6249169, baseEnd_6249169] using wordTrace_append hprefix tailTrace_6249169
  have hstable : (prefixWord ++ tailWord_6249169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249169).length < 2 ^ (prefixWord ++ tailWord_6249169).sum := by decide
  have hdescent : baseEnd_6249169 < baseStart_6249169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249180 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6249180 : Nat := 118140960795 + 6249180 * 2 ^ 59
def prefixEnd_6249180 : Nat := 4983230072969 + 3 ^ 40 * 6249180 * 2
def baseEnd_6249180 : Nat := 3208833036463965288210551

theorem tailTrace_6249180 : CollatzResearch.WordTrace tailWord_6249180 prefixEnd_6249180 3208833036463965288210551 := by
  unfold tailWord_6249180
  simp only [CollatzResearch.WordTrace]
  refine ⟨113963159750147804909504497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151950879666863739879339329 113963159750147804909504497)
  ·
    refine ⟨85472369812610853682128373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113963159750147804909504497 85472369812610853682128373)
    ·
      refine ⟨8013034669932267532699535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85472369812610853682128373 8013034669932267532699535)
      ·
        refine ⟨12019552004898401299049303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8013034669932267532699535 12019552004898401299049303)
        ·
          refine ⟨18029328007347601948573955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019552004898401299049303 18029328007347601948573955)
          ·
            refine ⟨27043992011021402922860933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029328007347601948573955 27043992011021402922860933)
            ·
              refine ⟨5070748502066513048036425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27043992011021402922860933 5070748502066513048036425)
              ·
                refine ⟨3803061376549884786027319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5070748502066513048036425 3803061376549884786027319)
                ·
                  refine ⟨5704592064824827179040979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803061376549884786027319 5704592064824827179040979)
                  ·
                    refine ⟨8556888097237240768561469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5704592064824827179040979 8556888097237240768561469)
                    ·
                      refine ⟨3208833036463965288210551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8556888097237240768561469 3208833036463965288210551)
                      ·
                        rfl

theorem cell23_6249180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6249180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249180 prefixEnd_6249180 := by exact prefixLift 6249180
  have htrace : WordTrace (prefixWord ++ tailWord_6249180) baseStart_6249180 baseEnd_6249180 := by
    simpa [prefixWord, tailWord_6249180, baseEnd_6249180] using wordTrace_append hprefix tailTrace_6249180
  have hstable : (prefixWord ++ tailWord_6249180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249180).length < 2 ^ (prefixWord ++ tailWord_6249180).sum := by decide
  have hdescent : baseEnd_6249180 < baseStart_6249180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249215 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_6249215 : Nat := 118140960795 + 6249215 * 2 ^ 59
def prefixEnd_6249215 : Nat := 4983230072969 + 3 ^ 40 * 6249215 * 2
def baseEnd_6249215 : Nat := 3208851008286872651272889

theorem tailTrace_6249215 : CollatzResearch.WordTrace tailWord_6249215 prefixEnd_6249215 3208851008286872651272889 := by
  unfold tailWord_6249215
  simp only [CollatzResearch.WordTrace]
  refine ⟨227927596055168810796533099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151951730703445873864355399 227927596055168810796533099)
  ·
    refine ⟨341891394082753216194799649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227927596055168810796533099 341891394082753216194799649)
    ·
      refine ⟨256418545562064912146099737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341891394082753216194799649 256418545562064912146099737)
      ·
        refine ⟨192313909171548684109574803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256418545562064912146099737 192313909171548684109574803)
        ·
          refine ⟨288470863757323026164362205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192313909171548684109574803 288470863757323026164362205)
          ·
            refine ⟨108176573908996134811635827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288470863757323026164362205 108176573908996134811635827)
            ·
              refine ⟨162264860863494202217453741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108176573908996134811635827 162264860863494202217453741)
              ·
                refine ⟨60849322823810325831545153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162264860863494202217453741 60849322823810325831545153)
                ·
                  refine ⟨45636992117857744373658865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60849322823810325831545153 45636992117857744373658865)
                  ·
                    refine ⟨34227744088393308280244149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45636992117857744373658865 34227744088393308280244149)
                    ·
                      refine ⟨3208851008286872651272889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34227744088393308280244149 3208851008286872651272889)
                      ·
                        rfl

theorem cell23_6249215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_6249215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249215 prefixEnd_6249215 := by exact prefixLift 6249215
  have htrace : WordTrace (prefixWord ++ tailWord_6249215) baseStart_6249215 baseEnd_6249215 := by
    simpa [prefixWord, tailWord_6249215, baseEnd_6249215] using wordTrace_append hprefix tailTrace_6249215
  have hstable : (prefixWord ++ tailWord_6249215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249215).length < 2 ^ (prefixWord ++ tailWord_6249215).sum := by decide
  have hdescent : baseEnd_6249215 < baseStart_6249215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249223 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6249223 : Nat := 118140960795 + 6249223 * 2 ^ 59
def prefixEnd_6249223 : Nat := 4983230072969 + 3 ^ 40 * 6249223 * 2
def baseEnd_6249223 : Nat := 3208855116132108619972853

theorem tailTrace_6249223 : CollatzResearch.WordTrace tailWord_6249223 prefixEnd_6249223 3208855116132108619972853 := by
  unfold tailWord_6249223
  simp only [CollatzResearch.WordTrace]
  refine ⟨227927887839139828162824323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151951925226093218775216215 227927887839139828162824323)
  ·
    refine ⟨341891831758709742244236485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227927887839139828162824323 341891831758709742244236485)
    ·
      refine ⟨64104718454758076670794341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341891831758709742244236485 64104718454758076670794341)
      ·
        refine ⟨12019634710267139375773939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64104718454758076670794341 12019634710267139375773939)
        ·
          refine ⟨18029452065400709063660909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019634710267139375773939 18029452065400709063660909)
          ·
            refine ⟨6761044524525265898872841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18029452065400709063660909 6761044524525265898872841)
            ·
              refine ⟨5070783393393949424154631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6761044524525265898872841 5070783393393949424154631)
              ·
                refine ⟨7606175090090924136231947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070783393393949424154631 7606175090090924136231947)
                ·
                  refine ⟨11409262635136386204347921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606175090090924136231947 11409262635136386204347921)
                  ·
                    refine ⟨8556946976352289653260941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11409262635136386204347921 8556946976352289653260941)
                    ·
                      refine ⟨3208855116132108619972853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8556946976352289653260941 3208855116132108619972853)
                      ·
                        rfl

theorem cell23_6249223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6249223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249223 prefixEnd_6249223 := by exact prefixLift 6249223
  have htrace : WordTrace (prefixWord ++ tailWord_6249223) baseStart_6249223 baseEnd_6249223 := by
    simpa [prefixWord, tailWord_6249223, baseEnd_6249223] using wordTrace_append hprefix tailTrace_6249223
  have hstable : (prefixWord ++ tailWord_6249223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249223).length < 2 ^ (prefixWord ++ tailWord_6249223).sum := by decide
  have hdescent : baseEnd_6249223 < baseStart_6249223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249235 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 4, 6]
def baseStart_6249235 : Nat := 118140960795 + 6249235 * 2 ^ 59
def prefixEnd_6249235 : Nat := 4983230072969 + 3 ^ 40 * 6249235 * 2
def baseEnd_6249235 : Nat := 1069620425966654191007599

theorem tailTrace_6249235 : CollatzResearch.WordTrace tailWord_6249235 prefixEnd_6249235 1069620425966654191007599 := by
  unfold tailWord_6249235
  simp only [CollatzResearch.WordTrace]
  refine ⟨227928325515096354212261159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151952217010064236141507439 227928325515096354212261159)
  ·
    refine ⟨341892488272644531318391739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227928325515096354212261159 341892488272644531318391739)
    ·
      refine ⟨512838732408966796977587609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341892488272644531318391739 512838732408966796977587609)
      ·
        refine ⟨384629049306725097733190707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512838732408966796977587609 384629049306725097733190707)
        ·
          refine ⟨576943573960087646599786061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384629049306725097733190707 576943573960087646599786061)
          ·
            refine ⟨216353840235032867474919773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576943573960087646599786061 216353840235032867474919773)
            ·
              refine ⟨81132690088137325303094915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216353840235032867474919773 81132690088137325303094915)
              ·
                refine ⟨121699035132205987954642373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81132690088137325303094915 121699035132205987954642373)
                ·
                  refine ⟨22818569087288622741495445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121699035132205987954642373 22818569087288622741495445)
                  ·
                    refine ⟨1069620425966654191007599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22818569087288622741495445 1069620425966654191007599)
                    ·
                      rfl

theorem cell23_6249235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_6249235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249235 prefixEnd_6249235 := by exact prefixLift 6249235
  have htrace : WordTrace (prefixWord ++ tailWord_6249235) baseStart_6249235 baseEnd_6249235 := by
    simpa [prefixWord, tailWord_6249235, baseEnd_6249235] using wordTrace_append hprefix tailTrace_6249235
  have hstable : (prefixWord ++ tailWord_6249235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249235).length < 2 ^ (prefixWord ++ tailWord_6249235).sum := by decide
  have hdescent : baseEnd_6249235 < baseStart_6249235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249259 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 6, 2, 2]
def baseStart_6249259 : Nat := 118140960795 + 6249259 * 2 ^ 59
def prefixEnd_6249259 : Nat := 4983230072969 + 3 ^ 40 * 6249259 * 2
def baseEnd_6249259 : Nat := 3208873601435670479122687

theorem tailTrace_6249259 : CollatzResearch.WordTrace tailWord_6249259 prefixEnd_6249259 3208873601435670479122687 := by
  unfold tailWord_6249259
  simp only [CollatzResearch.WordTrace]
  refine ⟨227929200867009406311134831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151952800578006270874089887 227929200867009406311134831)
  ·
    refine ⟨341893801300514109466702247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227929200867009406311134831 341893801300514109466702247)
    ·
      refine ⟨512840701950771164200053371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341893801300514109466702247 512840701950771164200053371)
      ·
        refine ⟨769261052926156746300080057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512840701950771164200053371 769261052926156746300080057)
        ·
          refine ⟨576945789694617559725060043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769261052926156746300080057 576945789694617559725060043)
          ·
            refine ⟨865418684541926339587590065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576945789694617559725060043 865418684541926339587590065)
            ·
              refine ⟨649064013406444754690692549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865418684541926339587590065 649064013406444754690692549)
              ·
                refine ⟨121699502513708391504504853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649064013406444754690692549 121699502513708391504504853)
                ·
                  refine ⟨5704664180330080851773665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121699502513708391504504853 5704664180330080851773665)
                  ·
                    refine ⟨4278498135247560638830249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5704664180330080851773665 4278498135247560638830249)
                    ·
                      refine ⟨3208873601435670479122687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278498135247560638830249 3208873601435670479122687)
                      ·
                        rfl

theorem cell23_6249259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2, 2].length) (baseStart_6249259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249259 prefixEnd_6249259 := by exact prefixLift 6249259
  have htrace : WordTrace (prefixWord ++ tailWord_6249259) baseStart_6249259 baseEnd_6249259 := by
    simpa [prefixWord, tailWord_6249259, baseEnd_6249259] using wordTrace_append hprefix tailTrace_6249259
  have hstable : (prefixWord ++ tailWord_6249259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249259).length < 2 ^ (prefixWord ++ tailWord_6249259).sum := by decide
  have hdescent : baseEnd_6249259 < baseStart_6249259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249295 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 11]
def baseStart_6249295 : Nat := 118140960795 + 6249295 * 2 ^ 59
def prefixEnd_6249295 : Nat := 4983230072969 + 3 ^ 40 * 6249295 * 2
def baseEnd_6249295 : Nat := 1069630695579744112757507

theorem tailTrace_6249295 : CollatzResearch.WordTrace tailWord_6249295 prefixEnd_6249295 1069630695579744112757507 := by
  unfold tailWord_6249295
  simp only [CollatzResearch.WordTrace]
  refine ⟨227930513894878984459445339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151953675929919322972963559 227930513894878984459445339)
  ·
    refine ⟨341895770842318476689168009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227930513894878984459445339 341895770842318476689168009)
    ·
      refine ⟨256421828131738857516876007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341895770842318476689168009 256421828131738857516876007)
      ·
        refine ⟨384632742197608286275314011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256421828131738857516876007 384632742197608286275314011)
        ·
          refine ⟨576949113296412429412971017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384632742197608286275314011 576949113296412429412971017)
          ·
            refine ⟨432711834972309322059728263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576949113296412429412971017 432711834972309322059728263)
            ·
              refine ⟨649067752458463983089592395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432711834972309322059728263 649067752458463983089592395)
              ·
                refine ⟨973601628687695974634388593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649067752458463983089592395 973601628687695974634388593)
                ·
                  refine ⟨730201221515771980975791445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973601628687695974634388593 730201221515771980975791445)
                  ·
                    refine ⟨1069630695579744112757507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 730201221515771980975791445 1069630695579744112757507)
                    ·
                      rfl

theorem cell23_6249295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_6249295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249295 prefixEnd_6249295 := by exact prefixLift 6249295
  have htrace : WordTrace (prefixWord ++ tailWord_6249295) baseStart_6249295 baseEnd_6249295 := by
    simpa [prefixWord, tailWord_6249295, baseEnd_6249295] using wordTrace_append hprefix tailTrace_6249295
  have hstable : (prefixWord ++ tailWord_6249295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249295).length < 2 ^ (prefixWord ++ tailWord_6249295).sum := by decide
  have hdescent : baseEnd_6249295 < baseStart_6249295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249312 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_6249312 : Nat := 118140960795 + 6249312 * 2 ^ 59
def prefixEnd_6249312 : Nat := 4983230072969 + 3 ^ 40 * 6249312 * 2
def baseEnd_6249312 : Nat := 1069633605303452923919981

theorem tailTrace_6249312 : CollatzResearch.WordTrace tailWord_6249312 prefixEnd_6249312 1069633605303452923919981 := by
  unfold tailWord_6249312
  simp only [CollatzResearch.WordTrace]
  refine ⟨113965566967908698181407095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151954089290544930908542793 113965566967908698181407095)
  ·
    refine ⟨170948350451863047272110643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113965566967908698181407095 170948350451863047272110643)
    ·
      refine ⟨256422525677794570908165965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170948350451863047272110643 256422525677794570908165965)
      ·
        refine ⟨96158447129172964090562237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256422525677794570908165965 96158447129172964090562237)
        ·
          refine ⟨36059417673439861533960839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96158447129172964090562237 36059417673439861533960839)
          ·
            refine ⟨54089126510159792300941259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36059417673439861533960839 54089126510159792300941259)
            ·
              refine ⟨81133689765239688451411889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54089126510159792300941259 81133689765239688451411889)
              ·
                refine ⟨60850267323929766338558917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81133689765239688451411889 60850267323929766338558917)
                ·
                  refine ⟨11409425123236831188479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60850267323929766338558917 11409425123236831188479797)
                  ·
                    refine ⟨1069633605303452923919981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11409425123236831188479797 1069633605303452923919981)
                    ·
                      rfl

theorem cell23_6249312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_6249312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249312 prefixEnd_6249312 := by exact prefixLift 6249312
  have htrace : WordTrace (prefixWord ++ tailWord_6249312) baseStart_6249312 baseEnd_6249312 := by
    simpa [prefixWord, tailWord_6249312, baseEnd_6249312] using wordTrace_append hprefix tailTrace_6249312
  have hstable : (prefixWord ++ tailWord_6249312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249312).length < 2 ^ (prefixWord ++ tailWord_6249312).sum := by decide
  have hdescent : baseEnd_6249312 < baseStart_6249312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249329 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_6249329 : Nat := 118140960795 + 6249329 * 2 ^ 59
def prefixEnd_6249329 : Nat := 4983230072969 + 3 ^ 40 * 6249329 * 2
def baseEnd_6249329 : Nat := 1069636515027161735082455

theorem tailTrace_6249329 : CollatzResearch.WordTrace tailWord_6249329 prefixEnd_6249329 1069636515027161735082455 := by
  unfold tailWord_6249329
  simp only [CollatzResearch.WordTrace]
  refine ⟨227931753976755808266183041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151954502651170538844122027 227931753976755808266183041)
  ·
    refine ⟨170948815482566856199637281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227931753976755808266183041 170948815482566856199637281)
    ·
      refine ⟨128211611611925142149727961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170948815482566856199637281 128211611611925142149727961)
      ·
        refine ⟨96158708708943856612295971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128211611611925142149727961 96158708708943856612295971)
        ·
          refine ⟨144238063063415784918443957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96158708708943856612295971 144238063063415784918443957)
          ·
            refine ⟨13522318412195229836104121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144238063063415784918443957 13522318412195229836104121)
            ·
              refine ⟨10141738809146422377078091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13522318412195229836104121 10141738809146422377078091)
              ·
                refine ⟨15212608213719633565617137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10141738809146422377078091 15212608213719633565617137)
                ·
                  refine ⟨11409456160289725174212853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15212608213719633565617137 11409456160289725174212853)
                  ·
                    refine ⟨1069636515027161735082455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11409456160289725174212853 1069636515027161735082455)
                    ·
                      rfl

theorem cell23_6249329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_6249329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249329 prefixEnd_6249329 := by exact prefixLift 6249329
  have htrace : WordTrace (prefixWord ++ tailWord_6249329) baseStart_6249329 baseEnd_6249329 := by
    simpa [prefixWord, tailWord_6249329, baseEnd_6249329] using wordTrace_append hprefix tailTrace_6249329
  have hstable : (prefixWord ++ tailWord_6249329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249329).length < 2 ^ (prefixWord ++ tailWord_6249329).sum := by decide
  have hdescent : baseEnd_6249329 < baseStart_6249329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249349 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_6249349 : Nat := 118140960795 + 6249349 * 2 ^ 59
def prefixEnd_6249349 : Nat := 4983230072969 + 3 ^ 40 * 6249349 * 2
def baseEnd_6249349 : Nat := 3208919814694575126997273

theorem tailTrace_6249349 : CollatzResearch.WordTrace tailWord_6249349 prefixEnd_6249349 3208919814694575126997273 := by
  unfold tailWord_6249349
  simp only [CollatzResearch.WordTrace]
  refine ⟨227932483436683351681911101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151954988957788901121274067 227932483436683351681911101)
  ·
    refine ⟨85474681288756256880716663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227932483436683351681911101 85474681288756256880716663)
    ·
      refine ⟨128212021933134385321074995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85474681288756256880716663 128212021933134385321074995)
      ·
        refine ⟨192318032899701577981612493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128212021933134385321074995 192318032899701577981612493)
        ·
          refine ⟨72119262337388091743104685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192318032899701577981612493 72119262337388091743104685)
          ·
            refine ⟨27044723376520534403664257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72119262337388091743104685 27044723376520534403664257)
            ·
              refine ⟨20283542532390400802748193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27044723376520534403664257 20283542532390400802748193)
              ·
                refine ⟨15212656899292800602061145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20283542532390400802748193 15212656899292800602061145)
                ·
                  refine ⟨11409492674469600451545859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15212656899292800602061145 11409492674469600451545859)
                  ·
                    refine ⟨17114239011704400677318789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11409492674469600451545859 17114239011704400677318789)
                    ·
                      refine ⟨3208919814694575126997273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17114239011704400677318789 3208919814694575126997273)
                      ·
                        rfl

theorem cell23_6249349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_6249349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249349 prefixEnd_6249349 := by exact prefixLift 6249349
  have htrace : WordTrace (prefixWord ++ tailWord_6249349) baseStart_6249349 baseEnd_6249349 := by
    simpa [prefixWord, tailWord_6249349, baseEnd_6249349] using wordTrace_append hprefix tailTrace_6249349
  have hstable : (prefixWord ++ tailWord_6249349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249349).length < 2 ^ (prefixWord ++ tailWord_6249349).sum := by decide
  have hdescent : baseEnd_6249349 < baseStart_6249349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249383 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_6249383 : Nat := 118140960795 + 6249383 * 2 ^ 59
def prefixEnd_6249383 : Nat := 4983230072969 + 3 ^ 40 * 6249383 * 2
def baseEnd_6249383 : Nat := 3208937273036827993972117

theorem tailTrace_6249383 : CollatzResearch.WordTrace tailWord_6249383 prefixEnd_6249383 3208937273036827993972117 := by
  unfold tailWord_6249383
  simp only [CollatzResearch.WordTrace]
  refine ⟨227933723518560175488648803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151955815679040116992432535 227933723518560175488648803)
  ·
    refine ⟨341900585277840263232973205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227933723518560175488648803 341900585277840263232973205)
    ·
      refine ⟨16026589934898762339045619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 341900585277840263232973205 16026589934898762339045619)
      ·
        refine ⟨24039884902348143508568429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16026589934898762339045619 24039884902348143508568429)
        ·
          refine ⟨9014956838380553815713161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24039884902348143508568429 9014956838380553815713161)
          ·
            refine ⟨6761217628785415361784871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014956838380553815713161 6761217628785415361784871)
            ·
              refine ⟨10141826443178123042677307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6761217628785415361784871 10141826443178123042677307)
              ·
                refine ⟨15212739664767184564015961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10141826443178123042677307 15212739664767184564015961)
                ·
                  refine ⟨11409554748575388423011971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15212739664767184564015961 11409554748575388423011971)
                  ·
                    refine ⟨17114332122863082634517957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11409554748575388423011971 17114332122863082634517957)
                    ·
                      refine ⟨3208937273036827993972117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17114332122863082634517957 3208937273036827993972117)
                      ·
                        rfl

theorem cell23_6249383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_6249383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249383 prefixEnd_6249383 := by exact prefixLift 6249383
  have htrace : WordTrace (prefixWord ++ tailWord_6249383) baseStart_6249383 baseEnd_6249383 := by
    simpa [prefixWord, tailWord_6249383, baseEnd_6249383] using wordTrace_append hprefix tailTrace_6249383
  have hstable : (prefixWord ++ tailWord_6249383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249383).length < 2 ^ (prefixWord ++ tailWord_6249383).sum := by decide
  have hdescent : baseEnd_6249383 < baseStart_6249383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249396 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6249396 : Nat := 118140960795 + 6249396 * 2 ^ 59
def prefixEnd_6249396 : Nat := 4983230072969 + 3 ^ 40 * 6249396 * 2
def baseEnd_6249396 : Nat := 3208943948285336443109557

theorem tailTrace_6249396 : CollatzResearch.WordTrace tailWord_6249396 prefixEnd_6249396 3208943948285336443109557 := by
  unfold tailWord_6249396
  simp only [CollatzResearch.WordTrace]
  refine ⟨113967098833756539354436021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151956131778342052472581361 113967098833756539354436021)
  ·
    refine ⟨10684415515664675564478377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113967098833756539354436021 10684415515664675564478377)
    ·
      refine ⟨8013311636748506673358783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10684415515664675564478377 8013311636748506673358783)
      ·
        refine ⟨12019967455122760010038175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8013311636748506673358783 12019967455122760010038175)
        ·
          refine ⟨18029951182684140015057263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019967455122760010038175 18029951182684140015057263)
          ·
            refine ⟨27044926774026210022585895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029951182684140015057263 27044926774026210022585895)
            ·
              refine ⟨40567390161039315033878843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27044926774026210022585895 40567390161039315033878843)
              ·
                refine ⟨60851085241558972550818265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40567390161039315033878843 60851085241558972550818265)
                ·
                  refine ⟨45638313931169229413113699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60851085241558972550818265 45638313931169229413113699)
                  ·
                    refine ⟨68457470896753844119670549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45638313931169229413113699 68457470896753844119670549)
                    ·
                      refine ⟨3208943948285336443109557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68457470896753844119670549 3208943948285336443109557)
                      ·
                        rfl

theorem cell23_6249396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6249396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249396 prefixEnd_6249396 := by exact prefixLift 6249396
  have htrace : WordTrace (prefixWord ++ tailWord_6249396) baseStart_6249396 baseEnd_6249396 := by
    simpa [prefixWord, tailWord_6249396, baseEnd_6249396] using wordTrace_append hprefix tailTrace_6249396
  have hstable : (prefixWord ++ tailWord_6249396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249396).length < 2 ^ (prefixWord ++ tailWord_6249396).sum := by decide
  have hdescent : baseEnd_6249396 < baseStart_6249396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249450 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_6249450 : Nat := 118140960795 + 6249450 * 2 ^ 59
def prefixEnd_6249450 : Nat := 4983230072969 + 3 ^ 40 * 6249450 * 2
def baseEnd_6249450 : Nat := 3208971676240679231834309

theorem tailTrace_6249450 : CollatzResearch.WordTrace tailWord_6249450 prefixEnd_6249450 3208971676240679231834309 := by
  unfold tailWord_6249450
  simp only [CollatzResearch.WordTrace]
  refine ⟨56984041802329361482834451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151957444806211630620891869 56984041802329361482834451)
  ·
    refine ⟨85476062703494042224251677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56984041802329361482834451 85476062703494042224251677)
    ·
      refine ⟨32053523513810265834094379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85476062703494042224251677 32053523513810265834094379)
      ·
        refine ⟨48080285270715398751141569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32053523513810265834094379 48080285270715398751141569)
        ·
          refine ⟨36060213953036549063356177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48080285270715398751141569 36060213953036549063356177)
          ·
            refine ⟨27045160464777411797517133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36060213953036549063356177 27045160464777411797517133)
            ·
              refine ⟨10141935174291529424068925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27045160464777411797517133 10141935174291529424068925)
              ·
                refine ⟨3803225690359323534025847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10141935174291529424068925 3803225690359323534025847)
                ·
                  refine ⟨5704838535538985301038771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803225690359323534025847 5704838535538985301038771)
                  ·
                    refine ⟨8557257803308477951558157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5704838535538985301038771 8557257803308477951558157)
                    ·
                      refine ⟨3208971676240679231834309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557257803308477951558157 3208971676240679231834309)
                      ·
                        rfl

theorem cell23_6249450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_6249450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249450 prefixEnd_6249450 := by exact prefixLift 6249450
  have htrace : WordTrace (prefixWord ++ tailWord_6249450) baseStart_6249450 baseEnd_6249450 := by
    simpa [prefixWord, tailWord_6249450, baseEnd_6249450] using wordTrace_append hprefix tailTrace_6249450
  have hstable : (prefixWord ++ tailWord_6249450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249450).length < 2 ^ (prefixWord ++ tailWord_6249450).sum := by decide
  have hdescent : baseEnd_6249450 < baseStart_6249450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249459 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3]
def baseStart_6249459 : Nat := 118140960795 + 6249459 * 2 ^ 59
def prefixEnd_6249459 : Nat := 4983230072969 + 3 ^ 40 * 6249459 * 2
def baseEnd_6249459 : Nat := 3208976297566569696621767

theorem tailTrace_6249459 : CollatzResearch.WordTrace tailWord_6249459 prefixEnd_6249459 3208976297566569696621767 := by
  unfold tailWord_6249459
  simp only [CollatzResearch.WordTrace]
  refine ⟨227936495466284840468415431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151957663644189893645610287 227936495466284840468415431)
  ·
    refine ⟨341904743199427260702623147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227936495466284840468415431 341904743199427260702623147)
    ·
      refine ⟨512857114799140891053934721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341904743199427260702623147 512857114799140891053934721)
      ·
        refine ⟨384642836099355668290451041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512857114799140891053934721 384642836099355668290451041)
        ·
          refine ⟨288482127074516751217838281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384642836099355668290451041 288482127074516751217838281)
          ·
            refine ⟨216361595305887563413378711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288482127074516751217838281 216361595305887563413378711)
            ·
              refine ⟨324542392958831345120068067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216361595305887563413378711 324542392958831345120068067)
              ·
                refine ⟨486813589438247017680102101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324542392958831345120068067 486813589438247017680102101)
                ·
                  refine ⟨11409693502458914476877393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 486813589438247017680102101 11409693502458914476877393)
                  ·
                    refine ⟨8557270126844185857658045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11409693502458914476877393 8557270126844185857658045)
                    ·
                      refine ⟨3208976297566569696621767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557270126844185857658045 3208976297566569696621767)
                      ·
                        rfl

theorem cell23_6249459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_6249459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249459 prefixEnd_6249459 := by exact prefixLift 6249459
  have htrace : WordTrace (prefixWord ++ tailWord_6249459) baseStart_6249459 baseEnd_6249459 := by
    simpa [prefixWord, tailWord_6249459, baseEnd_6249459] using wordTrace_append hprefix tailTrace_6249459
  have hstable : (prefixWord ++ tailWord_6249459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249459).length < 2 ^ (prefixWord ++ tailWord_6249459).sum := by decide
  have hdescent : baseEnd_6249459 < baseStart_6249459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249479 : List Nat := [1, 1, 4, 3, 1, 1, 4, 8]
def baseStart_6249479 : Nat := 118140960795 + 6249479 * 2 ^ 59
def prefixEnd_6249479 : Nat := 4983230072969 + 3 ^ 40 * 6249479 * 2
def baseEnd_6249479 : Nat := 118851354339987393273025

theorem tailTrace_6249479 : CollatzResearch.WordTrace tailWord_6249479 prefixEnd_6249479 118851354339987393273025 := by
  unfold tailWord_6249479
  simp only [CollatzResearch.WordTrace]
  refine ⟨227937224926212383884143491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151958149950808255922762327 227937224926212383884143491)
  ·
    refine ⟨341905837389318575826215237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227937224926212383884143491 341905837389318575826215237)
    ·
      refine ⟨64107344510497232967415357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341905837389318575826215237 64107344510497232967415357)
      ·
        refine ⟨24040254191436462362780759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64107344510497232967415357 24040254191436462362780759)
        ·
          refine ⟨36060381287154693544171139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24040254191436462362780759 36060381287154693544171139)
          ·
            refine ⟨54090571930732040316256709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36060381287154693544171139 54090571930732040316256709)
            ·
              refine ⟨10141982237012257559298133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54090571930732040316256709 10141982237012257559298133)
              ·
                refine ⟨118851354339987393273025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10141982237012257559298133 118851354339987393273025)
                ·
                  rfl

theorem cell23_6249479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 8].length) (baseStart_6249479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249479 prefixEnd_6249479 := by exact prefixLift 6249479
  have htrace : WordTrace (prefixWord ++ tailWord_6249479) baseStart_6249479 baseEnd_6249479 := by
    simpa [prefixWord, tailWord_6249479, baseEnd_6249479] using wordTrace_append hprefix tailTrace_6249479
  have hstable : (prefixWord ++ tailWord_6249479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249479).length < 2 ^ (prefixWord ++ tailWord_6249479).sum := by decide
  have hdescent : baseEnd_6249479 < baseStart_6249479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249483 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 2, 4]
def baseStart_6249483 : Nat := 118140960795 + 6249483 * 2 ^ 59
def prefixEnd_6249483 : Nat := 4983230072969 + 3 ^ 40 * 6249483 * 2
def baseEnd_6249483 : Nat := 1069662873700759200907219

theorem tailTrace_6249483 : CollatzResearch.WordTrace tailWord_6249483 prefixEnd_6249483 1069662873700759200907219 := by
  unfold tailWord_6249483
  simp only [CollatzResearch.WordTrace]
  refine ⟨227937370818197892567289103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151958247212131928378192735 227937370818197892567289103)
  ·
    refine ⟨341906056227296838850933655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227937370818197892567289103 341906056227296838850933655)
    ·
      refine ⟨512859084340945258276400483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341906056227296838850933655 512859084340945258276400483)
      ·
        refine ⟨769288626511417887414600725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512859084340945258276400483 769288626511417887414600725)
        ·
          refine ⟨36060404367722713472559409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 769288626511417887414600725 36060404367722713472559409)
          ·
            refine ⟨27045303275792035104419557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36060404367722713472559409 27045303275792035104419557)
            ·
              refine ⟨5070994364211006582078667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27045303275792035104419557 5070994364211006582078667)
              ·
                refine ⟨7606491546316509873118001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070994364211006582078667 7606491546316509873118001)
                ·
                  refine ⟨5704868659737382404838501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606491546316509873118001 5704868659737382404838501)
                  ·
                    refine ⟨1069662873700759200907219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704868659737382404838501 1069662873700759200907219)
                    ·
                      rfl

theorem cell23_6249483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 4].length) (baseStart_6249483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249483 prefixEnd_6249483 := by exact prefixLift 6249483
  have htrace : WordTrace (prefixWord ++ tailWord_6249483) baseStart_6249483 baseEnd_6249483 := by
    simpa [prefixWord, tailWord_6249483, baseEnd_6249483] using wordTrace_append hprefix tailTrace_6249483
  have hstable : (prefixWord ++ tailWord_6249483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249483).length < 2 ^ (prefixWord ++ tailWord_6249483).sum := by decide
  have hdescent : baseEnd_6249483 < baseStart_6249483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249489 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_6249489 : Nat := 118140960795 + 6249489 * 2 ^ 59
def prefixEnd_6249489 : Nat := 4983230072969 + 3 ^ 40 * 6249489 * 2
def baseEnd_6249489 : Nat := 3208991701986204579246629

theorem tailTrace_6249489 : CollatzResearch.WordTrace tailWord_6249489 prefixEnd_6249489 3208991701986204579246629 := by
  unfold tailWord_6249489
  simp only [CollatzResearch.WordTrace]
  refine ⟨227937589656176155592007521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151958393104117437061338347 227937589656176155592007521)
  ·
    refine ⟨170953192242132116694005641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227937589656176155592007521 170953192242132116694005641)
    ·
      refine ⟨128214894181599087520504231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170953192242132116694005641 128214894181599087520504231)
      ·
        refine ⟨192322341272398631280756347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128214894181599087520504231 192322341272398631280756347)
        ·
          refine ⟨288483511908597946921134521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192322341272398631280756347 288483511908597946921134521)
          ·
            refine ⟨216362633931448460190850891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288483511908597946921134521 216362633931448460190850891)
            ·
              refine ⟨324543950897172690286276337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216362633931448460190850891 324543950897172690286276337)
              ·
                refine ⟨243407963172879517714707253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324543950897172690286276337 243407963172879517714707253)
                ·
                  refine ⟨22819496547457454785753805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243407963172879517714707253 22819496547457454785753805)
                  ·
                    refine ⟨8557311205296545544657677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22819496547457454785753805 8557311205296545544657677)
                    ·
                      refine ⟨3208991701986204579246629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557311205296545544657677 3208991701986204579246629)
                      ·
                        rfl

theorem cell23_6249489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_6249489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249489 prefixEnd_6249489 := by exact prefixLift 6249489
  have htrace : WordTrace (prefixWord ++ tailWord_6249489) baseStart_6249489 baseEnd_6249489 := by
    simpa [prefixWord, tailWord_6249489, baseEnd_6249489] using wordTrace_append hprefix tailTrace_6249489
  have hstable : (prefixWord ++ tailWord_6249489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249489).length < 2 ^ (prefixWord ++ tailWord_6249489).sum := by decide
  have hdescent : baseEnd_6249489 < baseStart_6249489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249493 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_6249493 : Nat := 118140960795 + 6249493 * 2 ^ 59
def prefixEnd_6249493 : Nat := 4983230072969 + 3 ^ 40 * 6249493 * 2
def baseEnd_6249493 : Nat := 3208993755908822563596611

theorem tailTrace_6249493 : CollatzResearch.WordTrace tailWord_6249493 prefixEnd_6249493 3208993755908822563596611 := by
  unfold tailWord_6249493
  simp only [CollatzResearch.WordTrace]
  refine ⟨227937735548161664275153133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151958490365441109516768755 227937735548161664275153133)
  ·
    refine ⟨85476650830560624103182425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227937735548161664275153133 85476650830560624103182425)
    ·
      refine ⟨64107488122920468077386819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85476650830560624103182425 64107488122920468077386819)
      ·
        refine ⟨96161232184380702116080229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64107488122920468077386819 96161232184380702116080229)
        ·
          refine ⟨18030231034571381646765043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96161232184380702116080229 18030231034571381646765043)
          ·
            refine ⟨27045346551857072470147565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18030231034571381646765043 27045346551857072470147565)
            ·
              refine ⟨10142004956946402176305337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27045346551857072470147565 10142004956946402176305337)
              ·
                refine ⟨7606503717709801632229003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10142004956946402176305337 7606503717709801632229003)
                ·
                  refine ⟨11409755576564702448343505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606503717709801632229003 11409755576564702448343505)
                  ·
                    refine ⟨8557316682423526836257629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11409755576564702448343505 8557316682423526836257629)
                    ·
                      refine ⟨3208993755908822563596611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557316682423526836257629 3208993755908822563596611)
                      ·
                        rfl

theorem cell23_6249493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_6249493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249493 prefixEnd_6249493 := by exact prefixLift 6249493
  have htrace : WordTrace (prefixWord ++ tailWord_6249493) baseStart_6249493 baseEnd_6249493 := by
    simpa [prefixWord, tailWord_6249493, baseEnd_6249493] using wordTrace_append hprefix tailTrace_6249493
  have hstable : (prefixWord ++ tailWord_6249493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249493).length < 2 ^ (prefixWord ++ tailWord_6249493).sum := by decide
  have hdescent : baseEnd_6249493 < baseStart_6249493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249506 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6249506 : Nat := 118140960795 + 6249506 * 2 ^ 59
def prefixEnd_6249506 : Nat := 4983230072969 + 3 ^ 40 * 6249506 * 2
def baseEnd_6249506 : Nat := 3209000431157331012734051

theorem tailTrace_6249506 : CollatzResearch.WordTrace tailWord_6249506 prefixEnd_6249506 3209000431157331012734051 := by
  unfold tailWord_6249506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56984552424278641873844093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151958806464743044996917581 56984552424278641873844093)
  ·
    refine ⟨21369207159104490702691535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56984552424278641873844093 21369207159104490702691535)
    ·
      refine ⟨32053810738656736054037303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21369207159104490702691535 32053810738656736054037303)
      ·
        refine ⟨48080716107985104081055955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32053810738656736054037303 48080716107985104081055955)
        ·
          refine ⟨72121074161977656121583933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48080716107985104081055955 72121074161977656121583933)
          ·
            refine ⟨27045402810741621045593975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72121074161977656121583933 27045402810741621045593975)
            ·
              refine ⟨40568104216112431568390963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27045402810741621045593975 40568104216112431568390963)
              ·
                refine ⟨60852156324168647352586445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40568104216112431568390963 60852156324168647352586445)
                ·
                  refine ⟨22819558621563242757219917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60852156324168647352586445 22819558621563242757219917)
                  ·
                    refine ⟨8557334483086216033957469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22819558621563242757219917 8557334483086216033957469)
                    ·
                      refine ⟨3209000431157331012734051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557334483086216033957469 3209000431157331012734051)
                      ·
                        rfl

theorem cell23_6249506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6249506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249506 prefixEnd_6249506 := by exact prefixLift 6249506
  have htrace : WordTrace (prefixWord ++ tailWord_6249506) baseStart_6249506 baseEnd_6249506 := by
    simpa [prefixWord, tailWord_6249506, baseEnd_6249506] using wordTrace_append hprefix tailTrace_6249506
  have hstable : (prefixWord ++ tailWord_6249506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249506).length < 2 ^ (prefixWord ++ tailWord_6249506).sum := by decide
  have hdescent : baseEnd_6249506 < baseStart_6249506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249524 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6249524 : Nat := 118140960795 + 6249524 * 2 ^ 59
def prefixEnd_6249524 : Nat := 4983230072969 + 3 ^ 40 * 6249524 * 2
def baseEnd_6249524 : Nat := 3209009673809111942308969

theorem tailTrace_6249524 : CollatzResearch.WordTrace tailWord_6249524 prefixEnd_6249524 3209009673809111942308969 := by
  unfold tailWord_6249524
  simp only [CollatzResearch.WordTrace]
  refine ⟨113969433105524678284765813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151959244140699571046354417 113969433105524678284765813)
  ·
    refine ⟨10684634353642938589196795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113969433105524678284765813 10684634353642938589196795)
    ·
      refine ⟨16026951530464407883795193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10684634353642938589196795 16026951530464407883795193)
      ·
        refine ⟨12020213647848305912846395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16026951530464407883795193 12020213647848305912846395)
        ·
          refine ⟨18030320471772458869269593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12020213647848305912846395 18030320471772458869269593)
          ·
            refine ⟨13522740353829344151952195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18030320471772458869269593 13522740353829344151952195)
            ·
              refine ⟨20284110530744016227928293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522740353829344151952195 20284110530744016227928293)
              ·
                refine ⟨3803270724514503042736555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20284110530744016227928293 3803270724514503042736555)
                ·
                  refine ⟨5704906086771754564104833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803270724514503042736555 5704906086771754564104833)
                  ·
                    refine ⟨4278679565078815923078625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5704906086771754564104833 4278679565078815923078625)
                    ·
                      refine ⟨3209009673809111942308969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278679565078815923078625 3209009673809111942308969)
                      ·
                        rfl

theorem cell23_6249524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6249524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249524 prefixEnd_6249524 := by exact prefixLift 6249524
  have htrace : WordTrace (prefixWord ++ tailWord_6249524) baseStart_6249524 baseEnd_6249524 := by
    simpa [prefixWord, tailWord_6249524, baseEnd_6249524] using wordTrace_append hprefix tailTrace_6249524
  have hstable : (prefixWord ++ tailWord_6249524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249524).length < 2 ^ (prefixWord ++ tailWord_6249524).sum := by decide
  have hdescent : baseEnd_6249524 < baseStart_6249524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249526 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6249526 : Nat := 118140960795 + 6249526 * 2 ^ 59
def prefixEnd_6249526 : Nat := 4983230072969 + 3 ^ 40 * 6249526 * 2
def baseEnd_6249526 : Nat := 1069670233590140311494653

theorem tailTrace_6249526 : CollatzResearch.WordTrace tailWord_6249526 prefixEnd_6249526 1069670233590140311494653 := by
  unfold tailWord_6249526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246183697315131931944027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151959292771361407274069621 14246183697315131931944027)
  ·
    refine ⟨21369275545972697897916041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14246183697315131931944027 21369275545972697897916041)
    ·
      refine ⟨16026956659479523423437031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21369275545972697897916041 16026956659479523423437031)
      ·
        refine ⟨24040434989219285135155547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16026956659479523423437031 24040434989219285135155547)
        ·
          refine ⟨36060652483828927702733321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24040434989219285135155547 36060652483828927702733321)
          ·
            refine ⟨27045489362871695777049991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36060652483828927702733321 27045489362871695777049991)
            ·
              refine ⟨40568234044307543665574987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27045489362871695777049991 40568234044307543665574987)
              ·
                refine ⟨60852351066461315498362481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40568234044307543665574987 60852351066461315498362481)
                ·
                  refine ⟨45639263299845986623771861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60852351066461315498362481 45639263299845986623771861)
                  ·
                    refine ⟨1069670233590140311494653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45639263299845986623771861 1069670233590140311494653)
                    ·
                      rfl

theorem cell23_6249526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6249526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249526 prefixEnd_6249526 := by exact prefixLift 6249526
  have htrace : WordTrace (prefixWord ++ tailWord_6249526) baseStart_6249526 baseEnd_6249526 := by
    simpa [prefixWord, tailWord_6249526, baseEnd_6249526] using wordTrace_append hprefix tailTrace_6249526
  have hstable : (prefixWord ++ tailWord_6249526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249526).length < 2 ^ (prefixWord ++ tailWord_6249526).sum := by decide
  have hdescent : baseEnd_6249526 < baseStart_6249526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249533 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_6249533 : Nat := 118140960795 + 6249533 * 2 ^ 59
def prefixEnd_6249533 : Nat := 4983230072969 + 3 ^ 40 * 6249533 * 2
def baseEnd_6249533 : Nat := 3209014295135002407096427

theorem tailTrace_6249533 : CollatzResearch.WordTrace tailWord_6249533 prefixEnd_6249533 3209014295135002407096427 := by
  unfold tailWord_6249533
  simp only [CollatzResearch.WordTrace]
  refine ⟨227939194468016751106609253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151959462978677834071072835 227939194468016751106609253)
  ·
    refine ⟨42738598962753140832489235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227939194468016751106609253 42738598962753140832489235)
    ·
      refine ⟨64107898444129711248733853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42738598962753140832489235 64107898444129711248733853)
      ·
        refine ⟨24040461916548641718275195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64107898444129711248733853 24040461916548641718275195)
        ·
          refine ⟨36060692874822962577412793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24040461916548641718275195 36060692874822962577412793)
          ·
            refine ⟨27045519656117221933059595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36060692874822962577412793 27045519656117221933059595)
            ·
              refine ⟨40568279484175832899589393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27045519656117221933059595 40568279484175832899589393)
              ·
                refine ⟨30426209613131874674692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40568279484175832899589393 30426209613131874674692045)
                ·
                  refine ⟨11409828604924453003009517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30426209613131874674692045 11409828604924453003009517)
                  ·
                    refine ⟨4278685726846669876128569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11409828604924453003009517 4278685726846669876128569)
                    ·
                      refine ⟨3209014295135002407096427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278685726846669876128569 3209014295135002407096427)
                      ·
                        rfl

theorem cell23_6249533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_6249533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249533 prefixEnd_6249533 := by exact prefixLift 6249533
  have htrace : WordTrace (prefixWord ++ tailWord_6249533) baseStart_6249533 baseEnd_6249533 := by
    simpa [prefixWord, tailWord_6249533, baseEnd_6249533] using wordTrace_append hprefix tailTrace_6249533
  have hstable : (prefixWord ++ tailWord_6249533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249533).length < 2 ^ (prefixWord ++ tailWord_6249533).sum := by decide
  have hdescent : baseEnd_6249533 < baseStart_6249533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249539 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 2, 6]
def baseStart_6249539 : Nat := 118140960795 + 6249539 * 2 ^ 59
def prefixEnd_6249539 : Nat := 4983230072969 + 3 ^ 40 * 6249539 * 2
def baseEnd_6249539 : Nat := 1069672458672976461207133

theorem tailTrace_6249539 : CollatzResearch.WordTrace tailWord_6249539 prefixEnd_6249539 1069672458672976461207133 := by
  unfold tailWord_6249539
  simp only [CollatzResearch.WordTrace]
  refine ⟨227939413305995014131327671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151959608870663342754218447 227939413305995014131327671)
  ·
    refine ⟨341909119958992521196991507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227939413305995014131327671 341909119958992521196991507)
    ·
      refine ⟨512863679938488781795487261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341909119958992521196991507 512863679938488781795487261)
      ·
        refine ⟨192323879976933293173307723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512863679938488781795487261 192323879976933293173307723)
        ·
          refine ⟨288485819965399939759961585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192323879976933293173307723 288485819965399939759961585)
          ·
            refine ⟨216364364974049954819971189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288485819965399939759961585 216364364974049954819971189)
            ·
              refine ⟨20284159216317183264372299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216364364974049954819971189 20284159216317183264372299)
              ·
                refine ⟨30426238824475774896558449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20284159216317183264372299 30426238824475774896558449)
                ·
                  refine ⟨22819679118356831172418837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30426238824475774896558449 22819679118356831172418837)
                  ·
                    refine ⟨1069672458672976461207133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22819679118356831172418837 1069672458672976461207133)
                    ·
                      rfl

theorem cell23_6249539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_6249539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249539 prefixEnd_6249539 := by exact prefixLift 6249539
  have htrace : WordTrace (prefixWord ++ tailWord_6249539) baseStart_6249539 baseEnd_6249539 := by
    simpa [prefixWord, tailWord_6249539, baseEnd_6249539] using wordTrace_append hprefix tailTrace_6249539
  have hstable : (prefixWord ++ tailWord_6249539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249539).length < 2 ^ (prefixWord ++ tailWord_6249539).sum := by decide
  have hdescent : baseEnd_6249539 < baseStart_6249539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249559 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_6249559 : Nat := 118140960795 + 6249559 * 2 ^ 59
def prefixEnd_6249559 : Nat := 4983230072969 + 3 ^ 40 * 6249559 * 2
def baseEnd_6249559 : Nat := 3209027645632019305371307

theorem tailTrace_6249559 : CollatzResearch.WordTrace tailWord_6249559 prefixEnd_6249559 3209027645632019305371307 := by
  unfold tailWord_6249559
  simp only [CollatzResearch.WordTrace]
  refine ⟨227940142765922557547055731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151960095177281705031370487 227940142765922557547055731)
  ·
    refine ⟨341910214148883836320583597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227940142765922557547055731 341910214148883836320583597)
    ·
      refine ⟨128216330305831438620218849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341910214148883836320583597 128216330305831438620218849)
      ·
        refine ⟨96162247729373578965164137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128216330305831438620218849 96162247729373578965164137)
        ·
          refine ⟨72121685797030184223873103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96162247729373578965164137 72121685797030184223873103)
          ·
            refine ⟨108182528695545276335809655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72121685797030184223873103 108182528695545276335809655)
            ·
              refine ⟨162273793043317914503714483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108182528695545276335809655 162273793043317914503714483)
              ·
                refine ⟨243410689564976871755571725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162273793043317914503714483 243410689564976871755571725)
                ·
                  refine ⟨91279008586866326908339397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243410689564976871755571725 91279008586866326908339397)
                  ·
                    refine ⟨17114814110037436295313637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91279008586866326908339397 17114814110037436295313637)
                    ·
                      refine ⟨3209027645632019305371307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17114814110037436295313637 3209027645632019305371307)
                      ·
                        rfl

theorem cell23_6249559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_6249559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249559 prefixEnd_6249559 := by exact prefixLift 6249559
  have htrace : WordTrace (prefixWord ++ tailWord_6249559) baseStart_6249559 baseEnd_6249559 := by
    simpa [prefixWord, tailWord_6249559, baseEnd_6249559] using wordTrace_append hprefix tailTrace_6249559
  have hstable : (prefixWord ++ tailWord_6249559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249559).length < 2 ^ (prefixWord ++ tailWord_6249559).sum := by decide
  have hdescent : baseEnd_6249559 < baseStart_6249559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249586 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_6249586 : Nat := 118140960795 + 6249586 * 2 ^ 59
def prefixEnd_6249586 : Nat := 4983230072969 + 3 ^ 40 * 6249586 * 2
def baseEnd_6249586 : Nat := 356560167734410077748187

theorem tailTrace_6249586 : CollatzResearch.WordTrace tailWord_6249586 prefixEnd_6249586 356560167734410077748187 := by
  unfold tailWord_6249586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56985281884206185289572153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151960751691216494105525741 56985281884206185289572153)
  ·
    refine ⟨42738961413154638967179115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56985281884206185289572153 42738961413154638967179115)
    ·
      refine ⟨64108442119731958450768673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42738961413154638967179115 64108442119731958450768673)
      ·
        refine ⟨48081331589798968838076505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64108442119731958450768673 48081331589798968838076505)
        ·
          refine ⟨36060998692349226628557379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48081331589798968838076505 36060998692349226628557379)
          ·
            refine ⟨54091498038523839942836069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36060998692349226628557379 54091498038523839942836069)
            ·
              refine ⟨10142155882223219989281763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54091498038523839942836069 10142155882223219989281763)
              ·
                refine ⟨15213233823334829983922645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10142155882223219989281763 15213233823334829983922645)
                ·
                  refine ⟨356560167734410077748187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15213233823334829983922645 356560167734410077748187)
                  ·
                    rfl

theorem cell23_6249586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_6249586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249586 prefixEnd_6249586 := by exact prefixLift 6249586
  have htrace : WordTrace (prefixWord ++ tailWord_6249586) baseStart_6249586 baseEnd_6249586 := by
    simpa [prefixWord, tailWord_6249586, baseEnd_6249586] using wordTrace_append hprefix tailTrace_6249586
  have hstable : (prefixWord ++ tailWord_6249586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249586).length < 2 ^ (prefixWord ++ tailWord_6249586).sum := by decide
  have hdescent : baseEnd_6249586 < baseStart_6249586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249596 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_6249596 : Nat := 118140960795 + 6249596 * 2 ^ 59
def prefixEnd_6249596 : Nat := 4983230072969 + 3 ^ 40 * 6249596 * 2
def baseEnd_6249596 : Nat := 3209046644416235660608637

theorem tailTrace_6249596 : CollatzResearch.WordTrace tailWord_6249596 prefixEnd_6249596 3209046644416235660608637 := by
  unfold tailWord_6249596
  simp only [CollatzResearch.WordTrace]
  refine ⟨113970746133394256433076321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151960994844525675244101761 113970746133394256433076321)
  ·
    refine ⟨85478059600045692324807241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113970746133394256433076321 85478059600045692324807241)
    ·
      refine ⟨64108544700034269243605431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85478059600045692324807241 64108544700034269243605431)
      ·
        refine ⟨96162817050051403865408147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64108544700034269243605431 96162817050051403865408147)
        ·
          refine ⟨144244225575077105798112221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96162817050051403865408147 144244225575077105798112221)
          ·
            refine ⟨54091584590653914674292083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144244225575077105798112221 54091584590653914674292083)
            ·
              refine ⟨81137376885980872011438125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54091584590653914674292083 81137376885980872011438125)
              ·
                refine ⟨30426516332242827004289297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81137376885980872011438125 30426516332242827004289297)
                ·
                  refine ⟨22819887249182120253216973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30426516332242827004289297 22819887249182120253216973)
                  ·
                    refine ⟨8557457718443295094956365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22819887249182120253216973 8557457718443295094956365)
                    ·
                      refine ⟨3209046644416235660608637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557457718443295094956365 3209046644416235660608637)
                      ·
                        rfl

theorem cell23_6249596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_6249596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249596 prefixEnd_6249596 := by exact prefixLift 6249596
  have htrace : WordTrace (prefixWord ++ tailWord_6249596) baseStart_6249596 baseEnd_6249596 := by
    simpa [prefixWord, tailWord_6249596, baseEnd_6249596] using wordTrace_append hprefix tailTrace_6249596
  have hstable : (prefixWord ++ tailWord_6249596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249596).length < 2 ^ (prefixWord ++ tailWord_6249596).sum := by decide
  have hdescent : baseEnd_6249596 < baseStart_6249596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249597 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_6249597 : Nat := 118140960795 + 6249597 * 2 ^ 59
def prefixEnd_6249597 : Nat := 4983230072969 + 3 ^ 40 * 6249597 * 2
def baseEnd_6249597 : Nat := 3209047157896890156696133

theorem tailTrace_6249597 : CollatzResearch.WordTrace tailWord_6249597 prefixEnd_6249597 3209047157896890156696133 := by
  unfold tailWord_6249597
  simp only [CollatzResearch.WordTrace]
  refine ⟨227941528739784890036939045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151961019159856593357959363 227941528739784890036939045)
  ·
    refine ⟨42739036638709666881926071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227941528739784890036939045 42739036638709666881926071)
    ·
      refine ⟨64108554958064500322889107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42739036638709666881926071 64108554958064500322889107)
      ·
        refine ⟨96162832437096750484333661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64108554958064500322889107 96162832437096750484333661)
        ·
          refine ⟨36061062163911281431625123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96162832437096750484333661 36061062163911281431625123)
          ·
            refine ⟨54091593245866922147437685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36061062163911281431625123 54091593245866922147437685)
            ·
              refine ⟨5071086866800023951322283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54091593245866922147437685 5071086866800023951322283)
              ·
                refine ⟨7606630300200035926983425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071086866800023951322283 7606630300200035926983425)
                ·
                  refine ⟨5704972725150026945237569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606630300200035926983425 5704972725150026945237569)
                  ·
                    refine ⟨4278729543862520208928177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5704972725150026945237569 4278729543862520208928177)
                    ·
                      refine ⟨3209047157896890156696133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278729543862520208928177 3209047157896890156696133)
                      ·
                        rfl

theorem cell23_6249597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_6249597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249597 prefixEnd_6249597 := by exact prefixLift 6249597
  have htrace : WordTrace (prefixWord ++ tailWord_6249597) baseStart_6249597 baseEnd_6249597 := by
    simpa [prefixWord, tailWord_6249597, baseEnd_6249597] using wordTrace_append hprefix tailTrace_6249597
  have hstable : (prefixWord ++ tailWord_6249597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249597).length < 2 ^ (prefixWord ++ tailWord_6249597).sum := by decide
  have hdescent : baseEnd_6249597 < baseStart_6249597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249656 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_6249656 : Nat := 118140960795 + 6249656 * 2 ^ 59
def prefixEnd_6249656 : Nat := 4983230072969 + 3 ^ 40 * 6249656 * 2
def baseEnd_6249656 : Nat := 3209077453255505425858361

theorem tailTrace_6249656 : CollatzResearch.WordTrace tailWord_6249656 prefixEnd_6249656 3209077453255505425858361 := by
  unfold tailWord_6249656
  simp only [CollatzResearch.WordTrace]
  refine ⟨113971840323285571556668411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151962453764380762075557881 113971840323285571556668411)
  ·
    refine ⟨170957760484928357335002617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113971840323285571556668411 170957760484928357335002617)
    ·
      refine ⟨128218320363696268001251963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170957760484928357335002617 128218320363696268001251963)
      ·
        refine ⟨192327480545544402001877945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128218320363696268001251963 192327480545544402001877945)
        ·
          refine ⟨144245610409158301501408459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192327480545544402001877945 144245610409158301501408459)
          ·
            refine ⟨216368415613737452252112689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144245610409158301501408459 216368415613737452252112689)
            ·
              refine ⟨162276311710303089189084517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216368415613737452252112689 162276311710303089189084517)
              ·
                refine ⟨30426808445681829222953347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162276311710303089189084517 30426808445681829222953347)
                ·
                  refine ⟨45640212668522743834430021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30426808445681829222953347 45640212668522743834430021)
                  ·
                    refine ⟨8557539875348014468955629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45640212668522743834430021 8557539875348014468955629)
                    ·
                      refine ⟨3209077453255505425858361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557539875348014468955629 3209077453255505425858361)
                      ·
                        rfl

theorem cell23_6249656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_6249656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249656 prefixEnd_6249656 := by exact prefixLift 6249656
  have htrace : WordTrace (prefixWord ++ tailWord_6249656) baseStart_6249656 baseEnd_6249656 := by
    simpa [prefixWord, tailWord_6249656, baseEnd_6249656] using wordTrace_append hprefix tailTrace_6249656
  have hstable : (prefixWord ++ tailWord_6249656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249656).length < 2 ^ (prefixWord ++ tailWord_6249656).sum := by decide
  have hdescent : baseEnd_6249656 < baseStart_6249656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249659 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 10]
def baseStart_6249659 : Nat := 118140960795 + 6249659 * 2 ^ 59
def prefixEnd_6249659 : Nat := 4983230072969 + 3 ^ 40 * 6249659 * 2
def baseEnd_6249659 : Nat := 356564332633052101568983

theorem tailTrace_6249659 : CollatzResearch.WordTrace tailWord_6249659 prefixEnd_6249659 356564332633052101568983 := by
  unfold tailWord_6249659
  simp only [CollatzResearch.WordTrace]
  refine ⟨227943790065560274625696031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151962526710373516417130687 227943790065560274625696031)
  ·
    refine ⟨341915685098340411938544047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227943790065560274625696031 341915685098340411938544047)
    ·
      refine ⟨512873527647510617907816071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341915685098340411938544047 512873527647510617907816071)
      ·
        refine ⟨769310291471265926861724107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512873527647510617907816071 769310291471265926861724107)
        ·
          refine ⟨1153965437206898890292586161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769310291471265926861724107 1153965437206898890292586161)
          ·
            refine ⟨865474077905174167719439621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153965437206898890292586161 865474077905174167719439621)
            ·
              refine ⟨162276389607220156447394929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 865474077905174167719439621 162276389607220156447394929)
              ·
                refine ⟨121707292205415117335546197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162276389607220156447394929 121707292205415117335546197)
                ·
                  refine ⟨356564332633052101568983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121707292205415117335546197 356564332633052101568983)
                  ·
                    rfl

theorem cell23_6249659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 10].length) (baseStart_6249659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249659 prefixEnd_6249659 := by exact prefixLift 6249659
  have htrace : WordTrace (prefixWord ++ tailWord_6249659) baseStart_6249659 baseEnd_6249659 := by
    simpa [prefixWord, tailWord_6249659, baseEnd_6249659] using wordTrace_append hprefix tailTrace_6249659
  have hstable : (prefixWord ++ tailWord_6249659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249659).length < 2 ^ (prefixWord ++ tailWord_6249659).sum := by decide
  have hdescent : baseEnd_6249659 < baseStart_6249659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249697 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 1, 4]
def baseStart_6249697 : Nat := 118140960795 + 6249697 * 2 ^ 59
def prefixEnd_6249697 : Nat := 4983230072969 + 3 ^ 40 * 6249697 * 2
def baseEnd_6249697 : Nat := 1069699501987446588481891

theorem tailTrace_6249697 : CollatzResearch.WordTrace tailWord_6249697 prefixEnd_6249697 1069699501987446588481891 := by
  unfold tailWord_6249697
  simp only [CollatzResearch.WordTrace]
  refine ⟨227945176039422607115579345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151963450692948404743719563 227945176039422607115579345)
  ·
    refine ⟨170958882029566955336684509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227945176039422607115579345 170958882029566955336684509)
    ·
      refine ⟨64109580761087608251256691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170958882029566955336684509 64109580761087608251256691)
      ·
        refine ⟨96164371141631412376885037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64109580761087608251256691 96164371141631412376885037)
        ·
          refine ⟨36061639178111779641331889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96164371141631412376885037 36061639178111779641331889)
          ·
            refine ⟨27046229383583834730998917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36061639178111779641331889 27046229383583834730998917)
            ·
              refine ⟨5071168009421969012062297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27046229383583834730998917 5071168009421969012062297)
              ·
                refine ⟨3803376007066476759046723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5071168009421969012062297 3803376007066476759046723)
                ·
                  refine ⟨5705064010599715138570085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803376007066476759046723 5705064010599715138570085)
                  ·
                    refine ⟨1069699501987446588481891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705064010599715138570085 1069699501987446588481891)
                    ·
                      rfl

theorem cell23_6249697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_6249697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249697 prefixEnd_6249697 := by exact prefixLift 6249697
  have htrace : WordTrace (prefixWord ++ tailWord_6249697) baseStart_6249697 baseEnd_6249697 := by
    simpa [prefixWord, tailWord_6249697, baseEnd_6249697] using wordTrace_append hprefix tailTrace_6249697
  have hstable : (prefixWord ++ tailWord_6249697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249697).length < 2 ^ (prefixWord ++ tailWord_6249697).sum := by decide
  have hdescent : baseEnd_6249697 < baseStart_6249697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249713 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_6249713 : Nat := 118140960795 + 6249713 * 2 ^ 59
def prefixEnd_6249713 : Nat := 4983230072969 + 3 ^ 40 * 6249713 * 2
def baseEnd_6249713 : Nat := 3209106721652811702845599

theorem tailTrace_6249713 : CollatzResearch.WordTrace tailWord_6249713 prefixEnd_6249713 3209106721652811702845599 := by
  unfold tailWord_6249713
  simp only [CollatzResearch.WordTrace]
  refine ⟨227945759607364641848161793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151963839738243094565441195 227945759607364641848161793)
  ·
    refine ⟨170959319705523481386121345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227945759607364641848161793 170959319705523481386121345)
    ·
      refine ⟨128219489779142611039591009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170959319705523481386121345 128219489779142611039591009)
      ·
        refine ⟨96164617334356958279693257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128219489779142611039591009 96164617334356958279693257)
        ·
          refine ⟨72123463000767718709769943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96164617334356958279693257 72123463000767718709769943)
          ·
            refine ⟨108185194501151578064654915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72123463000767718709769943 108185194501151578064654915)
            ·
              refine ⟨162277791751727367096982373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108185194501151578064654915 162277791751727367096982373)
              ·
                refine ⟨30427085953448881330684195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162277791751727367096982373 30427085953448881330684195)
                ·
                  refine ⟨45640628930173321996026293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30427085953448881330684195 45640628930173321996026293)
                  ·
                    refine ⟨4278808962203748937127465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45640628930173321996026293 4278808962203748937127465)
                    ·
                      refine ⟨3209106721652811702845599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278808962203748937127465 3209106721652811702845599)
                      ·
                        rfl

theorem cell23_6249713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_6249713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249713 prefixEnd_6249713 := by exact prefixLift 6249713
  have htrace : WordTrace (prefixWord ++ tailWord_6249713) baseStart_6249713 baseEnd_6249713 := by
    simpa [prefixWord, tailWord_6249713, baseEnd_6249713] using wordTrace_append hprefix tailTrace_6249713
  have hstable : (prefixWord ++ tailWord_6249713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249713).length < 2 ^ (prefixWord ++ tailWord_6249713).sum := by decide
  have hdescent : baseEnd_6249713 < baseStart_6249713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249737 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 1, 1, 3]
def baseStart_6249737 : Nat := 118140960795 + 6249737 * 2 ^ 59
def prefixEnd_6249737 : Nat := 4983230072969 + 3 ^ 40 * 6249737 * 2
def baseEnd_6249737 : Nat := 3209119045188519608945489

theorem tailTrace_6249737 : CollatzResearch.WordTrace tailWord_6249737 prefixEnd_6249737 3209119045188519608945489 := by
  unfold tailWord_6249737
  simp only [CollatzResearch.WordTrace]
  refine ⟨227946634959277693947035465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151964423306185129298023643 227946634959277693947035465)
  ·
    refine ⟨170959976219458270460276599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227946634959277693947035465 170959976219458270460276599)
    ·
      refine ⟨256439964329187405690414899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170959976219458270460276599 256439964329187405690414899)
      ·
        refine ⟨384659946493781108535622349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256439964329187405690414899 384659946493781108535622349)
        ·
          refine ⟨144247479935167915700858381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384659946493781108535622349 144247479935167915700858381)
          ·
            refine ⟨54092804975687968387821893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144247479935167915700858381 54092804975687968387821893)
            ·
              refine ⟨10142400932941494072716605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54092804975687968387821893 10142400932941494072716605)
              ·
                refine ⟨3803400349853060277268727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10142400932941494072716605 3803400349853060277268727)
                ·
                  refine ⟨5705100524779590415903091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803400349853060277268727 5705100524779590415903091)
                  ·
                    refine ⟨8557650787169385623854637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705100524779590415903091 8557650787169385623854637)
                    ·
                      refine ⟨3209119045188519608945489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557650787169385623854637 3209119045188519608945489)
                      ·
                        rfl

theorem cell23_6249737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 1, 3].length) (baseStart_6249737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249737 prefixEnd_6249737 := by exact prefixLift 6249737
  have htrace : WordTrace (prefixWord ++ tailWord_6249737) baseStart_6249737 baseEnd_6249737 := by
    simpa [prefixWord, tailWord_6249737, baseEnd_6249737] using wordTrace_append hprefix tailTrace_6249737
  have hstable : (prefixWord ++ tailWord_6249737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249737).length < 2 ^ (prefixWord ++ tailWord_6249737).sum := by decide
  have hdescent : baseEnd_6249737 < baseStart_6249737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249740 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_6249740 : Nat := 118140960795 + 6249740 * 2 ^ 59
def prefixEnd_6249740 : Nat := 4983230072969 + 3 ^ 40 * 6249740 * 2
def baseEnd_6249740 : Nat := 1069706861876827699069325

theorem tailTrace_6249740 : CollatzResearch.WordTrace tailWord_6249740 prefixEnd_6249740 1069706861876827699069325 := by
  unfold tailWord_6249740
  simp only [CollatzResearch.WordTrace]
  refine ⟨113973372189133412729697337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151964496252177883639596449 113973372189133412729697337)
  ·
    refine ⟨85480029141850059547273003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113973372189133412729697337 85480029141850059547273003)
    ·
      refine ⟨128220043712775089320909505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85480029141850059547273003 128220043712775089320909505)
      ·
        refine ⟨96165032784581316990682129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128220043712775089320909505 96165032784581316990682129)
        ·
          refine ⟨72123774588435987743011597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96165032784581316990682129 72123774588435987743011597)
          ·
            refine ⟨27046415470663495403629349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72123774588435987743011597 27046415470663495403629349)
            ·
              refine ⟨5071202900749405388180503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27046415470663495403629349 5071202900749405388180503)
              ·
                refine ⟨7606804351124108082270755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071202900749405388180503 7606804351124108082270755)
                ·
                  refine ⟨11410206526686162123406133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606804351124108082270755 11410206526686162123406133)
                  ·
                    refine ⟨1069706861876827699069325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11410206526686162123406133 1069706861876827699069325)
                    ·
                      rfl

theorem cell23_6249740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_6249740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249740 prefixEnd_6249740 := by exact prefixLift 6249740
  have htrace : WordTrace (prefixWord ++ tailWord_6249740) baseStart_6249740 baseEnd_6249740 := by
    simpa [prefixWord, tailWord_6249740, baseEnd_6249740] using wordTrace_append hprefix tailTrace_6249740
  have hstable : (prefixWord ++ tailWord_6249740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249740).length < 2 ^ (prefixWord ++ tailWord_6249740).sum := by decide
  have hdescent : baseEnd_6249740 < baseStart_6249740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249763 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5]
def baseStart_6249763 : Nat := 118140960795 + 6249763 * 2 ^ 59
def prefixEnd_6249763 : Nat := 4983230072969 + 3 ^ 40 * 6249763 * 2
def baseEnd_6249763 : Nat := 3209132395685536507220369

theorem tailTrace_6249763 : CollatzResearch.WordTrace tailWord_6249763 prefixEnd_6249763 3209132395685536507220369 := by
  unfold tailWord_6249763
  simp only [CollatzResearch.WordTrace]
  refine ⟨227947583257183500387481943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151965055504789000258321295 227947583257183500387481943)
  ·
    refine ⟨341921374885775250581222915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227947583257183500387481943 341921374885775250581222915)
    ·
      refine ⟨512882062328662875871834373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341921374885775250581222915 512882062328662875871834373)
      ·
        refine ⟨96165386686624289225968945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 512882062328662875871834373 96165386686624289225968945)
        ·
          refine ⟨72124040014968216919476709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96165386686624289225968945 72124040014968216919476709)
          ·
            refine ⟨13523257502806540672401883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72124040014968216919476709 13523257502806540672401883)
            ·
              refine ⟨20284886254209811008602825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523257502806540672401883 20284886254209811008602825)
              ·
                refine ⟨15213664690657358256452119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20284886254209811008602825 15213664690657358256452119)
                ·
                  refine ⟨22820497035986037384678179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15213664690657358256452119 22820497035986037384678179)
                  ·
                    refine ⟨34230745553979056077017269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22820497035986037384678179 34230745553979056077017269)
                    ·
                      refine ⟨3209132395685536507220369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34230745553979056077017269 3209132395685536507220369)
                      ·
                        rfl

theorem cell23_6249763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_6249763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249763 prefixEnd_6249763 := by exact prefixLift 6249763
  have htrace : WordTrace (prefixWord ++ tailWord_6249763) baseStart_6249763 baseEnd_6249763 := by
    simpa [prefixWord, tailWord_6249763, baseEnd_6249763] using wordTrace_append hprefix tailTrace_6249763
  have hstable : (prefixWord ++ tailWord_6249763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249763).length < 2 ^ (prefixWord ++ tailWord_6249763).sum := by decide
  have hdescent : baseEnd_6249763 < baseStart_6249763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249770 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_6249770 : Nat := 118140960795 + 6249770 * 2 ^ 59
def prefixEnd_6249770 : Nat := 4983230072969 + 3 ^ 40 * 6249770 * 2
def baseEnd_6249770 : Nat := 1069711996683372659944279

theorem tailTrace_6249770 : CollatzResearch.WordTrace tailWord_6249770 prefixEnd_6249770 1069711996683372659944279 := by
  unfold tailWord_6249770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56986959642039535145746691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151965225712105427055324509 56986959642039535145746691)
  ·
    refine ⟨85480439463059302718620037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56986959642039535145746691 85480439463059302718620037)
    ·
      refine ⟨16027582399323619259741257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85480439463059302718620037 16027582399323619259741257)
      ·
        refine ⟨12020686799492714444805943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16027582399323619259741257 12020686799492714444805943)
        ·
          refine ⟨18031030199239071667208915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12020686799492714444805943 18031030199239071667208915)
          ·
            refine ⟨27046545298858607500813373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18031030199239071667208915 27046545298858607500813373)
            ·
              refine ⟨10142454487071977812805015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27046545298858607500813373 10142454487071977812805015)
              ·
                refine ⟨15213681730607966719207523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10142454487071977812805015 15213681730607966719207523)
                ·
                  refine ⟨22820522595911950078811285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15213681730607966719207523 22820522595911950078811285)
                  ·
                    refine ⟨1069711996683372659944279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22820522595911950078811285 1069711996683372659944279)
                    ·
                      rfl

theorem cell23_6249770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_6249770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249770 prefixEnd_6249770 := by exact prefixLift 6249770
  have htrace : WordTrace (prefixWord ++ tailWord_6249770) baseStart_6249770 baseEnd_6249770 := by
    simpa [prefixWord, tailWord_6249770, baseEnd_6249770] using wordTrace_append hprefix tailTrace_6249770
  have hstable : (prefixWord ++ tailWord_6249770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249770).length < 2 ^ (prefixWord ++ tailWord_6249770).sum := by decide
  have hdescent : baseEnd_6249770 < baseStart_6249770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249777 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_6249777 : Nat := 118140960795 + 6249777 * 2 ^ 59
def prefixEnd_6249777 : Nat := 4983230072969 + 3 ^ 40 * 6249777 * 2
def baseEnd_6249777 : Nat := 3209139584414699452445305

theorem tailTrace_6249777 : CollatzResearch.WordTrace tailWord_6249777 prefixEnd_6249777 3209139584414699452445305 := by
  unfold tailWord_6249777
  simp only [CollatzResearch.WordTrace]
  refine ⟨227948093879132780778491585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151965395919421853852327723 227948093879132780778491585)
  ·
    refine ⟨170961070409349585583868689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227948093879132780778491585 170961070409349585583868689)
    ·
      refine ⟨128220802807012189187901517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170961070409349585583868689 128220802807012189187901517)
      ·
        refine ⟨48082801052629570945463069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128220802807012189187901517 48082801052629570945463069)
        ·
          refine ⟨18031050394736089104548651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48082801052629570945463069 18031050394736089104548651)
          ·
            refine ⟨27046575592104133656822977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18031050394736089104548651 27046575592104133656822977)
            ·
              refine ⟨20284931694078100242617233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27046575592104133656822977 20284931694078100242617233)
              ·
                refine ⟨15213698770558575181962925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20284931694078100242617233 15213698770558575181962925)
                ·
                  refine ⟨5705137038959465693236097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15213698770558575181962925 5705137038959465693236097)
                  ·
                    refine ⟨4278852779219599269927073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5705137038959465693236097 4278852779219599269927073)
                    ·
                      refine ⟨3209139584414699452445305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278852779219599269927073 3209139584414699452445305)
                      ·
                        rfl

theorem cell23_6249777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_6249777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249777 prefixEnd_6249777 := by exact prefixLift 6249777
  have htrace : WordTrace (prefixWord ++ tailWord_6249777) baseStart_6249777 baseEnd_6249777 := by
    simpa [prefixWord, tailWord_6249777, baseEnd_6249777] using wordTrace_append hprefix tailTrace_6249777
  have hstable : (prefixWord ++ tailWord_6249777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249777).length < 2 ^ (prefixWord ++ tailWord_6249777).sum := by decide
  have hdescent : baseEnd_6249777 < baseStart_6249777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249803 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 9, 2]
def baseStart_6249803 : Nat := 118140960795 + 6249803 * 2 ^ 59
def prefixEnd_6249803 : Nat := 4983230072969 + 3 ^ 40 * 6249803 * 2
def baseEnd_6249803 : Nat := 3209152934911716350720185

theorem tailTrace_6249803 : CollatzResearch.WordTrace tailWord_6249803 prefixEnd_6249803 3209152934911716350720185 := by
  unfold tailWord_6249803
  simp only [CollatzResearch.WordTrace]
  refine ⟨227949042177038587218938063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151966028118025724812625375 227949042177038587218938063)
  ·
    refine ⟨341923563265557880828407095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227949042177038587218938063 341923563265557880828407095)
    ·
      refine ⟨512885344898336821242610643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341923563265557880828407095 512885344898336821242610643)
      ·
        refine ⟨769328017347505231863915965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512885344898336821242610643 769328017347505231863915965)
        ·
          refine ⟨288498006505314461948968487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 769328017347505231863915965 288498006505314461948968487)
          ·
            refine ⟨432747009757971692923452731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288498006505314461948968487 432747009757971692923452731)
            ·
              refine ⟨649120514636957539385179097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432747009757971692923452731 649120514636957539385179097)
              ·
                refine ⟨486840385977718154538884323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649120514636957539385179097 486840385977718154538884323)
                ·
                  refine ⟨730260578966577231808326485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486840385977718154538884323 730260578966577231808326485)
                  ·
                    refine ⟨4278870579882288467626913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 730260578966577231808326485 4278870579882288467626913)
                    ·
                      refine ⟨3209152934911716350720185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278870579882288467626913 3209152934911716350720185)
                      ·
                        rfl

theorem cell23_6249803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9, 2].length) (baseStart_6249803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249803 prefixEnd_6249803 := by exact prefixLift 6249803
  have htrace : WordTrace (prefixWord ++ tailWord_6249803) baseStart_6249803 baseEnd_6249803 := by
    simpa [prefixWord, tailWord_6249803, baseEnd_6249803] using wordTrace_append hprefix tailTrace_6249803
  have hstable : (prefixWord ++ tailWord_6249803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249803).length < 2 ^ (prefixWord ++ tailWord_6249803).sum := by decide
  have hdescent : baseEnd_6249803 < baseStart_6249803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249821 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6249821 : Nat := 118140960795 + 6249821 * 2 ^ 59
def prefixEnd_6249821 : Nat := 4983230072969 + 3 ^ 40 * 6249821 * 2
def baseEnd_6249821 : Nat := 1069720725854499093431701

theorem tailTrace_6249821 : CollatzResearch.WordTrace tailWord_6249821 prefixEnd_6249821 1069720725854499093431701 := by
  unfold tailWord_6249821
  simp only [CollatzResearch.WordTrace]
  refine ⟨227949698690973376293093317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151966465793982250862062211 227949698690973376293093317)
  ·
    refine ⟨42740568504557508054954997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227949698690973376293093317 42740568504557508054954997)
    ·
      refine ⟨4006928297302266380152031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42740568504557508054954997 4006928297302266380152031)
      ·
        refine ⟨6010392445953399570228047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006928297302266380152031 6010392445953399570228047)
        ·
          refine ⟨9015588668930099355342071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010392445953399570228047 9015588668930099355342071)
          ·
            refine ⟨13523383003395149033013107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015588668930099355342071 13523383003395149033013107)
            ·
              refine ⟨20285074505092723549519661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523383003395149033013107 20285074505092723549519661)
              ·
                refine ⟨7606902939409771331069873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20285074505092723549519661 7606902939409771331069873)
                ·
                  refine ⟨5705177204557328498302405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606902939409771331069873 5705177204557328498302405)
                  ·
                    refine ⟨1069720725854499093431701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705177204557328498302405 1069720725854499093431701)
                    ·
                      rfl

theorem cell23_6249821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6249821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249821 prefixEnd_6249821 := by exact prefixLift 6249821
  have htrace : WordTrace (prefixWord ++ tailWord_6249821) baseStart_6249821 baseEnd_6249821 := by
    simpa [prefixWord, tailWord_6249821, baseEnd_6249821] using wordTrace_append hprefix tailTrace_6249821
  have hstable : (prefixWord ++ tailWord_6249821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249821).length < 2 ^ (prefixWord ++ tailWord_6249821).sum := by decide
  have hdescent : baseEnd_6249821 < baseStart_6249821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249827 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 3]
def baseStart_6249827 : Nat := 118140960795 + 6249827 * 2 ^ 59
def prefixEnd_6249827 : Nat := 4983230072969 + 3 ^ 40 * 6249827 * 2
def baseEnd_6249827 : Nat := 3209165258447424256820075

theorem tailTrace_6249827 : CollatzResearch.WordTrace tailWord_6249827 prefixEnd_6249827 3209165258447424256820075 := by
  unfold tailWord_6249827
  simp only [CollatzResearch.WordTrace]
  refine ⟨227949917528951639317811735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151966611685967759545207823 227949917528951639317811735)
  ·
    refine ⟨341924876293427458976717603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227949917528951639317811735 341924876293427458976717603)
    ·
      refine ⟨512887314440141188465076405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341924876293427458976717603 512887314440141188465076405)
      ·
        refine ⟨48083185728763236418600913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 512887314440141188465076405 48083185728763236418600913)
        ·
          refine ⟨36062389296572427313950685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48083185728763236418600913 36062389296572427313950685)
          ·
            refine ⟨13523395986214660242731507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36062389296572427313950685 13523395986214660242731507)
            ·
              refine ⟨20285093979321990364097261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523395986214660242731507 20285093979321990364097261)
              ·
                refine ⟨7606910242245746386536473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20285093979321990364097261 7606910242245746386536473)
                ·
                  refine ⟨5705182681684309789902355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606910242245746386536473 5705182681684309789902355)
                  ·
                    refine ⟨8557774022526464684853533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705182681684309789902355 8557774022526464684853533)
                    ·
                      refine ⟨3209165258447424256820075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557774022526464684853533 3209165258447424256820075)
                      ·
                        rfl

theorem cell23_6249827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_6249827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249827 prefixEnd_6249827 := by exact prefixLift 6249827
  have htrace : WordTrace (prefixWord ++ tailWord_6249827) baseStart_6249827 baseEnd_6249827 := by
    simpa [prefixWord, tailWord_6249827, baseEnd_6249827] using wordTrace_append hprefix tailTrace_6249827
  have hstable : (prefixWord ++ tailWord_6249827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249827).length < 2 ^ (prefixWord ++ tailWord_6249827).sum := by decide
  have hdescent : baseEnd_6249827 < baseStart_6249827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249837 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6249837 : Nat := 118140960795 + 6249837 * 2 ^ 59
def prefixEnd_6249837 : Nat := 4983230072969 + 3 ^ 40 * 6249837 * 2
def baseEnd_6249837 : Nat := 3209170393253969217695029

theorem tailTrace_6249837 : CollatzResearch.WordTrace tailWord_6249837 prefixEnd_6249837 3209170393253969217695029 := by
  unfold tailWord_6249837
  simp only [CollatzResearch.WordTrace]
  refine ⟨227950282258915411025675765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151966854839276940683783843 227950282258915411025675765)
  ·
    refine ⟨21370338961773319783657103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227950282258915411025675765 21370338961773319783657103)
    ·
      refine ⟨32055508442659979675485655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21370338961773319783657103 32055508442659979675485655)
      ·
        refine ⟨48083262663989969513228483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32055508442659979675485655 48083262663989969513228483)
        ·
          refine ⟨72124893995984954269842725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48083262663989969513228483 72124893995984954269842725)
          ·
            refine ⟨13523417624247178925595511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72124893995984954269842725 13523417624247178925595511)
            ·
              refine ⟨20285126436370768388393267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523417624247178925595511 20285126436370768388393267)
              ·
                refine ⟨30427689654556152582589901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20285126436370768388393267 30427689654556152582589901)
                ·
                  refine ⟨11410383620458557218471213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30427689654556152582589901 11410383620458557218471213)
                  ·
                    refine ⟨4278893857671958956926705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11410383620458557218471213 4278893857671958956926705)
                    ·
                      refine ⟨3209170393253969217695029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278893857671958956926705 3209170393253969217695029)
                      ·
                        rfl

theorem cell23_6249837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6249837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249837 prefixEnd_6249837 := by exact prefixLift 6249837
  have htrace : WordTrace (prefixWord ++ tailWord_6249837) baseStart_6249837 baseEnd_6249837 := by
    simpa [prefixWord, tailWord_6249837, baseEnd_6249837] using wordTrace_append hprefix tailTrace_6249837
  have hstable : (prefixWord ++ tailWord_6249837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249837).length < 2 ^ (prefixWord ++ tailWord_6249837).sum := by decide
  have hdescent : baseEnd_6249837 < baseStart_6249837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249850 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_6249850 : Nat := 118140960795 + 6249850 * 2 ^ 59
def prefixEnd_6249850 : Nat := 4983230072969 + 3 ^ 40 * 6249850 * 2
def baseEnd_6249850 : Nat := 3209177068502477666832469

theorem tailTrace_6249850 : CollatzResearch.WordTrace tailWord_6249850 prefixEnd_6249850 3209177068502477666832469 := by
  unfold tailWord_6249850
  simp only [CollatzResearch.WordTrace]
  refine ⟨56987689101967078561474751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151967170938578876163932669 56987689101967078561474751)
  ·
    refine ⟨85481533652950617842212127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56987689101967078561474751 85481533652950617842212127)
    ·
      refine ⟨128222300479425926763318191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85481533652950617842212127 128222300479425926763318191)
      ·
        refine ⟨192333450719138890144977287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128222300479425926763318191 192333450719138890144977287)
        ·
          refine ⟨288500176078708335217465931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192333450719138890144977287 288500176078708335217465931)
          ·
            refine ⟨432750264118062502826198897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288500176078708335217465931 432750264118062502826198897)
            ·
              refine ⟨324562698088546877119649173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432750264118062502826198897 324562698088546877119649173)
              ·
                refine ⟨15213876472900634864983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324562698088546877119649173 15213876472900634864983555)
                ·
                  refine ⟨22820814709350952297475333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15213876472900634864983555 22820814709350952297475333)
                  ·
                    refine ⟨4278902758003303555776625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22820814709350952297475333 4278902758003303555776625)
                    ·
                      refine ⟨3209177068502477666832469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4278902758003303555776625 3209177068502477666832469)
                      ·
                        rfl

theorem cell23_6249850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_6249850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249850 prefixEnd_6249850 := by exact prefixLift 6249850
  have htrace : WordTrace (prefixWord ++ tailWord_6249850) baseStart_6249850 baseEnd_6249850 := by
    simpa [prefixWord, tailWord_6249850, baseEnd_6249850] using wordTrace_append hprefix tailTrace_6249850
  have hstable : (prefixWord ++ tailWord_6249850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249850).length < 2 ^ (prefixWord ++ tailWord_6249850).sum := by decide
  have hdescent : baseEnd_6249850 < baseStart_6249850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249853 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_6249853 : Nat := 118140960795 + 6249853 * 2 ^ 59
def prefixEnd_6249853 : Nat := 4983230072969 + 3 ^ 40 * 6249853 * 2
def baseEnd_6249853 : Nat := 3209178608944441155094955

theorem tailTrace_6249853 : CollatzResearch.WordTrace tailWord_6249853 prefixEnd_6249853 3209178608944441155094955 := by
  unfold tailWord_6249853
  simp only [CollatzResearch.WordTrace]
  refine ⟨227950865826857445758258213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151967243884571630505505475 227950865826857445758258213)
  ·
    refine ⟨42740787342535771079673415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227950865826857445758258213 42740787342535771079673415)
    ·
      refine ⟨64111181013803656619510123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42740787342535771079673415 64111181013803656619510123)
      ·
        refine ⟨96166771520705484929265185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64111181013803656619510123 96166771520705484929265185)
        ·
          refine ⟨72125078640529113696948889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96166771520705484929265185 72125078640529113696948889)
          ·
            refine ⟨54093808980396835272711667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72125078640529113696948889 54093808980396835272711667)
            ·
              refine ⟨81140713470595252909067501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54093808980396835272711667 81140713470595252909067501)
              ·
                refine ⟨30427767551473219840900313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81140713470595252909067501 30427767551473219840900313)
                ·
                  refine ⟨22820825663604914880675235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30427767551473219840900313 22820825663604914880675235)
                  ·
                    refine ⟨34231238495407372321012853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22820825663604914880675235 34231238495407372321012853)
                    ·
                      refine ⟨3209178608944441155094955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34231238495407372321012853 3209178608944441155094955)
                      ·
                        rfl

theorem cell23_6249853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_6249853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249853 prefixEnd_6249853 := by exact prefixLift 6249853
  have htrace : WordTrace (prefixWord ++ tailWord_6249853) baseStart_6249853 baseEnd_6249853 := by
    simpa [prefixWord, tailWord_6249853, baseEnd_6249853] using wordTrace_append hprefix tailTrace_6249853
  have hstable : (prefixWord ++ tailWord_6249853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249853).length < 2 ^ (prefixWord ++ tailWord_6249853).sum := by decide
  have hdescent : baseEnd_6249853 < baseStart_6249853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249883 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3]
def baseStart_6249883 : Nat := 118140960795 + 6249883 * 2 ^ 59
def prefixEnd_6249883 : Nat := 4983230072969 + 3 ^ 40 * 6249883 * 2
def baseEnd_6249883 : Nat := 3209194013364076037719817

theorem tailTrace_6249883 : CollatzResearch.WordTrace tailWord_6249883 prefixEnd_6249883 3209194013364076037719817 := by
  unfold tailWord_6249883
  simp only [CollatzResearch.WordTrace]
  refine ⟨227951960016748760881850303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151967973344499173921233535 227951960016748760881850303)
  ·
    refine ⟨341927940025123141322775455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227951960016748760881850303 341927940025123141322775455)
    ·
      refine ⟨512891910037684711984163183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341927940025123141322775455 512891910037684711984163183)
      ·
        refine ⟨769337865056527067976244775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512891910037684711984163183 769337865056527067976244775)
        ·
          refine ⟨1154006797584790601964367163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769337865056527067976244775 1154006797584790601964367163)
          ·
            refine ⟨1731010196377185902946550745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154006797584790601964367163 1731010196377185902946550745)
            ·
              refine ⟨1298257647282889427209913059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731010196377185902946550745 1298257647282889427209913059)
              ·
                refine ⟨1947386470924334140814869589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298257647282889427209913059 1947386470924334140814869589)
                ·
                  refine ⟨22820935206144540712674253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1947386470924334140814869589 22820935206144540712674253)
                  ·
                    refine ⟨8557850702304202767252845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22820935206144540712674253 8557850702304202767252845)
                    ·
                      refine ⟨3209194013364076037719817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557850702304202767252845 3209194013364076037719817)
                      ·
                        rfl

theorem cell23_6249883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3].length) (baseStart_6249883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249883 prefixEnd_6249883 := by exact prefixLift 6249883
  have htrace : WordTrace (prefixWord ++ tailWord_6249883) baseStart_6249883 baseEnd_6249883 := by
    simpa [prefixWord, tailWord_6249883, baseEnd_6249883] using wordTrace_append hprefix tailTrace_6249883
  have hstable : (prefixWord ++ tailWord_6249883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249883).length < 2 ^ (prefixWord ++ tailWord_6249883).sum := by decide
  have hdescent : baseEnd_6249883 < baseStart_6249883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249890 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_6249890 : Nat := 118140960795 + 6249890 * 2 ^ 59
def prefixEnd_6249890 : Nat := 4983230072969 + 3 ^ 40 * 6249890 * 2
def baseEnd_6249890 : Nat := 356577511969850834481365

theorem tailTrace_6249890 : CollatzResearch.WordTrace tailWord_6249890 prefixEnd_6249890 356577511969850834481365 := by
  unfold tailWord_6249890
  simp only [CollatzResearch.WordTrace]
  refine ⟨56988053831930850269338781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151968143551815600718236749 56988053831930850269338781)
  ·
    refine ⟨21370520186974068851002043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56988053831930850269338781 21370520186974068851002043)
    ·
      refine ⟨32055780280461103276503065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21370520186974068851002043 32055780280461103276503065)
      ·
        refine ⟨24041835210345827457377299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32055780280461103276503065 24041835210345827457377299)
        ·
          refine ⟨36062752815518741186065949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24041835210345827457377299 36062752815518741186065949)
          ·
            refine ⟨13523532305819527944774731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36062752815518741186065949 13523532305819527944774731)
            ·
              refine ⟨20285298458729291917162097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523532305819527944774731 20285298458729291917162097)
              ·
                refine ⟨15213973844046968937871573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20285298458729291917162097 15213973844046968937871573)
                ·
                  refine ⟨356577511969850834481365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15213973844046968937871573 356577511969850834481365)
                  ·
                    rfl

theorem cell23_6249890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_6249890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249890 prefixEnd_6249890 := by exact prefixLift 6249890
  have htrace : WordTrace (prefixWord ++ tailWord_6249890) baseStart_6249890 baseEnd_6249890 := by
    simpa [prefixWord, tailWord_6249890, baseEnd_6249890] using wordTrace_append hprefix tailTrace_6249890
  have hstable : (prefixWord ++ tailWord_6249890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249890).length < 2 ^ (prefixWord ++ tailWord_6249890).sum := by decide
  have hdescent : baseEnd_6249890 < baseStart_6249890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249960 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6249960 : Nat := 118140960795 + 6249960 * 2 ^ 59
def prefixEnd_6249960 : Nat := 4983230072969 + 3 ^ 40 * 6249960 * 2
def baseEnd_6249960 : Nat := 3209233551374472236456963

theorem tailTrace_6249960 : CollatzResearch.WordTrace tailWord_6249960 prefixEnd_6249960 3209233551374472236456963 := by
  unfold tailWord_6249960
  simp only [CollatzResearch.WordTrace]
  refine ⟨113977384218734901516201667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151969845624979868688268889 113977384218734901516201667)
  ·
    refine ⟨170966076328102352274302501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113977384218734901516201667 170966076328102352274302501)
    ·
      refine ⟨32056139311519191051431719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170966076328102352274302501 32056139311519191051431719)
      ·
        refine ⟨48084208967278786577147579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32056139311519191051431719 48084208967278786577147579)
        ·
          refine ⟨72126313450918179865721369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48084208967278786577147579 72126313450918179865721369)
          ·
            refine ⟨54094735088188634899291027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72126313450918179865721369 54094735088188634899291027)
            ·
              refine ⟨81142102632282952348936541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54094735088188634899291027 81142102632282952348936541)
              ·
                refine ⟨30428288487106107130851203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81142102632282952348936541 30428288487106107130851203)
                ·
                  refine ⟨45642432730659160696276805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30428288487106107130851203 45642432730659160696276805)
                  ·
                    refine ⟨8557956136998592630551901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45642432730659160696276805 8557956136998592630551901)
                    ·
                      refine ⟨3209233551374472236456963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8557956136998592630551901 3209233551374472236456963)
                      ·
                        rfl

theorem cell23_6249960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6249960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249960 prefixEnd_6249960 := by exact prefixLift 6249960
  have htrace : WordTrace (prefixWord ++ tailWord_6249960) baseStart_6249960 baseEnd_6249960 := by
    simpa [prefixWord, tailWord_6249960, baseEnd_6249960] using wordTrace_append hprefix tailTrace_6249960
  have hstable : (prefixWord ++ tailWord_6249960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249960).length < 2 ^ (prefixWord ++ tailWord_6249960).sum := by decide
  have hdescent : baseEnd_6249960 < baseStart_6249960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6249983 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_6249983 : Nat := 118140960795 + 6249983 * 2 ^ 59
def prefixEnd_6249983 : Nat := 4983230072969 + 3 ^ 40 * 6249983 * 2
def baseEnd_6249983 : Nat := 3209245361429525646469357

theorem tailTrace_6249983 : CollatzResearch.WordTrace tailWord_6249983 prefixEnd_6249983 3209245361429525646469357 := by
  unfold tailWord_6249983
  simp only [CollatzResearch.WordTrace]
  refine ⟨227955607316386477960490603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151970404877590985306993735 227955607316386477960490603)
  ·
    refine ⟨341933410974579716940735905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227955607316386477960490603 341933410974579716940735905)
    ·
      refine ⟨256450058230934787705551929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341933410974579716940735905 256450058230934787705551929)
      ·
        refine ⟨192337543673201090779163947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256450058230934787705551929 192337543673201090779163947)
        ·
          refine ⟨288506315509801636168745921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192337543673201090779163947 288506315509801636168745921)
          ·
            refine ⟨216379736632351227126559441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288506315509801636168745921 216379736632351227126559441)
            ·
              refine ⟨162284802474263420344919581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216379736632351227126559441 162284802474263420344919581)
              ·
                refine ⟨60856800927848782629344843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162284802474263420344919581 60856800927848782629344843)
                ·
                  refine ⟨91285201391773173944017265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60856800927848782629344843 91285201391773173944017265)
                  ·
                    refine ⟨68463901043829880458012949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91285201391773173944017265 68463901043829880458012949)
                    ·
                      refine ⟨3209245361429525646469357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68463901043829880458012949 3209245361429525646469357)
                      ·
                        rfl

theorem cell23_6249983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_6249983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6249983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6249983 prefixEnd_6249983 := by exact prefixLift 6249983
  have htrace : WordTrace (prefixWord ++ tailWord_6249983) baseStart_6249983 baseEnd_6249983 := by
    simpa [prefixWord, tailWord_6249983, baseEnd_6249983] using wordTrace_append hprefix tailTrace_6249983
  have hstable : (prefixWord ++ tailWord_6249983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6249983).length < 2 ^ (prefixWord ++ tailWord_6249983).sum := by decide
  have hdescent : baseEnd_6249983 < baseStart_6249983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6249983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250041 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6250041 : Nat := 118140960795 + 6250041 * 2 ^ 59
def prefixEnd_6250041 : Nat := 4983230072969 + 3 ^ 40 * 6250041 * 2
def baseEnd_6250041 : Nat := 3209275143307486419544091

theorem tailTrace_6250041 : CollatzResearch.WordTrace tailWord_6250041 prefixEnd_6250041 3209275143307486419544091 := by
  unfold tailWord_6250041
  simp only [CollatzResearch.WordTrace]
  refine ⟨227957722750176353866101977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151971815166784235910734651 227957722750176353866101977)
  ·
    refine ⟨170968292062632265399576483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227957722750176353866101977 170968292062632265399576483)
    ·
      refine ⟨256452438093948398099364725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170968292062632265399576483 256452438093948398099364725)
      ·
        refine ⟨24042416071307662321815443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256452438093948398099364725 24042416071307662321815443)
        ·
          refine ⟨36063624106961493482723165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24042416071307662321815443 36063624106961493482723165)
          ·
            refine ⟨13523859040110560056021187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36063624106961493482723165 13523859040110560056021187)
            ·
              refine ⟨20285788560165840084031781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523859040110560056021187 20285788560165840084031781)
              ·
                refine ⟨3803585355031095015755959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20285788560165840084031781 3803585355031095015755959)
                ·
                  refine ⟨5705378032546642523633939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803585355031095015755959 5705378032546642523633939)
                  ·
                    refine ⟨8558067048819963785450909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705378032546642523633939 8558067048819963785450909)
                    ·
                      refine ⟨3209275143307486419544091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558067048819963785450909 3209275143307486419544091)
                      ·
                        rfl

theorem cell23_6250041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6250041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250041 prefixEnd_6250041 := by exact prefixLift 6250041
  have htrace : WordTrace (prefixWord ++ tailWord_6250041) baseStart_6250041 baseEnd_6250041 := by
    simpa [prefixWord, tailWord_6250041, baseEnd_6250041] using wordTrace_append hprefix tailTrace_6250041
  have hstable : (prefixWord ++ tailWord_6250041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250041).length < 2 ^ (prefixWord ++ tailWord_6250041).sum := by decide
  have hdescent : baseEnd_6250041 < baseStart_6250041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250064 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2]
def baseStart_6250064 : Nat := 118140960795 + 6250064 * 2 ^ 59
def prefixEnd_6250064 : Nat := 4983230072969 + 3 ^ 40 * 6250064 * 2
def baseEnd_6250064 : Nat := 3209286953362539829556485

theorem tailTrace_6250064 : CollatzResearch.WordTrace tailWord_6250064 prefixEnd_6250064 3209286953362539829556485 := by
  unfold tailWord_6250064
  simp only [CollatzResearch.WordTrace]
  refine ⟨113979280814546514397094623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151972374419395352529459497 113979280814546514397094623)
  ·
    refine ⟨170968921221819771595641935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113979280814546514397094623 170968921221819771595641935)
    ·
      refine ⟨256453381832729657393462903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170968921221819771595641935 256453381832729657393462903)
      ·
        refine ⟨384680072749094486090194355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256453381832729657393462903 384680072749094486090194355)
        ·
          refine ⟨577020109123641729135291533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384680072749094486090194355 577020109123641729135291533)
          ·
            refine ⟨216382540921365648425734325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577020109123641729135291533 216382540921365648425734325)
            ·
              refine ⟨20285863211378029539912593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216382540921365648425734325 20285863211378029539912593)
              ·
                refine ⟨15214397408533522154934445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20285863211378029539912593 15214397408533522154934445)
                ·
                  refine ⟨5705399028200070808100417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15214397408533522154934445 5705399028200070808100417)
                  ·
                    refine ⟨4279049271150053106075313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5705399028200070808100417 4279049271150053106075313)
                    ·
                      refine ⟨3209286953362539829556485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279049271150053106075313 3209286953362539829556485)
                      ·
                        rfl

theorem cell23_6250064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 2, 2].length) (baseStart_6250064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250064 prefixEnd_6250064 := by exact prefixLift 6250064
  have htrace : WordTrace (prefixWord ++ tailWord_6250064) baseStart_6250064 baseEnd_6250064 := by
    simpa [prefixWord, tailWord_6250064, baseEnd_6250064] using wordTrace_append hprefix tailTrace_6250064
  have hstable : (prefixWord ++ tailWord_6250064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250064).length < 2 ^ (prefixWord ++ tailWord_6250064).sum := by decide
  have hdescent : baseEnd_6250064 < baseStart_6250064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250084 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_6250084 : Nat := 118140960795 + 6250084 * 2 ^ 59
def prefixEnd_6250084 : Nat := 4983230072969 + 3 ^ 40 * 6250084 * 2
def baseEnd_6250084 : Nat := 3209297222975629751306393

theorem tailTrace_6250084 : CollatzResearch.WordTrace tailWord_6250084 prefixEnd_6250084 3209297222975629751306393 := by
  unfold tailWord_6250084
  simp only [CollatzResearch.WordTrace]
  refine ⟨113979645544510286104958653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151972860726013714806611537 113979645544510286104958653)
  ·
    refine ⟨42742367079191357289359495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113979645544510286104958653 42742367079191357289359495)
    ·
      refine ⟨64113550618787035934039243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42742367079191357289359495 64113550618787035934039243)
      ·
        refine ⟨96170325928180553901058865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64113550618787035934039243 96170325928180553901058865)
        ·
          refine ⟨72127744446135415425794149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96170325928180553901058865 72127744446135415425794149)
          ·
            refine ⟨13523952083650390392336403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72127744446135415425794149 13523952083650390392336403)
            ·
              refine ⟨20285928125475585588504605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523952083650390392336403 20285928125475585588504605)
              ·
                refine ⟨7607223047053344595689227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20285928125475585588504605 7607223047053344595689227)
                ·
                  refine ⟨11410834570580016893533841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607223047053344595689227 11410834570580016893533841)
                  ·
                    refine ⟨8558125927935012670150381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11410834570580016893533841 8558125927935012670150381)
                    ·
                      refine ⟨3209297222975629751306393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558125927935012670150381 3209297222975629751306393)
                      ·
                        rfl

theorem cell23_6250084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_6250084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250084 prefixEnd_6250084 := by exact prefixLift 6250084
  have htrace : WordTrace (prefixWord ++ tailWord_6250084) baseStart_6250084 baseEnd_6250084 := by
    simpa [prefixWord, tailWord_6250084, baseEnd_6250084] using wordTrace_append hprefix tailTrace_6250084
  have hstable : (prefixWord ++ tailWord_6250084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250084).length < 2 ^ (prefixWord ++ tailWord_6250084).sum := by decide
  have hdescent : baseEnd_6250084 < baseStart_6250084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250098 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6250098 : Nat := 118140960795 + 6250098 * 2 ^ 59
def prefixEnd_6250098 : Nat := 4983230072969 + 3 ^ 40 * 6250098 * 2
def baseEnd_6250098 : Nat := 3209304411704792696531329

theorem tailTrace_6250098 : CollatzResearch.WordTrace tailWord_6250098 prefixEnd_6250098 3209304411704792696531329 := by
  unfold tailWord_6250098
  simp only [CollatzResearch.WordTrace]
  refine ⟨56989950427742463150231737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151973201140646568400617965 56989950427742463150231737)
  ·
    refine ⟨42742462820806847362673803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56989950427742463150231737 42742462820806847362673803)
    ·
      refine ⟨64113694231210271044010705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42742462820806847362673803 64113694231210271044010705)
      ·
        refine ⟨48085270673407703283008029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64113694231210271044010705 48085270673407703283008029)
        ·
          refine ⟨18031976502527888731128011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48085270673407703283008029 18031976502527888731128011)
          ·
            refine ⟨27047964753791833096692017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18031976502527888731128011 27047964753791833096692017)
            ·
              refine ⟨20285973565343874822519013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27047964753791833096692017 20285973565343874822519013)
              ·
                refine ⟨3803620043501976529222315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20285973565343874822519013 3803620043501976529222315)
                ·
                  refine ⟨5705430065252964793833473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803620043501976529222315 5705430065252964793833473)
                  ·
                    refine ⟨4279072548939723595375105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5705430065252964793833473 4279072548939723595375105)
                    ·
                      refine ⟨3209304411704792696531329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279072548939723595375105 3209304411704792696531329)
                      ·
                        rfl

theorem cell23_6250098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6250098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250098 prefixEnd_6250098 := by exact prefixLift 6250098
  have htrace : WordTrace (prefixWord ++ tailWord_6250098) baseStart_6250098 baseEnd_6250098 := by
    simpa [prefixWord, tailWord_6250098, baseEnd_6250098] using wordTrace_append hprefix tailTrace_6250098
  have hstable : (prefixWord ++ tailWord_6250098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250098).length < 2 ^ (prefixWord ++ tailWord_6250098).sum := by decide
  have hdescent : baseEnd_6250098 < baseStart_6250098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250132 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6250132 : Nat := 118140960795 + 6250132 * 2 ^ 59
def prefixEnd_6250132 : Nat := 4983230072969 + 3 ^ 40 * 6250132 * 2
def baseEnd_6250132 : Nat := 3209321870047045563506173

theorem tailTrace_6250132 : CollatzResearch.WordTrace tailWord_6250132 prefixEnd_6250132 3209321870047045563506173 := by
  unfold tailWord_6250132
  simp only [CollatzResearch.WordTrace]
  refine ⟨113980520896423338203832325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151974027861897784271776433 113980520896423338203832325)
  ·
    refine ⟨21371347668079375913218561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113980520896423338203832325 21371347668079375913218561)
    ·
      refine ⟨16028510751059531934913921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21371347668079375913218561 16028510751059531934913921)
      ·
        refine ⟨12021383063294648951185441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16028510751059531934913921 12021383063294648951185441)
        ·
          refine ⟨9016037297470986713389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12021383063294648951185441 9016037297470986713389081)
          ·
            refine ⟨6762027973103240035041811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9016037297470986713389081 6762027973103240035041811)
            ·
              refine ⟨10143041959654860052562717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762027973103240035041811 10143041959654860052562717)
              ·
                refine ⟨3803640734870572519711019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10143041959654860052562717 3803640734870572519711019)
                ·
                  refine ⟨5705461102305858779566529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803640734870572519711019 5705461102305858779566529)
                  ·
                    refine ⟨4279095826729394084674897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5705461102305858779566529 4279095826729394084674897)
                    ·
                      refine ⟨3209321870047045563506173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279095826729394084674897 3209321870047045563506173)
                      ·
                        rfl

theorem cell23_6250132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6250132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250132 prefixEnd_6250132 := by exact prefixLift 6250132
  have htrace : WordTrace (prefixWord ++ tailWord_6250132) baseStart_6250132 baseEnd_6250132 := by
    simpa [prefixWord, tailWord_6250132, baseEnd_6250132] using wordTrace_append hprefix tailTrace_6250132
  have hstable : (prefixWord ++ tailWord_6250132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250132).length < 2 ^ (prefixWord ++ tailWord_6250132).sum := by decide
  have hdescent : baseEnd_6250132 < baseStart_6250132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250157 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6250157 : Nat := 118140960795 + 6250157 * 2 ^ 59
def prefixEnd_6250157 : Nat := 4983230072969 + 3 ^ 40 * 6250157 * 2
def baseEnd_6250157 : Nat := 3209334707063407965693557

theorem tailTrace_6250157 : CollatzResearch.WordTrace tailWord_6250157 prefixEnd_6250157 3209334707063407965693557 := by
  unfold tailWord_6250157
  simp only [CollatzResearch.WordTrace]
  refine ⟨227961953617756105677324725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151974635745170737118216483 227961953617756105677324725)
  ·
    refine ⟨21371433151664634907249193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227961953617756105677324725 21371433151664634907249193)
    ·
      refine ⟨16028574863748476180436895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21371433151664634907249193 16028574863748476180436895)
      ·
        refine ⟨24042862295622714270655343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028574863748476180436895 24042862295622714270655343)
        ·
          refine ⟨36064293443434071405983015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24042862295622714270655343 36064293443434071405983015)
          ·
            refine ⟨54096440165151107108974523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36064293443434071405983015 54096440165151107108974523)
            ·
              refine ⟨81144660247726660663461785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54096440165151107108974523 81144660247726660663461785)
              ·
                refine ⟨60858495185794995497596339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81144660247726660663461785 60858495185794995497596339)
                ·
                  refine ⟨91287742778692493246394509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60858495185794995497596339 91287742778692493246394509)
                  ·
                    refine ⟨34232903542009684967397941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91287742778692493246394509 34232903542009684967397941)
                    ·
                      refine ⟨3209334707063407965693557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34232903542009684967397941 3209334707063407965693557)
                      ·
                        rfl

theorem cell23_6250157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6250157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250157 prefixEnd_6250157 := by exact prefixLift 6250157
  have htrace : WordTrace (prefixWord ++ tailWord_6250157) baseStart_6250157 baseEnd_6250157 := by
    simpa [prefixWord, tailWord_6250157, baseEnd_6250157] using wordTrace_append hprefix tailTrace_6250157
  have hstable : (prefixWord ++ tailWord_6250157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250157).length < 2 ^ (prefixWord ++ tailWord_6250157).sum := by decide
  have hdescent : baseEnd_6250157 < baseStart_6250157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250165 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6250165 : Nat := 118140960795 + 6250165 * 2 ^ 59
def prefixEnd_6250165 : Nat := 4983230072969 + 3 ^ 40 * 6250165 * 2
def baseEnd_6250165 : Nat := 3209338814908643934393521

theorem tailTrace_6250165 : CollatzResearch.WordTrace tailWord_6250165 prefixEnd_6250165 3209338814908643934393521 := by
  unfold tailWord_6250165
  simp only [CollatzResearch.WordTrace]
  refine ⟨227962245401727123043615949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151974830267818082029077299 227962245401727123043615949)
  ·
    refine ⟨85485842025647671141355981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227962245401727123043615949 85485842025647671141355981)
    ·
      refine ⟨32057190759617876678008493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85485842025647671141355981 32057190759617876678008493)
      ·
        refine ⟨12021446534856703754253185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32057190759617876678008493 12021446534856703754253185)
        ·
          refine ⟨9016084901142527815689889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12021446534856703754253185 9016084901142527815689889)
          ·
            refine ⟨6762063675856895861767417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9016084901142527815689889 6762063675856895861767417)
            ·
              refine ⟨5071547756892671896325563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6762063675856895861767417 5071547756892671896325563)
              ·
                refine ⟨7607321635339007844488345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071547756892671896325563 7607321635339007844488345)
                ·
                  refine ⟨5705491226504255883366259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7607321635339007844488345 5705491226504255883366259)
                  ·
                    refine ⟨8558236839756383825049389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705491226504255883366259 8558236839756383825049389)
                    ·
                      refine ⟨3209338814908643934393521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558236839756383825049389 3209338814908643934393521)
                      ·
                        rfl

theorem cell23_6250165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6250165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250165 prefixEnd_6250165 := by exact prefixLift 6250165
  have htrace : WordTrace (prefixWord ++ tailWord_6250165) baseStart_6250165 baseEnd_6250165 := by
    simpa [prefixWord, tailWord_6250165, baseEnd_6250165] using wordTrace_append hprefix tailTrace_6250165
  have hstable : (prefixWord ++ tailWord_6250165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250165).length < 2 ^ (prefixWord ++ tailWord_6250165).sum := by decide
  have hdescent : baseEnd_6250165 < baseStart_6250165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250207 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 2, 5]
def baseStart_6250207 : Nat := 118140960795 + 6250207 * 2 ^ 59
def prefixEnd_6250207 : Nat := 4983230072969 + 3 ^ 40 * 6250207 * 2
def baseEnd_6250207 : Nat := 1069786793698710923356109

theorem tailTrace_6250207 : CollatzResearch.WordTrace tailWord_6250207 prefixEnd_6250207 1069786793698710923356109 := by
  unfold tailWord_6250207
  simp only [CollatzResearch.WordTrace]
  refine ⟨227963777267574964216644875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151975851511716642811096583 227963777267574964216644875)
  ·
    refine ⟨341945665901362446324967313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227963777267574964216644875 341945665901362446324967313)
    ·
      refine ⟨256459249426021834743725485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341945665901362446324967313 256459249426021834743725485)
      ·
        refine ⟨96172218534758188028897057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256459249426021834743725485 96172218534758188028897057)
        ·
          refine ⟨72129163901068641021672793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96172218534758188028897057 72129163901068641021672793)
          ·
            refine ⟨54096872925801480766254595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72129163901068641021672793 54096872925801480766254595)
            ·
              refine ⟨81145309388702221149381893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54096872925801480766254595 81145309388702221149381893)
              ·
                refine ⟨15214745510381666465509105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81145309388702221149381893 15214745510381666465509105)
                ·
                  refine ⟨11411059132786249849131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15214745510381666465509105 11411059132786249849131829)
                  ·
                    refine ⟨1069786793698710923356109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11411059132786249849131829 1069786793698710923356109)
                    ·
                      rfl

theorem cell23_6250207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_6250207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250207 prefixEnd_6250207 := by exact prefixLift 6250207
  have htrace : WordTrace (prefixWord ++ tailWord_6250207) baseStart_6250207 baseEnd_6250207 := by
    simpa [prefixWord, tailWord_6250207, baseEnd_6250207] using wordTrace_append hprefix tailTrace_6250207
  have hstable : (prefixWord ++ tailWord_6250207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250207).length < 2 ^ (prefixWord ++ tailWord_6250207).sum := by decide
  have hdescent : baseEnd_6250207 < baseStart_6250207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250211 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 5]
def baseStart_6250211 : Nat := 118140960795 + 6250211 * 2 ^ 59
def prefixEnd_6250211 : Nat := 4983230072969 + 3 ^ 40 * 6250211 * 2
def baseEnd_6250211 : Nat := 356595826113194528268701

theorem tailTrace_6250211 : CollatzResearch.WordTrace tailWord_6250211 prefixEnd_6250211 356595826113194528268701 := by
  unfold tailWord_6250211
  simp only [CollatzResearch.WordTrace]
  refine ⟨227963923159560472899790487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151975948773040315266526991 227963923159560472899790487)
  ·
    refine ⟨341945884739340709349685731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227963923159560472899790487 341945884739340709349685731)
    ·
      refine ⟨512918827109011064024528597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341945884739340709349685731 512918827109011064024528597)
      ·
        refine ⟨12021535010367446813074889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 512918827109011064024528597 12021535010367446813074889)
        ·
          refine ⟨9016151257775585109806167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12021535010367446813074889 9016151257775585109806167)
          ·
            refine ⟨13524226886663377664709251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9016151257775585109806167 13524226886663377664709251)
            ·
              refine ⟨20286340329995066497063877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13524226886663377664709251 20286340329995066497063877)
              ·
                refine ⟨3803688811874074968199477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20286340329995066497063877 3803688811874074968199477)
                ·
                  refine ⟨356595826113194528268701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803688811874074968199477 356595826113194528268701)
                  ·
                    rfl

theorem cell23_6250211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 5].length) (baseStart_6250211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250211 prefixEnd_6250211 := by exact prefixLift 6250211
  have htrace : WordTrace (prefixWord ++ tailWord_6250211) baseStart_6250211 baseEnd_6250211 := by
    simpa [prefixWord, tailWord_6250211, baseEnd_6250211] using wordTrace_append hprefix tailTrace_6250211
  have hstable : (prefixWord ++ tailWord_6250211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250211).length < 2 ^ (prefixWord ++ tailWord_6250211).sum := by decide
  have hdescent : baseEnd_6250211 < baseStart_6250211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250227 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4]
def baseStart_6250227 : Nat := 118140960795 + 6250227 * 2 ^ 59
def prefixEnd_6250227 : Nat := 4983230072969 + 3 ^ 40 * 6250227 * 2
def baseEnd_6250227 : Nat := 3209370650709222691818235

theorem tailTrace_6250227 : CollatzResearch.WordTrace tailWord_6250227 prefixEnd_6250227 3209370650709222691818235 := by
  unfold tailWord_6250227
  simp only [CollatzResearch.WordTrace]
  refine ⟨227964506727502507632372935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151976337818335005088248623 227964506727502507632372935)
  ·
    refine ⟨341946760091253761448559403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227964506727502507632372935 341946760091253761448559403)
    ·
      refine ⟨512920140136880642172839105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341946760091253761448559403 512920140136880642172839105)
      ·
        refine ⟨384690105102660481629629329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512920140136880642172839105 384690105102660481629629329)
        ·
          refine ⟨288517578826995361222221997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384690105102660481629629329 288517578826995361222221997)
          ·
            refine ⟨108194092060123260458333249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288517578826995361222221997 108194092060123260458333249)
            ·
              refine ⟨81145569045092445343749937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108194092060123260458333249 81145569045092445343749937)
              ·
                refine ⟨60859176783819334007812453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81145569045092445343749937 60859176783819334007812453)
                ·
                  refine ⟨11411095646966125126464835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60859176783819334007812453 11411095646966125126464835)
                  ·
                    refine ⟨17116643470449187689697253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411095646966125126464835 17116643470449187689697253)
                    ·
                      refine ⟨3209370650709222691818235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17116643470449187689697253 3209370650709222691818235)
                      ·
                        rfl

theorem cell23_6250227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_6250227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250227 prefixEnd_6250227 := by exact prefixLift 6250227
  have htrace : WordTrace (prefixWord ++ tailWord_6250227) baseStart_6250227 baseEnd_6250227 := by
    simpa [prefixWord, tailWord_6250227, baseEnd_6250227] using wordTrace_append hprefix tailTrace_6250227
  have hstable : (prefixWord ++ tailWord_6250227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250227).length < 2 ^ (prefixWord ++ tailWord_6250227).sum := by decide
  have hdescent : baseEnd_6250227 < baseStart_6250227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250244 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6250244 : Nat := 118140960795 + 6250244 * 2 ^ 59
def prefixEnd_6250244 : Nat := 4983230072969 + 3 ^ 40 * 6250244 * 2
def baseEnd_6250244 : Nat := 3209379379880349125305657

theorem tailTrace_6250244 : CollatzResearch.WordTrace tailWord_6250244 prefixEnd_6250244 3209379379880349125305657 := by
  unfold tailWord_6250244
  simp only [CollatzResearch.WordTrace]
  refine ⟨113982563384220459767870893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151976751178960613023827857 113982563384220459767870893)
  ·
    refine ⟨42743461269082672412951585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113982563384220459767870893 42743461269082672412951585)
    ·
      refine ⟨32057595951812004309713689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42743461269082672412951585 32057595951812004309713689)
      ·
        refine ⟨24043196963859003232285267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32057595951812004309713689 24043196963859003232285267)
        ·
          refine ⟨36064795445788504848427901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24043196963859003232285267 36064795445788504848427901)
          ·
            refine ⟨13524298292170689318160463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36064795445788504848427901 13524298292170689318160463)
            ·
              refine ⟨20286447438256033977240695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13524298292170689318160463 20286447438256033977240695)
              ·
                refine ⟨30429671157384050965861043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20286447438256033977240695 30429671157384050965861043)
                ·
                  refine ⟨45644506736076076448791565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30429671157384050965861043 45644506736076076448791565)
                  ·
                    refine ⟨17116690026028528668296837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45644506736076076448791565 17116690026028528668296837)
                    ·
                      refine ⟨3209379379880349125305657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17116690026028528668296837 3209379379880349125305657)
                      ·
                        rfl

theorem cell23_6250244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6250244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250244 prefixEnd_6250244 := by exact prefixLift 6250244
  have htrace : WordTrace (prefixWord ++ tailWord_6250244) baseStart_6250244 baseEnd_6250244 := by
    simpa [prefixWord, tailWord_6250244, baseEnd_6250244] using wordTrace_append hprefix tailTrace_6250244
  have hstable : (prefixWord ++ tailWord_6250244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250244).length < 2 ^ (prefixWord ++ tailWord_6250244).sum := by decide
  have hdescent : baseEnd_6250244 < baseStart_6250244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250264 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6250264 : Nat := 118140960795 + 6250264 * 2 ^ 59
def prefixEnd_6250264 : Nat := 4983230072969 + 3 ^ 40 * 6250264 * 2
def baseEnd_6250264 : Nat := 3209389649493439047055565

theorem tailTrace_6250264 : CollatzResearch.WordTrace tailWord_6250264 prefixEnd_6250264 3209389649493439047055565 := by
  unfold tailWord_6250264
  simp only [CollatzResearch.WordTrace]
  refine ⟨113982928114184231475734923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151977237485578975300979897 113982928114184231475734923)
  ·
    refine ⟨170974392171276347213602385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113982928114184231475734923 170974392171276347213602385)
    ·
      refine ⟨128230794128457260410201789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170974392171276347213602385 128230794128457260410201789)
      ·
        refine ⟨48086547798171472653825671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128230794128457260410201789 48086547798171472653825671)
        ·
          refine ⟨72129821697257208980738507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48086547798171472653825671 72129821697257208980738507)
          ·
            refine ⟨108194732545885813471107761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72129821697257208980738507 108194732545885813471107761)
            ·
              refine ⟨81146049409414360103330821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108194732545885813471107761 81146049409414360103330821)
              ·
                refine ⟨15214884264265192519374529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81146049409414360103330821 15214884264265192519374529)
                ·
                  refine ⟨11411163198198894389530897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15214884264265192519374529 11411163198198894389530897)
                  ·
                    refine ⟨8558372398649170792148173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11411163198198894389530897 8558372398649170792148173)
                    ·
                      refine ⟨3209389649493439047055565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558372398649170792148173 3209389649493439047055565)
                      ·
                        rfl

theorem cell23_6250264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6250264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250264 prefixEnd_6250264 := by exact prefixLift 6250264
  have htrace : WordTrace (prefixWord ++ tailWord_6250264) baseStart_6250264 baseEnd_6250264 := by
    simpa [prefixWord, tailWord_6250264, baseEnd_6250264] using wordTrace_append hprefix tailTrace_6250264
  have hstable : (prefixWord ++ tailWord_6250264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250264).length < 2 ^ (prefixWord ++ tailWord_6250264).sum := by decide
  have hdescent : baseEnd_6250264 < baseStart_6250264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250271 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 1, 4]
def baseStart_6250271 : Nat := 118140960795 + 6250271 * 2 ^ 59
def prefixEnd_6250271 : Nat := 4983230072969 + 3 ^ 40 * 6250271 * 2
def baseEnd_6250271 : Nat := 1069797747952673506556011

theorem tailTrace_6250271 : CollatzResearch.WordTrace tailWord_6250271 prefixEnd_6250271 1069797747952673506556011 := by
  unfold tailWord_6250271
  simp only [CollatzResearch.WordTrace]
  refine ⟨227966111539343103146974667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151977407692895402097983111 227966111539343103146974667)
  ·
    refine ⟨341949167309014654720462001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227966111539343103146974667 341949167309014654720462001)
    ·
      refine ⟨256461875481760991040346501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341949167309014654720462001 256461875481760991040346501)
      ·
        refine ⟨48086601652830185820064969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256461875481760991040346501 48086601652830185820064969)
        ·
          refine ⟨36064951239622639365048727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48086601652830185820064969 36064951239622639365048727)
          ·
            refine ⟨54097426859433959047573091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36064951239622639365048727 54097426859433959047573091)
            ·
              refine ⟨81146140289150938571359637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54097426859433959047573091 81146140289150938571359637)
              ·
                refine ⟨3803725326053950245532483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81146140289150938571359637 3803725326053950245532483)
                ·
                  refine ⟨5705587989080925368298725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803725326053950245532483 5705587989080925368298725)
                  ·
                    refine ⟨1069797747952673506556011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705587989080925368298725 1069797747952673506556011)
                    ·
                      rfl

theorem cell23_6250271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 4].length) (baseStart_6250271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250271 prefixEnd_6250271 := by exact prefixLift 6250271
  have htrace : WordTrace (prefixWord ++ tailWord_6250271) baseStart_6250271 baseEnd_6250271 := by
    simpa [prefixWord, tailWord_6250271, baseEnd_6250271] using wordTrace_append hprefix tailTrace_6250271
  have hstable : (prefixWord ++ tailWord_6250271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250271).length < 2 ^ (prefixWord ++ tailWord_6250271).sum := by decide
  have hdescent : baseEnd_6250271 < baseStart_6250271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250314 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_6250314 : Nat := 118140960795 + 6250314 * 2 ^ 59
def prefixEnd_6250314 : Nat := 4983230072969 + 3 ^ 40 * 6250314 * 2
def baseEnd_6250314 : Nat := 1069805107842054617143445

theorem tailTrace_6250314 : CollatzResearch.WordTrace tailWord_6250314 prefixEnd_6250314 1069805107842054617143445 := by
  unfold tailWord_6250314
  simp only [CollatzResearch.WordTrace]
  refine ⟨56991919969546830372697499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151978453252124880993859997 56991919969546830372697499)
  ·
    refine ⟨85487879954320245559046249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56991919969546830372697499 85487879954320245559046249)
    ·
      refine ⟨64115909965740184169284687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85487879954320245559046249 64115909965740184169284687)
      ·
        refine ⟨96173864948610276253927031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64115909965740184169284687 96173864948610276253927031)
        ·
          refine ⟨144260797422915414380890547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96173864948610276253927031 144260797422915414380890547)
          ·
            refine ⟨216391196134373121571335821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144260797422915414380890547 216391196134373121571335821)
            ·
              refine ⟨81146698550389920589250933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216391196134373121571335821 81146698550389920589250933)
              ·
                refine ⟨7607502989099055055242275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81146698550389920589250933 7607502989099055055242275)
                ·
                  refine ⟨11411254483648582582863413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607502989099055055242275 11411254483648582582863413)
                  ·
                    refine ⟨1069805107842054617143445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11411254483648582582863413 1069805107842054617143445)
                    ·
                      rfl

theorem cell23_6250314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_6250314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250314 prefixEnd_6250314 := by exact prefixLift 6250314
  have htrace : WordTrace (prefixWord ++ tailWord_6250314) baseStart_6250314 baseEnd_6250314 := by
    simpa [prefixWord, tailWord_6250314, baseEnd_6250314] using wordTrace_append hprefix tailTrace_6250314
  have hstable : (prefixWord ++ tailWord_6250314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250314).length < 2 ^ (prefixWord ++ tailWord_6250314).sum := by decide
  have hdescent : baseEnd_6250314 < baseStart_6250314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250321 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_6250321 : Nat := 118140960795 + 6250321 * 2 ^ 59
def prefixEnd_6250321 : Nat := 4983230072969 + 3 ^ 40 * 6250321 * 2
def baseEnd_6250321 : Nat := 3209418917890745324042803

theorem tailTrace_6250321 : CollatzResearch.WordTrace tailWord_6250321 prefixEnd_6250321 3209418917890745324042803 := by
  unfold tailWord_6250321
  simp only [CollatzResearch.WordTrace]
  refine ⟨227967935189161961686294817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151978623459441307790863211 227967935189161961686294817)
  ·
    refine ⟨170975951391871471264721113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227967935189161961686294817 170975951391871471264721113)
    ·
      refine ⟨128231963543903603448540835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170975951391871471264721113 128231963543903603448540835)
      ·
        refine ⟨192347945315855405172811253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128231963543903603448540835 192347945315855405172811253)
        ·
          refine ⟨18032619873361444234951055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192347945315855405172811253 18032619873361444234951055)
          ·
            refine ⟨27048929810042166352426583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18032619873361444234951055 27048929810042166352426583)
            ·
              refine ⟨40573394715063249528639875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27048929810042166352426583 40573394715063249528639875)
              ·
                refine ⟨60860092072594874292959813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40573394715063249528639875 60860092072594874292959813)
                ·
                  refine ⟨11411267263611538929929965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60860092072594874292959813 11411267263611538929929965)
                  ·
                    refine ⟨4279225223854327098723737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11411267263611538929929965 4279225223854327098723737)
                    ·
                      refine ⟨3209418917890745324042803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279225223854327098723737 3209418917890745324042803)
                      ·
                        rfl

theorem cell23_6250321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_6250321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250321 prefixEnd_6250321 := by exact prefixLift 6250321
  have htrace : WordTrace (prefixWord ++ tailWord_6250321) baseStart_6250321 baseEnd_6250321 := by
    simpa [prefixWord, tailWord_6250321, baseEnd_6250321] using wordTrace_append hprefix tailTrace_6250321
  have hstable : (prefixWord ++ tailWord_6250321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250321).length < 2 ^ (prefixWord ++ tailWord_6250321).sum := by decide
  have hdescent : baseEnd_6250321 < baseStart_6250321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250344 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6250344 : Nat := 118140960795 + 6250344 * 2 ^ 59
def prefixEnd_6250344 : Nat := 4983230072969 + 3 ^ 40 * 6250344 * 2
def baseEnd_6250344 : Nat := 1069810242648599578018399

theorem tailTrace_6250344 : CollatzResearch.WordTrace tailWord_6250344 prefixEnd_6250344 1069810242648599578018399 := by
  unfold tailWord_6250344
  simp only [CollatzResearch.WordTrace]
  refine ⟨113984387034039318307191043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151979182712052424409588057 113984387034039318307191043)
  ·
    refine ⟨170976580551058977460786565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113984387034039318307191043 170976580551058977460786565)
    ·
      refine ⟨32058108853323558273897481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170976580551058977460786565 32058108853323558273897481)
      ·
        refine ⟨24043581639992668705423111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32058108853323558273897481 24043581639992668705423111)
        ·
          refine ⟨36065372459989003058134667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24043581639992668705423111 36065372459989003058134667)
          ·
            refine ⟨54098058689983504587202001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36065372459989003058134667 54098058689983504587202001)
            ·
              refine ⟨40573544017487628440401501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54098058689983504587202001 40573544017487628440401501)
              ·
                refine ⟨15215079006557860665150563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40573544017487628440401501 15215079006557860665150563)
                ·
                  refine ⟨22822618509836790997725845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15215079006557860665150563 22822618509836790997725845)
                  ·
                    refine ⟨1069810242648599578018399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22822618509836790997725845 1069810242648599578018399)
                    ·
                      rfl

theorem cell23_6250344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6250344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250344 prefixEnd_6250344 := by exact prefixLift 6250344
  have htrace : WordTrace (prefixWord ++ tailWord_6250344) baseStart_6250344 baseEnd_6250344 := by
    simpa [prefixWord, tailWord_6250344, baseEnd_6250344] using wordTrace_append hprefix tailTrace_6250344
  have hstable : (prefixWord ++ tailWord_6250344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250344).length < 2 ^ (prefixWord ++ tailWord_6250344).sum := by decide
  have hdescent : baseEnd_6250344 < baseStart_6250344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250371 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 5]
def baseStart_6250371 : Nat := 118140960795 + 6250371 * 2 ^ 59
def prefixEnd_6250371 : Nat := 4983230072969 + 3 ^ 40 * 6250371 * 2
def baseEnd_6250371 : Nat := 3209444591923470128417573

theorem tailTrace_6250371 : CollatzResearch.WordTrace tailWord_6250371 prefixEnd_6250371 3209444591923470128417573 := by
  unfold tailWord_6250371
  simp only [CollatzResearch.WordTrace]
  refine ⟨227969758838980820225614967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151979839225987213483743311 227969758838980820225614967)
  ·
    refine ⟨341954638258471230338422451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227969758838980820225614967 341954638258471230338422451)
    ·
      refine ⟨512931957387706845507633677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341954638258471230338422451 512931957387706845507633677)
      ·
        refine ⟨192349484020390067065362629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512931957387706845507633677 192349484020390067065362629)
        ·
          refine ⟨36065528253823137574755493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192349484020390067065362629 36065528253823137574755493)
          ·
            refine ⟨6762286547591838295266655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36065528253823137574755493 6762286547591838295266655)
            ·
              refine ⟨10143429821387757442899983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762286547591838295266655 10143429821387757442899983)
              ·
                refine ⟨15215144732081636164349975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143429821387757442899983 15215144732081636164349975)
                ·
                  refine ⟨22822717098122454246524963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15215144732081636164349975 22822717098122454246524963)
                  ·
                    refine ⟨34234075647183681369787445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22822717098122454246524963 34234075647183681369787445)
                    ·
                      refine ⟨3209444591923470128417573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34234075647183681369787445 3209444591923470128417573)
                      ·
                        rfl

theorem cell23_6250371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_6250371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250371 prefixEnd_6250371 := by exact prefixLift 6250371
  have htrace : WordTrace (prefixWord ++ tailWord_6250371) baseStart_6250371 baseEnd_6250371 := by
    simpa [prefixWord, tailWord_6250371, baseEnd_6250371] using wordTrace_append hprefix tailTrace_6250371
  have hstable : (prefixWord ++ tailWord_6250371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250371).length < 2 ^ (prefixWord ++ tailWord_6250371).sum := by decide
  have hdescent : baseEnd_6250371 < baseStart_6250371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250582 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6250582 : Nat := 118140960795 + 6250582 * 2 ^ 59
def prefixEnd_6250582 : Nat := 4983230072969 + 3 ^ 40 * 6250582 * 2
def baseEnd_6250582 : Nat := 3209552936341568802879103

theorem tailTrace_6250582 : CollatzResearch.WordTrace tailWord_6250582 prefixEnd_6250582 3209552936341568802879103 := by
  unfold tailWord_6250582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248590915076025203846625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151984969760810935507697333 14248590915076025203846625)
  ·
    refine ⟨10686443186307018902884969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14248590915076025203846625 10686443186307018902884969)
    ·
      refine ⟨8014832389730264177163727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10686443186307018902884969 8014832389730264177163727)
      ·
        refine ⟨12022248584595396265745591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014832389730264177163727 12022248584595396265745591)
        ·
          refine ⟨18033372876893094398618387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022248584595396265745591 18033372876893094398618387)
          ·
            refine ⟨27050059315339641597927581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033372876893094398618387 27050059315339641597927581)
            ·
              refine ⟨10143772243252365599222843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27050059315339641597927581 10143772243252365599222843)
              ·
                refine ⟨15215658364878548398834265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143772243252365599222843 15215658364878548398834265)
                ·
                  refine ⟨11411743773658911299125699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15215658364878548398834265 11411743773658911299125699)
                  ·
                    refine ⟨17117615660488366948688549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411743773658911299125699 17117615660488366948688549)
                    ·
                      refine ⟨3209552936341568802879103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17117615660488366948688549 3209552936341568802879103)
                      ·
                        rfl

theorem cell23_6250582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6250582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250582 prefixEnd_6250582 := by exact prefixLift 6250582
  have htrace : WordTrace (prefixWord ++ tailWord_6250582) baseStart_6250582 baseEnd_6250582 := by
    simpa [prefixWord, tailWord_6250582, baseEnd_6250582] using wordTrace_append hprefix tailTrace_6250582
  have hstable : (prefixWord ++ tailWord_6250582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250582).length < 2 ^ (prefixWord ++ tailWord_6250582).sum := by decide
  have hdescent : baseEnd_6250582 < baseStart_6250582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250615 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_6250615 : Nat := 118140960795 + 6250615 * 2 ^ 59
def prefixEnd_6250615 : Nat := 4983230072969 + 3 ^ 40 * 6250615 * 2
def baseEnd_6250615 : Nat := 3209569881203167173766451

theorem tailTrace_6250615 : CollatzResearch.WordTrace tailWord_6250615 prefixEnd_6250615 3209569881203167173766451 := by
  unfold tailWord_6250615
  simp only [CollatzResearch.WordTrace]
  refine ⟨227978658250096849897497299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151985772166731233264998199 227978658250096849897497299)
  ·
    refine ⟨341967987375145274846245949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227978658250096849897497299 341967987375145274846245949)
    ·
      refine ⟨128237995265679478067342231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341967987375145274846245949 128237995265679478067342231)
      ·
        refine ⟨192356992898519217101013347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128237995265679478067342231 192356992898519217101013347)
        ·
          refine ⟨288535489347778825651520021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192356992898519217101013347 288535489347778825651520021)
          ·
            refine ⟨13525101063177132452415001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 288535489347778825651520021 13525101063177132452415001)
            ·
              refine ⟨10143825797382849339311251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13525101063177132452415001 10143825797382849339311251)
              ·
                refine ⟨15215738696074274008966877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143825797382849339311251 15215738696074274008966877)
                ·
                  refine ⟨5705902011027852753362579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15215738696074274008966877 5705902011027852753362579)
                  ·
                    refine ⟨8558853016541779130043869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705902011027852753362579 8558853016541779130043869)
                    ·
                      refine ⟨3209569881203167173766451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558853016541779130043869 3209569881203167173766451)
                      ·
                        rfl

theorem cell23_6250615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_6250615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250615 prefixEnd_6250615 := by exact prefixLift 6250615
  have htrace : WordTrace (prefixWord ++ tailWord_6250615) baseStart_6250615 baseEnd_6250615 := by
    simpa [prefixWord, tailWord_6250615, baseEnd_6250615] using wordTrace_append hprefix tailTrace_6250615
  have hstable : (prefixWord ++ tailWord_6250615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250615).length < 2 ^ (prefixWord ++ tailWord_6250615).sum := by decide
  have hdescent : baseEnd_6250615 < baseStart_6250615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250641 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_6250641 : Nat := 118140960795 + 6250641 * 2 ^ 59
def prefixEnd_6250641 : Nat := 4983230072969 + 3 ^ 40 * 6250641 * 2
def baseEnd_6250641 : Nat := 3209583231700184072041331

theorem tailTrace_6250641 : CollatzResearch.WordTrace tailWord_6250641 prefixEnd_6250641 3209583231700184072041331 := by
  unfold tailWord_6250641
  simp only [CollatzResearch.WordTrace]
  refine ⟨227979606548002656337943777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151986404365335104225295851 227979606548002656337943777)
  ·
    refine ⟨170984704911001992253457833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227979606548002656337943777 170984704911001992253457833)
    ·
      refine ⟨128238528683251494190093375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170984704911001992253457833 128238528683251494190093375)
      ·
        refine ⟨192357793024877241285140063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128238528683251494190093375 192357793024877241285140063)
        ·
          refine ⟨288536689537315861927710095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192357793024877241285140063 288536689537315861927710095)
          ·
            refine ⟨432805034305973792891565143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288536689537315861927710095 432805034305973792891565143)
            ·
              refine ⟨649207551458960689337347715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432805034305973792891565143 649207551458960689337347715)
              ·
                refine ⟨973811327188441034006021573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649207551458960689337347715 973811327188441034006021573)
                ·
                  refine ⟨182589623847832693876129045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973811327188441034006021573 182589623847832693876129045)
                  ·
                    refine ⟨8558888617867157525443549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182589623847832693876129045 8558888617867157525443549)
                    ·
                      refine ⟨3209583231700184072041331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558888617867157525443549 3209583231700184072041331)
                      ·
                        rfl

theorem cell23_6250641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_6250641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250641 prefixEnd_6250641 := by exact prefixLift 6250641
  have htrace : WordTrace (prefixWord ++ tailWord_6250641) baseStart_6250641 baseEnd_6250641 := by
    simpa [prefixWord, tailWord_6250641, baseEnd_6250641] using wordTrace_append hprefix tailTrace_6250641
  have hstable : (prefixWord ++ tailWord_6250641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250641).length < 2 ^ (prefixWord ++ tailWord_6250641).sum := by decide
  have hdescent : baseEnd_6250641 < baseStart_6250641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250655 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6250655 : Nat := 118140960795 + 6250655 * 2 ^ 59
def prefixEnd_6250655 : Nat := 4983230072969 + 3 ^ 40 * 6250655 * 2
def baseEnd_6250655 : Nat := 3209590420429347017266267

theorem tailTrace_6250655 : CollatzResearch.WordTrace tailWord_6250655 prefixEnd_6250655 3209590420429347017266267 := by
  unfold tailWord_6250655
  simp only [CollatzResearch.WordTrace]
  refine ⟨227980117169951936728953419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151986744779967957819302279 227980117169951936728953419)
  ·
    refine ⟨341970175754927905093430129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227980117169951936728953419 341970175754927905093430129)
    ·
      refine ⟨256477631816195928820072597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341970175754927905093430129 256477631816195928820072597)
      ·
        refine ⟨12022388991384184163440903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256477631816195928820072597 12022388991384184163440903)
        ·
          refine ⟨18033583487076276245161355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022388991384184163440903 18033583487076276245161355)
          ·
            refine ⟨27050375230614414367742033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033583487076276245161355 27050375230614414367742033)
            ·
              refine ⟨20287781422960810775806525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27050375230614414367742033 20287781422960810775806525)
              ·
                refine ⟨7607918033610304040927447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20287781422960810775806525 7607918033610304040927447)
                ·
                  refine ⟨11411877050415456061391171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607918033610304040927447 11411877050415456061391171)
                  ·
                    refine ⟨17117815575623184092086757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411877050415456061391171 17117815575623184092086757)
                    ·
                      refine ⟨3209590420429347017266267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17117815575623184092086757 3209590420429347017266267)
                      ·
                        rfl

theorem cell23_6250655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6250655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250655 prefixEnd_6250655 := by exact prefixLift 6250655
  have htrace : WordTrace (prefixWord ++ tailWord_6250655) baseStart_6250655 baseEnd_6250655 := by
    simpa [prefixWord, tailWord_6250655, baseEnd_6250655] using wordTrace_append hprefix tailTrace_6250655
  have hstable : (prefixWord ++ tailWord_6250655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250655).length < 2 ^ (prefixWord ++ tailWord_6250655).sum := by decide
  have hdescent : baseEnd_6250655 < baseStart_6250655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250666 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6250666 : Nat := 118140960795 + 6250666 * 2 ^ 59
def prefixEnd_6250666 : Nat := 4983230072969 + 3 ^ 40 * 6250666 * 2
def baseEnd_6250666 : Nat := 3209596068716546474228717

theorem tailTrace_6250666 : CollatzResearch.WordTrace tailWord_6250666 prefixEnd_6250666 3209596068716546474228717 := by
  unfold tailWord_6250666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995129593228021401900963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151987012248608057071735901 56995129593228021401900963)
  ·
    refine ⟨85492694389842032102851445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56995129593228021401900963 85492694389842032102851445)
    ·
      refine ⟨8014940099047690509642323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85492694389842032102851445 8014940099047690509642323)
      ·
        refine ⟨12022410148571535764463485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014940099047690509642323 12022410148571535764463485)
        ·
          refine ⟨4508403805714325911673807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12022410148571535764463485 4508403805714325911673807)
          ·
            refine ⟨6762605708571488867510711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508403805714325911673807 6762605708571488867510711)
            ·
              refine ⟨10143908562857233301266067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762605708571488867510711 10143908562857233301266067)
              ·
                refine ⟨15215862844285849951899101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143908562857233301266067 15215862844285849951899101)
                ·
                  refine ⟨5705948566607193731962163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15215862844285849951899101 5705948566607193731962163)
                  ·
                    refine ⟨8558922849910790597943245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705948566607193731962163 8558922849910790597943245)
                    ·
                      refine ⟨3209596068716546474228717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558922849910790597943245 3209596068716546474228717)
                      ·
                        rfl

theorem cell23_6250666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6250666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250666 prefixEnd_6250666 := by exact prefixLift 6250666
  have htrace : WordTrace (prefixWord ++ tailWord_6250666) baseStart_6250666 baseEnd_6250666 := by
    simpa [prefixWord, tailWord_6250666, baseEnd_6250666] using wordTrace_append hprefix tailTrace_6250666
  have hstable : (prefixWord ++ tailWord_6250666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250666).length < 2 ^ (prefixWord ++ tailWord_6250666).sum := by decide
  have hdescent : baseEnd_6250666 < baseStart_6250666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250681 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6250681 : Nat := 118140960795 + 6250681 * 2 ^ 59
def prefixEnd_6250681 : Nat := 4983230072969 + 3 ^ 40 * 6250681 * 2
def baseEnd_6250681 : Nat := 3209603770926363915541147

theorem tailTrace_6250681 : CollatzResearch.WordTrace tailWord_6250681 prefixEnd_6250681 3209603770926363915541147 := by
  unfold tailWord_6250681
  simp only [CollatzResearch.WordTrace]
  refine ⟨227981065467857743169399897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151987376978571828779599931 227981065467857743169399897)
  ·
    refine ⟨170985799100893307377049923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227981065467857743169399897 170985799100893307377049923)
    ·
      refine ⟨256478698651339961065574885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170985799100893307377049923 256478698651339961065574885)
      ·
        refine ⟨48089755997126242699795291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256478698651339961065574885 48089755997126242699795291)
        ·
          refine ⟨72134633995689364049692937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48089755997126242699795291 72134633995689364049692937)
          ·
            refine ⟨54100975496767023037269703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72134633995689364049692937 54100975496767023037269703)
            ·
              refine ⟨81151463245150534555904555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54100975496767023037269703 81151463245150534555904555)
              ·
                refine ⟨121727194867725801833856833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81151463245150534555904555 121727194867725801833856833)
                ·
                  refine ⟨91295396150794351375392625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121727194867725801833856833 91295396150794351375392625)
                  ·
                    refine ⟨68471547113095763531544469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91295396150794351375392625 68471547113095763531544469)
                    ·
                      refine ⟨3209603770926363915541147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68471547113095763531544469 3209603770926363915541147)
                      ·
                        rfl

theorem cell23_6250681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6250681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250681 prefixEnd_6250681 := by exact prefixLift 6250681
  have htrace : WordTrace (prefixWord ++ tailWord_6250681) baseStart_6250681 baseEnd_6250681 := by
    simpa [prefixWord, tailWord_6250681, baseEnd_6250681] using wordTrace_append hprefix tailTrace_6250681
  have hstable : (prefixWord ++ tailWord_6250681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250681).length < 2 ^ (prefixWord ++ tailWord_6250681).sum := by decide
  have hdescent : baseEnd_6250681 < baseStart_6250681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250689 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6250689 : Nat := 118140960795 + 6250689 * 2 ^ 59
def prefixEnd_6250689 : Nat := 4983230072969 + 3 ^ 40 * 6250689 * 2
def baseEnd_6250689 : Nat := 3209607878771599884241111

theorem tailTrace_6250689 : CollatzResearch.WordTrace tailWord_6250689 prefixEnd_6250689 3209607878771599884241111 := by
  unfold tailWord_6250689
  simp only [CollatzResearch.WordTrace]
  refine ⟨227981357251828760535691121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151987571501219173690460747 227981357251828760535691121)
  ·
    refine ⟨170986017938871570401768341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227981357251828760535691121 170986017938871570401768341)
    ·
      refine ⟨8014969590884604862582891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170986017938871570401768341 8014969590884604862582891)
      ·
        refine ⟨12022454386326907293874337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014969590884604862582891 12022454386326907293874337)
        ·
          refine ⟨9016840789745180470405753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12022454386326907293874337 9016840789745180470405753)
          ·
            refine ⟨6762630592308885352804315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9016840789745180470405753 6762630592308885352804315)
            ·
              refine ⟨10143945888463328029206473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762630592308885352804315 10143945888463328029206473)
              ·
                refine ⟨7607959416347496021904855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10143945888463328029206473 7607959416347496021904855)
                ·
                  refine ⟨11411939124521244032857283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607959416347496021904855 11411939124521244032857283)
                  ·
                    refine ⟨17117908686781866049285925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411939124521244032857283 17117908686781866049285925)
                    ·
                      refine ⟨3209607878771599884241111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17117908686781866049285925 3209607878771599884241111)
                      ·
                        rfl

theorem cell23_6250689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6250689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250689 prefixEnd_6250689 := by exact prefixLift 6250689
  have htrace : WordTrace (prefixWord ++ tailWord_6250689) baseStart_6250689 baseEnd_6250689 := by
    simpa [prefixWord, tailWord_6250689, baseEnd_6250689] using wordTrace_append hprefix tailTrace_6250689
  have hstable : (prefixWord ++ tailWord_6250689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250689).length < 2 ^ (prefixWord ++ tailWord_6250689).sum := by decide
  have hdescent : baseEnd_6250689 < baseStart_6250689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250692 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_6250692 : Nat := 118140960795 + 6250692 * 2 ^ 59
def prefixEnd_6250692 : Nat := 4983230072969 + 3 ^ 40 * 6250692 * 2
def baseEnd_6250692 : Nat := 3209609419213563372503597

theorem tailTrace_6250692 : CollatzResearch.WordTrace tailWord_6250692 prefixEnd_6250692 3209609419213563372503597 := by
  unfold tailWord_6250692
  simp only [CollatzResearch.WordTrace]
  refine ⟨113990733335408946024025165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151987644447211928032033553 113990733335408946024025165)
  ·
    refine ⟨42746525000778354759009437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113990733335408946024025165 42746525000778354759009437)
    ·
      refine ⟨16029946875291883034628539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42746525000778354759009437 16029946875291883034628539)
      ·
        refine ⟨24044920312937824551942809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16029946875291883034628539 24044920312937824551942809)
        ·
          refine ⟨18033690234703368413957107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24044920312937824551942809 18033690234703368413957107)
          ·
            refine ⟨27050535352055052620935661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033690234703368413957107 27050535352055052620935661)
            ·
              refine ⟨10143950757020644732850873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27050535352055052620935661 10143950757020644732850873)
              ·
                refine ⟨7607963067765483549638155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10143950757020644732850873 7607963067765483549638155)
                ·
                  refine ⟨11411944601648225324457233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607963067765483549638155 11411944601648225324457233)
                  ·
                    refine ⟨8558958451236168993342925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11411944601648225324457233 8558958451236168993342925)
                    ·
                      refine ⟨3209609419213563372503597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558958451236168993342925 3209609419213563372503597)
                      ·
                        rfl

theorem cell23_6250692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_6250692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250692 prefixEnd_6250692 := by exact prefixLift 6250692
  have htrace : WordTrace (prefixWord ++ tailWord_6250692) baseStart_6250692 baseEnd_6250692 := by
    simpa [prefixWord, tailWord_6250692, baseEnd_6250692] using wordTrace_append hprefix tailTrace_6250692
  have hstable : (prefixWord ++ tailWord_6250692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250692).length < 2 ^ (prefixWord ++ tailWord_6250692).sum := by decide
  have hdescent : baseEnd_6250692 < baseStart_6250692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250709 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6250709 : Nat := 118140960795 + 6250709 * 2 ^ 59
def prefixEnd_6250709 : Nat := 4983230072969 + 3 ^ 40 * 6250709 * 2
def baseEnd_6250709 : Nat := 3209618148384689805991019

theorem tailTrace_6250709 : CollatzResearch.WordTrace tailWord_6250709 prefixEnd_6250709 3209618148384689805991019 := by
  unfold tailWord_6250709
  simp only [CollatzResearch.WordTrace]
  refine ⟨227982086711756303951419181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151988057807837535967612787 227982086711756303951419181)
  ·
    refine ⟨85493282516908613981782193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227982086711756303951419181 85493282516908613981782193)
    ·
      refine ⟨64119961887681460486336645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85493282516908613981782193 64119961887681460486336645)
      ·
        refine ⟨12022492853940273841188121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64119961887681460486336645 12022492853940273841188121)
        ·
          refine ⟨9016869640455205380891091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12022492853940273841188121 9016869640455205380891091)
          ·
            refine ⟨13525304460682808071336637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9016869640455205380891091 13525304460682808071336637)
            ·
              refine ⟨5071989172756053026751239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13525304460682808071336637 5071989172756053026751239)
              ·
                refine ⟨7607983759134079540126859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071989172756053026751239 7607983759134079540126859)
                ·
                  refine ⟨11411975638701119310190289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607983759134079540126859 11411975638701119310190289)
                  ·
                    refine ⟨8558981729025839482642717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11411975638701119310190289 8558981729025839482642717)
                    ·
                      refine ⟨3209618148384689805991019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8558981729025839482642717 3209618148384689805991019)
                      ·
                        rfl

theorem cell23_6250709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6250709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250709 prefixEnd_6250709 := by exact prefixLift 6250709
  have htrace : WordTrace (prefixWord ++ tailWord_6250709) baseStart_6250709 baseEnd_6250709 := by
    simpa [prefixWord, tailWord_6250709, baseEnd_6250709] using wordTrace_append hprefix tailTrace_6250709
  have hstable : (prefixWord ++ tailWord_6250709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250709).length < 2 ^ (prefixWord ++ tailWord_6250709).sum := by decide
  have hdescent : baseEnd_6250709 < baseStart_6250709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250728 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6250728 : Nat := 118140960795 + 6250728 * 2 ^ 59
def prefixEnd_6250728 : Nat := 4983230072969 + 3 ^ 40 * 6250728 * 2
def baseEnd_6250728 : Nat := 3209627904517125231653431

theorem tailTrace_6250728 : CollatzResearch.WordTrace tailWord_6250728 prefixEnd_6250728 3209627904517125231653431 := by
  unfold tailWord_6250728
  simp only [CollatzResearch.WordTrace]
  refine ⟨113991389849343735098180419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151988519799124980130907225 113991389849343735098180419)
  ·
    refine ⟨170987084774015602647270629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113991389849343735098180419 170987084774015602647270629)
    ·
      refine ⟨32060078395127925496363243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170987084774015602647270629 32060078395127925496363243)
      ·
        refine ⟨48090117592691888244544865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32060078395127925496363243 48090117592691888244544865)
        ·
          refine ⟨36067588194518916183408649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48090117592691888244544865 36067588194518916183408649)
          ·
            refine ⟨27050691145889187137556487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36067588194518916183408649 27050691145889187137556487)
            ·
              refine ⟨40576036718833780706334731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27050691145889187137556487 40576036718833780706334731)
              ·
                refine ⟨60864055078250671059502097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40576036718833780706334731 60864055078250671059502097)
                ·
                  refine ⟨45648041308688003294626573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60864055078250671059502097 45648041308688003294626573)
                  ·
                    refine ⟨17118015490758001235484965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45648041308688003294626573 17118015490758001235484965)
                    ·
                      refine ⟨3209627904517125231653431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17118015490758001235484965 3209627904517125231653431)
                      ·
                        rfl

theorem cell23_6250728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6250728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250728 prefixEnd_6250728 := by exact prefixLift 6250728
  have htrace : WordTrace (prefixWord ++ tailWord_6250728) baseStart_6250728 baseEnd_6250728 := by
    simpa [prefixWord, tailWord_6250728, baseEnd_6250728] using wordTrace_append hprefix tailTrace_6250728
  have hstable : (prefixWord ++ tailWord_6250728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250728).length < 2 ^ (prefixWord ++ tailWord_6250728).sum := by decide
  have hdescent : baseEnd_6250728 < baseStart_6250728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250738 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_6250738 : Nat := 118140960795 + 6250738 * 2 ^ 59
def prefixEnd_6250738 : Nat := 4983230072969 + 3 ^ 40 * 6250738 * 2
def baseEnd_6250738 : Nat := 1069877679774556730842795

theorem tailTrace_6250738 : CollatzResearch.WordTrace tailWord_6250738 prefixEnd_6250738 1069877679774556730842795 := by
  unfold tailWord_6250738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995786107162810476056217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151988762952434161269483245 56995786107162810476056217)
  ·
    refine ⟨42746839580372107857042163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56995786107162810476056217 42746839580372107857042163)
    ·
      refine ⟨64120259370558161785563245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42746839580372107857042163 64120259370558161785563245)
      ·
        refine ⟨24045097263959310669586217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64120259370558161785563245 24045097263959310669586217)
        ·
          refine ⟨18033822947969483002189663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24045097263959310669586217 18033822947969483002189663)
          ·
            refine ⟨27050734421954224503284495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033822947969483002189663 27050734421954224503284495)
            ·
              refine ⟨40576101632931336754926743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27050734421954224503284495 40576101632931336754926743)
              ·
                refine ⟨60864152449397005132390115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40576101632931336754926743 60864152449397005132390115)
                ·
                  refine ⟨91296228674095507698585173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60864152449397005132390115 91296228674095507698585173)
                  ·
                    refine ⟨1069877679774556730842795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91296228674095507698585173 1069877679774556730842795)
                    ·
                      rfl

theorem cell23_6250738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_6250738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250738 prefixEnd_6250738 := by exact prefixLift 6250738
  have htrace : WordTrace (prefixWord ++ tailWord_6250738) baseStart_6250738 baseEnd_6250738 := by
    simpa [prefixWord, tailWord_6250738, baseEnd_6250738] using wordTrace_append hprefix tailTrace_6250738
  have hstable : (prefixWord ++ tailWord_6250738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250738).length < 2 ^ (prefixWord ++ tailWord_6250738).sum := by decide
  have hdescent : baseEnd_6250738 < baseStart_6250738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250785 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 5]
def baseStart_6250785 : Nat := 118140960795 + 6250785 * 2 ^ 59
def prefixEnd_6250785 : Nat := 4983230072969 + 3 ^ 40 * 6250785 * 2
def baseEnd_6250785 : Nat := 356628574768270167626741

theorem tailTrace_6250785 : CollatzResearch.WordTrace tailWord_6250785 prefixEnd_6250785 356628574768270167626741 := by
  unfold tailWord_6250785
  simp only [CollatzResearch.WordTrace]
  refine ⟨227984858659480968931185809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151989905772987312620790539 227984858659480968931185809)
  ·
    refine ⟨170988643994610726698389357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227984858659480968931185809 170988643994610726698389357)
    ·
      refine ⟨64120741497979022511896009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170988643994610726698389357 64120741497979022511896009)
      ·
        refine ⟨48090556123484266883922007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64120741497979022511896009 48090556123484266883922007)
        ·
          refine ⟨72135834185226400325883011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48090556123484266883922007 72135834185226400325883011)
          ·
            refine ⟨108203751277839600488824517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72135834185226400325883011 108203751277839600488824517)
            ·
              refine ⟨20288203364594925091654597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108203751277839600488824517 20288203364594925091654597)
              ·
                refine ⟨3804038130861548454685237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20288203364594925091654597 3804038130861548454685237)
                ·
                  refine ⟨356628574768270167626741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3804038130861548454685237 356628574768270167626741)
                  ·
                    rfl

theorem cell23_6250785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 5].length) (baseStart_6250785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250785 prefixEnd_6250785 := by exact prefixLift 6250785
  have htrace : WordTrace (prefixWord ++ tailWord_6250785) baseStart_6250785 baseEnd_6250785 := by
    simpa [prefixWord, tailWord_6250785, baseEnd_6250785] using wordTrace_append hprefix tailTrace_6250785
  have hstable : (prefixWord ++ tailWord_6250785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250785).length < 2 ^ (prefixWord ++ tailWord_6250785).sum := by decide
  have hdescent : baseEnd_6250785 < baseStart_6250785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250835 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 2, 4, 2]
def baseStart_6250835 : Nat := 118140960795 + 6250835 * 2 ^ 59
def prefixEnd_6250835 : Nat := 4983230072969 + 3 ^ 40 * 6250835 * 2
def baseEnd_6250835 : Nat := 3209682846947156313015439

theorem tailTrace_6250835 : CollatzResearch.WordTrace tailWord_6250835 prefixEnd_6250835 3209682846947156313015439 := by
  unfold tailWord_6250835
  simp only [CollatzResearch.WordTrace]
  refine ⟨227986682309299827470505959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151991121539533218313670639 227986682309299827470505959)
  ·
    refine ⟨341980023463949741205758939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227986682309299827470505959 341980023463949741205758939)
    ·
      refine ⟨512970035195924611808638409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341980023463949741205758939 512970035195924611808638409)
      ·
        refine ⟨384727526396943458856478807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512970035195924611808638409 384727526396943458856478807)
        ·
          refine ⟨577091289595415188284718211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384727526396943458856478807 577091289595415188284718211)
          ·
            refine ⟨865636934393122782427077317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577091289595415188284718211 865636934393122782427077317)
            ·
              refine ⟨162306925198710521705076997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 865636934393122782427077317 162306925198710521705076997)
              ·
                refine ⟨30432548474758222819701937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162306925198710521705076997 30432548474758222819701937)
                ·
                  refine ⟨22824411356068667114776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30432548474758222819701937 22824411356068667114776453)
                  ·
                    refine ⟨4279577129262875084020585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22824411356068667114776453 4279577129262875084020585)
                    ·
                      refine ⟨3209682846947156313015439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279577129262875084020585 3209682846947156313015439)
                      ·
                        rfl

theorem cell23_6250835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4, 2].length) (baseStart_6250835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250835 prefixEnd_6250835 := by exact prefixLift 6250835
  have htrace : WordTrace (prefixWord ++ tailWord_6250835) baseStart_6250835 baseEnd_6250835 := by
    simpa [prefixWord, tailWord_6250835, baseEnd_6250835] using wordTrace_append hprefix tailTrace_6250835
  have hstable : (prefixWord ++ tailWord_6250835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250835).length < 2 ^ (prefixWord ++ tailWord_6250835).sum := by decide
  have hdescent : baseEnd_6250835 < baseStart_6250835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250919 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_6250919 : Nat := 118140960795 + 6250919 * 2 ^ 59
def prefixEnd_6250919 : Nat := 4983230072969 + 3 ^ 40 * 6250919 * 2
def baseEnd_6250919 : Nat := 3209725979322133984365053

theorem tailTrace_6250919 : CollatzResearch.WordTrace tailWord_6250919 prefixEnd_6250919 3209725979322133984365053 := by
  unfold tailWord_6250919
  simp only [CollatzResearch.WordTrace]
  refine ⟨227989746040995509816563811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151993164027330339877709207 227989746040995509816563811)
  ·
    refine ⟨341984619061493264724845717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227989746040995509816563811 341984619061493264724845717)
    ·
      refine ⟨16030529018507496783977143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 341984619061493264724845717 16030529018507496783977143)
      ·
        refine ⟨24045793527761245175965715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16030529018507496783977143 24045793527761245175965715)
        ·
          refine ⟨36068690291641867763948573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24045793527761245175965715 36068690291641867763948573)
          ·
            refine ⟨13525758859365700411480715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36068690291641867763948573 13525758859365700411480715)
            ·
              refine ⟨20288638289048550617221073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525758859365700411480715 20288638289048550617221073)
              ·
                refine ⟨15216478716786412962915805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20288638289048550617221073 15216478716786412962915805)
                ·
                  refine ⟨5706179518794904861093427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15216478716786412962915805 5706179518794904861093427)
                  ·
                    refine ⟨8559269278192357291640141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5706179518794904861093427 8559269278192357291640141)
                    ·
                      refine ⟨3209725979322133984365053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559269278192357291640141 3209725979322133984365053)
                      ·
                        rfl

theorem cell23_6250919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_6250919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250919 prefixEnd_6250919 := by exact prefixLift 6250919
  have htrace : WordTrace (prefixWord ++ tailWord_6250919) baseStart_6250919 baseEnd_6250919 := by
    simpa [prefixWord, tailWord_6250919, baseEnd_6250919] using wordTrace_append hprefix tailTrace_6250919
  have hstable : (prefixWord ++ tailWord_6250919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250919).length < 2 ^ (prefixWord ++ tailWord_6250919).sum := by decide
  have hdescent : baseEnd_6250919 < baseStart_6250919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250929 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6250929 : Nat := 118140960795 + 6250929 * 2 ^ 59
def prefixEnd_6250929 : Nat := 4983230072969 + 3 ^ 40 * 6250929 * 2
def baseEnd_6250929 : Nat := 3209731114128678945240007

theorem tailTrace_6250929 : CollatzResearch.WordTrace tailWord_6250929 prefixEnd_6250929 3209731114128678945240007 := by
  unfold tailWord_6250929
  simp only [CollatzResearch.WordTrace]
  refine ⟨227990110770959281524427841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151993407180639521016285227 227990110770959281524427841)
  ·
    refine ⟨170992583078219461143320881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227990110770959281524427841 170992583078219461143320881)
    ·
      refine ⟨128244437308664595857490661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170992583078219461143320881 128244437308664595857490661)
      ·
        refine ⟨24045831995374611723279499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128244437308664595857490661 24045831995374611723279499)
        ·
          refine ⟨36068747993061917584919249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24045831995374611723279499 36068747993061917584919249)
          ·
            refine ⟨27051560994796438188689437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36068747993061917584919249 27051560994796438188689437)
            ·
              refine ⟨10144335373048664320758539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27051560994796438188689437 10144335373048664320758539)
              ·
                refine ⟨15216503059572996481137809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144335373048664320758539 15216503059572996481137809)
                ·
                  refine ⟨11412377294679747360853357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15216503059572996481137809 11412377294679747360853357)
                  ·
                    refine ⟨4279641485504905260320009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11412377294679747360853357 4279641485504905260320009)
                    ·
                      refine ⟨3209731114128678945240007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279641485504905260320009 3209731114128678945240007)
                      ·
                        rfl

theorem cell23_6250929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6250929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250929 prefixEnd_6250929 := by exact prefixLift 6250929
  have htrace : WordTrace (prefixWord ++ tailWord_6250929) baseStart_6250929 baseEnd_6250929 := by
    simpa [prefixWord, tailWord_6250929, baseEnd_6250929] using wordTrace_append hprefix tailTrace_6250929
  have hstable : (prefixWord ++ tailWord_6250929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250929).length < 2 ^ (prefixWord ++ tailWord_6250929).sum := by decide
  have hdescent : baseEnd_6250929 < baseStart_6250929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250935 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 1, 6]
def baseStart_6250935 : Nat := 118140960795 + 6250935 * 2 ^ 59
def prefixEnd_6250935 : Nat := 4983230072969 + 3 ^ 40 * 6250935 * 2
def baseEnd_6250935 : Nat := 1069911398337535307254993

theorem tailTrace_6250935 : CollatzResearch.WordTrace tailWord_6250935 prefixEnd_6250935 1069911398337535307254993 := by
  unfold tailWord_6250935
  simp only [CollatzResearch.WordTrace]
  refine ⟨227990329608937544549146259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151993553072625029699430839 227990329608937544549146259)
  ·
    refine ⟨341985494413406316823719389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227990329608937544549146259 341985494413406316823719389)
    ·
      refine ⟨128244560405027368808894771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341985494413406316823719389 128244560405027368808894771)
      ·
        refine ⟨192366840607541053213342157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128244560405027368808894771 192366840607541053213342157)
        ·
          refine ⟨72137565227827894955003309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192366840607541053213342157 72137565227827894955003309)
          ·
            refine ⟨27051586960435460608126241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72137565227827894955003309 27051586960435460608126241)
            ·
              refine ⟨20288690220326595456094681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27051586960435460608126241 20288690220326595456094681)
              ·
                refine ⟨15216517665244946592071011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20288690220326595456094681 15216517665244946592071011)
                ·
                  refine ⟨22824776497867419888106517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15216517665244946592071011 22824776497867419888106517)
                  ·
                    refine ⟨1069911398337535307254993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22824776497867419888106517 1069911398337535307254993)
                    ·
                      rfl

theorem cell23_6250935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_6250935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250935 prefixEnd_6250935 := by exact prefixLift 6250935
  have htrace : WordTrace (prefixWord ++ tailWord_6250935) baseStart_6250935 baseEnd_6250935 := by
    simpa [prefixWord, tailWord_6250935, baseEnd_6250935] using wordTrace_append hprefix tailTrace_6250935
  have hstable : (prefixWord ++ tailWord_6250935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250935).length < 2 ^ (prefixWord ++ tailWord_6250935).sum := by decide
  have hdescent : baseEnd_6250935 < baseStart_6250935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250952 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_6250952 : Nat := 118140960795 + 6250952 * 2 ^ 59
def prefixEnd_6250952 : Nat := 4983230072969 + 3 ^ 40 * 6250952 * 2
def baseEnd_6250952 : Nat := 1069914308061244118417467

theorem tailTrace_6250952 : CollatzResearch.WordTrace tailWord_6250952 prefixEnd_6250952 1069914308061244118417467 := by
  unfold tailWord_6250952
  simp only [CollatzResearch.WordTrace]
  refine ⟨113995474824937978226257555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151993966433250637635010073 113995474824937978226257555)
  ·
    refine ⟨170993212237406967339386333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113995474824937978226257555 170993212237406967339386333)
    ·
      refine ⟨64122454589027612752269875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170993212237406967339386333 64122454589027612752269875)
      ·
        refine ⟨96183681883541419128404813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64122454589027612752269875 96183681883541419128404813)
        ·
          refine ⟨36068880706328032173151805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96183681883541419128404813 36068880706328032173151805)
          ·
            refine ⟨13525830264873012064931927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36068880706328032173151805 13525830264873012064931927)
            ·
              refine ⟨20288745397309518097397891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525830264873012064931927 20288745397309518097397891)
              ·
                refine ⟨30433118095964277146096837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20288745397309518097397891 30433118095964277146096837)
                ·
                  refine ⟨5706209642993301964893157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30433118095964277146096837 5706209642993301964893157)
                  ·
                    refine ⟨1069914308061244118417467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706209642993301964893157 1069914308061244118417467)
                    ·
                      rfl

theorem cell23_6250952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_6250952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250952 prefixEnd_6250952 := by exact prefixLift 6250952
  have htrace : WordTrace (prefixWord ++ tailWord_6250952) baseStart_6250952 baseEnd_6250952 := by
    simpa [prefixWord, tailWord_6250952, baseEnd_6250952] using wordTrace_append hprefix tailTrace_6250952
  have hstable : (prefixWord ++ tailWord_6250952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250952).length < 2 ^ (prefixWord ++ tailWord_6250952).sum := by decide
  have hdescent : baseEnd_6250952 < baseStart_6250952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250969 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 2, 4]
def baseStart_6250969 : Nat := 118140960795 + 6250969 * 2 ^ 59
def prefixEnd_6250969 : Nat := 4983230072969 + 3 ^ 40 * 6250969 * 2
def baseEnd_6250969 : Nat := 1069917217784952929579941

theorem tailTrace_6250969 : CollatzResearch.WordTrace tailWord_6250969 prefixEnd_6250969 1069917217784952929579941 := by
  unfold tailWord_6250969
  simp only [CollatzResearch.WordTrace]
  refine ⟨227991569690814368355883961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151994379793876245570589307 227991569690814368355883961)
  ·
    refine ⟨170993677268110776266912971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227991569690814368355883961 170993677268110776266912971)
    ·
      refine ⟨256490515902166164400369457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170993677268110776266912971 256490515902166164400369457)
      ·
        refine ⟨192367886926624623300277093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256490515902166164400369457 192367886926624623300277093)
        ·
          refine ⟨36068978798742116868801955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192367886926624623300277093 36068978798742116868801955)
          ·
            refine ⟨54103468198113175303202933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36068978798742116868801955 54103468198113175303202933)
            ·
              refine ⟨5072200143573110184675275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54103468198113175303202933 5072200143573110184675275)
              ·
                refine ⟨7608300215359665277012913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072200143573110184675275 7608300215359665277012913)
                ·
                  refine ⟨5706225161519748957759685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7608300215359665277012913 5706225161519748957759685)
                  ·
                    refine ⟨1069917217784952929579941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706225161519748957759685 1069917217784952929579941)
                    ·
                      rfl

theorem cell23_6250969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_6250969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250969 prefixEnd_6250969 := by exact prefixLift 6250969
  have htrace : WordTrace (prefixWord ++ tailWord_6250969) baseStart_6250969 baseEnd_6250969 := by
    simpa [prefixWord, tailWord_6250969, baseEnd_6250969] using wordTrace_append hprefix tailTrace_6250969
  have hstable : (prefixWord ++ tailWord_6250969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250969).length < 2 ^ (prefixWord ++ tailWord_6250969).sum := by decide
  have hdescent : baseEnd_6250969 < baseStart_6250969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6250992 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3]
def baseStart_6250992 : Nat := 118140960795 + 6250992 * 2 ^ 59
def prefixEnd_6250992 : Nat := 4983230072969 + 3 ^ 40 * 6250992 * 2
def baseEnd_6250992 : Nat := 3209763463409912198752217

theorem tailTrace_6250992 : CollatzResearch.WordTrace tailWord_6250992 prefixEnd_6250992 3209763463409912198752217 := by
  unfold tailWord_6250992
  simp only [CollatzResearch.WordTrace]
  refine ⟨113996204284865521641985615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151994939046487362189314153 113996204284865521641985615)
  ·
    refine ⟨170994306427298282462978423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113996204284865521641985615 170994306427298282462978423)
    ·
      refine ⟨256491459640947423694467635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170994306427298282462978423 256491459640947423694467635)
      ·
        refine ⟨384737189461421135541701453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256491459640947423694467635 384737189461421135541701453)
        ·
          refine ⟨144276446048032925828138045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384737189461421135541701453 144276446048032925828138045)
          ·
            refine ⟨54103667268012347185551767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144276446048032925828138045 54103667268012347185551767)
            ·
              refine ⟨81155500902018520778327651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54103667268012347185551767 81155500902018520778327651)
              ·
                refine ⟨121733251353027781167491477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81155500902018520778327651 121733251353027781167491477)
                ·
                  refine ⟨5706246157173177242226163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121733251353027781167491477 5706246157173177242226163)
                  ·
                    refine ⟨8559369235759765863339245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5706246157173177242226163 8559369235759765863339245)
                    ·
                      refine ⟨3209763463409912198752217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559369235759765863339245 3209763463409912198752217)
                      ·
                        rfl

theorem cell23_6250992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_6250992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6250992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6250992 prefixEnd_6250992 := by exact prefixLift 6250992
  have htrace : WordTrace (prefixWord ++ tailWord_6250992) baseStart_6250992 baseEnd_6250992 := by
    simpa [prefixWord, tailWord_6250992, baseEnd_6250992] using wordTrace_append hprefix tailTrace_6250992
  have hstable : (prefixWord ++ tailWord_6250992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6250992).length < 2 ^ (prefixWord ++ tailWord_6250992).sum := by decide
  have hdescent : baseEnd_6250992 < baseStart_6250992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6250992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251005 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_6251005 : Nat := 118140960795 + 6251005 * 2 ^ 59
def prefixEnd_6251005 : Nat := 4983230072969 + 3 ^ 40 * 6251005 * 2
def baseEnd_6251005 : Nat := 3209770138658420647889657

theorem tailTrace_6251005 : CollatzResearch.WordTrace tailWord_6251005 prefixEnd_6251005 3209770138658420647889657 := by
  unfold tailWord_6251005
  simp only [CollatzResearch.WordTrace]
  refine ⟨227992882718683946504194469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151995255145789297669462979 227992882718683946504194469)
  ·
    refine ⟨42748665509753239969536463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227992882718683946504194469 42748665509753239969536463)
    ·
      refine ⟨64122998264629859954304695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42748665509753239969536463 64122998264629859954304695)
      ·
        refine ⟨96184497396944789931457043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64122998264629859954304695 96184497396944789931457043)
        ·
          refine ⟨144276746095417184897185565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96184497396944789931457043 144276746095417184897185565)
          ·
            refine ⟨54103779785781444336444587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144276746095417184897185565 54103779785781444336444587)
            ·
              refine ⟨81155669678672166504666881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54103779785781444336444587 81155669678672166504666881)
              ·
                refine ⟨60866752259004124878500161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81155669678672166504666881 60866752259004124878500161)
                ·
                  refine ⟨45650064194253093658875121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60866752259004124878500161 45650064194253093658875121)
                  ·
                    refine ⟨34237548145689820244156341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45650064194253093658875121 34237548145689820244156341)
                    ·
                      refine ⟨3209770138658420647889657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34237548145689820244156341 3209770138658420647889657)
                      ·
                        rfl

theorem cell23_6251005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_6251005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251005 prefixEnd_6251005 := by exact prefixLift 6251005
  have htrace : WordTrace (prefixWord ++ tailWord_6251005) baseStart_6251005 baseEnd_6251005 := by
    simpa [prefixWord, tailWord_6251005, baseEnd_6251005] using wordTrace_append hprefix tailTrace_6251005
  have hstable : (prefixWord ++ tailWord_6251005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251005).length < 2 ^ (prefixWord ++ tailWord_6251005).sum := by decide
  have hdescent : baseEnd_6251005 < baseStart_6251005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251009 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_6251009 : Nat := 118140960795 + 6251009 * 2 ^ 59
def prefixEnd_6251009 : Nat := 4983230072969 + 3 ^ 40 * 6251009 * 2
def baseEnd_6251009 : Nat := 3209772192581038632239639

theorem tailTrace_6251009 : CollatzResearch.WordTrace tailWord_6251009 prefixEnd_6251009 3209772192581038632239639 := by
  unfold tailWord_6251009
  simp only [CollatzResearch.WordTrace]
  refine ⟨227993028610669455187340081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151995352407112970124893387 227993028610669455187340081)
  ·
    refine ⟨170994771458002091390505061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227993028610669455187340081 170994771458002091390505061)
    ·
      refine ⟨32061519648375392135719699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170994771458002091390505061 32061519648375392135719699)
      ·
        refine ⟨48092279472563088203579549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32061519648375392135719699 48092279472563088203579549)
        ·
          refine ⟨18034604802211158076342331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48092279472563088203579549 18034604802211158076342331)
          ·
            refine ⟨27051907203316737114513497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18034604802211158076342331 27051907203316737114513497)
            ·
              refine ⟨20288930402487552835885123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27051907203316737114513497 20288930402487552835885123)
              ·
                refine ⟨30433395603731329253827685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20288930402487552835885123 30433395603731329253827685)
                ·
                  refine ⟨5706261675699624235092691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30433395603731329253827685 5706261675699624235092691)
                  ·
                    refine ⟨8559392513549436352639037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5706261675699624235092691 8559392513549436352639037)
                    ·
                      refine ⟨3209772192581038632239639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559392513549436352639037 3209772192581038632239639)
                      ·
                        rfl

theorem cell23_6251009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_6251009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251009 prefixEnd_6251009 := by exact prefixLift 6251009
  have htrace : WordTrace (prefixWord ++ tailWord_6251009) baseStart_6251009 baseEnd_6251009 := by
    simpa [prefixWord, tailWord_6251009, baseEnd_6251009] using wordTrace_append hprefix tailTrace_6251009
  have hstable : (prefixWord ++ tailWord_6251009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251009).length < 2 ^ (prefixWord ++ tailWord_6251009).sum := by decide
  have hdescent : baseEnd_6251009 < baseStart_6251009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251010 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6251010 : Nat := 118140960795 + 6251010 * 2 ^ 59
def prefixEnd_6251010 : Nat := 4983230072969 + 3 ^ 40 * 6251010 * 2
def baseEnd_6251010 : Nat := 3209772706061693128327135

theorem tailTrace_6251010 : CollatzResearch.WordTrace tailWord_6251010 prefixEnd_6251010 3209772706061693128327135 := by
  unfold tailWord_6251010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56998266270916458089531621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151995376722443888238750989 56998266270916458089531621)
  ·
    refine ⟨10687174925796835891787179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56998266270916458089531621 10687174925796835891787179)
    ·
      refine ⟨16030762388695253837680769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10687174925796835891787179 16030762388695253837680769)
      ·
        refine ⟨12023071791521440378260577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16030762388695253837680769 12023071791521440378260577)
        ·
          refine ⟨9017303843641080283695433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12023071791521440378260577 9017303843641080283695433)
          ·
            refine ⟨6762977882730810212771575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9017303843641080283695433 6762977882730810212771575)
            ·
              refine ⟨10144466824096215319157363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762977882730810212771575 10144466824096215319157363)
              ·
                refine ⟨15216700236144322978736045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144466824096215319157363 15216700236144322978736045)
                ·
                  refine ⟨5706262588554121117026017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15216700236144322978736045 5706262588554121117026017)
                  ·
                    refine ⟨4279696941415590837769513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5706262588554121117026017 4279696941415590837769513)
                    ·
                      refine ⟨3209772706061693128327135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279696941415590837769513 3209772706061693128327135)
                      ·
                        rfl

theorem cell23_6251010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6251010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251010 prefixEnd_6251010 := by exact prefixLift 6251010
  have htrace : WordTrace (prefixWord ++ tailWord_6251010) baseStart_6251010 baseEnd_6251010 := by
    simpa [prefixWord, tailWord_6251010, baseEnd_6251010] using wordTrace_append hprefix tailTrace_6251010
  have hstable : (prefixWord ++ tailWord_6251010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251010).length < 2 ^ (prefixWord ++ tailWord_6251010).sum := by decide
  have hdescent : baseEnd_6251010 < baseStart_6251010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251036 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6251036 : Nat := 118140960795 + 6251036 * 2 ^ 59
def prefixEnd_6251036 : Nat := 4983230072969 + 3 ^ 40 * 6251036 * 2
def baseEnd_6251036 : Nat := 3209786056558710026602015

theorem tailTrace_6251036 : CollatzResearch.WordTrace tailWord_6251036 prefixEnd_6251036 3209786056558710026602015 := by
  unfold tailWord_6251036
  simp only [CollatzResearch.WordTrace]
  refine ⟨113997006690785819399286481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151996008921047759199048641 113997006690785819399286481)
  ·
    refine ⟨85497755018089364549464861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113997006690785819399286481 85497755018089364549464861)
    ·
      refine ⟨32061658131783511706049323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85497755018089364549464861 32061658131783511706049323)
      ·
        refine ⟨48092487197675267559073985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32061658131783511706049323 48092487197675267559073985)
        ·
          refine ⟨36069365398256450669305489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48092487197675267559073985 36069365398256450669305489)
          ·
            refine ⟨27052024048692338001979117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36069365398256450669305489 27052024048692338001979117)
            ·
              refine ⟨10144509018259626750742169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27052024048692338001979117 10144509018259626750742169)
              ·
                refine ⟨7608381763694720063056627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10144509018259626750742169 7608381763694720063056627)
                ·
                  refine ⟨11412572645542080094584941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608381763694720063056627 11412572645542080094584941)
                  ·
                    refine ⟨4279714742078280035469353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11412572645542080094584941 4279714742078280035469353)
                    ·
                      refine ⟨3209786056558710026602015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279714742078280035469353 3209786056558710026602015)
                      ·
                        rfl

theorem cell23_6251036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6251036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251036 prefixEnd_6251036 := by exact prefixLift 6251036
  have htrace : WordTrace (prefixWord ++ tailWord_6251036) baseStart_6251036 baseEnd_6251036 := by
    simpa [prefixWord, tailWord_6251036, baseEnd_6251036] using wordTrace_append hprefix tailTrace_6251036
  have hstable : (prefixWord ++ tailWord_6251036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251036).length < 2 ^ (prefixWord ++ tailWord_6251036).sum := by decide
  have hdescent : baseEnd_6251036 < baseStart_6251036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251060 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6251060 : Nat := 118140960795 + 6251060 * 2 ^ 59
def prefixEnd_6251060 : Nat := 4983230072969 + 3 ^ 40 * 6251060 * 2
def baseEnd_6251060 : Nat := 3209798380094417932701905

theorem tailTrace_6251060 : CollatzResearch.WordTrace tailWord_6251060 prefixEnd_6251060 3209798380094417932701905 := by
  unfold tailWord_6251060
  simp only [CollatzResearch.WordTrace]
  refine ⟨113997444366742345448723317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151996592488989793931631089 113997444366742345448723317)
  ·
    refine ⟨10687260409382094885817811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113997444366742345448723317 10687260409382094885817811)
    ·
      refine ⟨16030890614073142328726717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10687260409382094885817811 16030890614073142328726717)
      ·
        refine ⟨6011583980277428373272519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16030890614073142328726717 6011583980277428373272519)
        ·
          refine ⟨9017375970416142559908779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011583980277428373272519 9017375970416142559908779)
          ·
            refine ⟨13526063955624213839863169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017375970416142559908779 13526063955624213839863169)
            ·
              refine ⟨10144547966718160379897377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13526063955624213839863169 10144547966718160379897377)
              ·
                refine ⟨7608410975038620284923033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10144547966718160379897377 7608410975038620284923033)
                ·
                  refine ⟨5706308231278965213692275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7608410975038620284923033 5706308231278965213692275)
                  ·
                    refine ⟨8559462346918447820538413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5706308231278965213692275 8559462346918447820538413)
                    ·
                      refine ⟨3209798380094417932701905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559462346918447820538413 3209798380094417932701905)
                      ·
                        rfl

theorem cell23_6251060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6251060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251060 prefixEnd_6251060 := by exact prefixLift 6251060
  have htrace : WordTrace (prefixWord ++ tailWord_6251060) baseStart_6251060 baseEnd_6251060 := by
    simpa [prefixWord, tailWord_6251060, baseEnd_6251060] using wordTrace_append hprefix tailTrace_6251060
  have hstable : (prefixWord ++ tailWord_6251060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251060).length < 2 ^ (prefixWord ++ tailWord_6251060).sum := by decide
  have hdescent : baseEnd_6251060 < baseStart_6251060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251066 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_6251066 : Nat := 118140960795 + 6251066 * 2 ^ 59
def prefixEnd_6251066 : Nat := 4983230072969 + 3 ^ 40 * 6251066 * 2
def baseEnd_6251066 : Nat := 3209801460978344909226877

theorem tailTrace_6251066 : CollatzResearch.WordTrace tailWord_6251066 prefixEnd_6251066 3209801460978344909226877 := by
  unfold tailWord_6251066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56998776892865738480541263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151996738380975302614776701 56998776892865738480541263)
  ·
    refine ⟨85498165339298607720811895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56998776892865738480541263 85498165339298607720811895)
    ·
      refine ⟨128247248008947911581217843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85498165339298607720811895 128247248008947911581217843)
      ·
        refine ⟨192370872013421867371826765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128247248008947911581217843 192370872013421867371826765)
        ·
          refine ⟨72139077005033200264435037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192370872013421867371826765 72139077005033200264435037)
          ·
            refine ⟨27052153876887450099163139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72139077005033200264435037 27052153876887450099163139)
            ·
              refine ⟨40578230815331175148744709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27052153876887450099163139 40578230815331175148744709)
              ·
                refine ⟨7608418277874595340389633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40578230815331175148744709 7608418277874595340389633)
                ·
                  refine ⟨5706313708405946505292225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7608418277874595340389633 5706313708405946505292225)
                  ·
                    refine ⟨4279735281304459878969169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5706313708405946505292225 4279735281304459878969169)
                    ·
                      refine ⟨3209801460978344909226877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279735281304459878969169 3209801460978344909226877)
                      ·
                        rfl

theorem cell23_6251066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_6251066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251066 prefixEnd_6251066 := by exact prefixLift 6251066
  have htrace : WordTrace (prefixWord ++ tailWord_6251066) baseStart_6251066 baseEnd_6251066 := by
    simpa [prefixWord, tailWord_6251066, baseEnd_6251066] using wordTrace_append hprefix tailTrace_6251066
  have hstable : (prefixWord ++ tailWord_6251066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251066).length < 2 ^ (prefixWord ++ tailWord_6251066).sum := by decide
  have hdescent : baseEnd_6251066 < baseStart_6251066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251082 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_6251082 : Nat := 118140960795 + 6251082 * 2 ^ 59
def prefixEnd_6251082 : Nat := 4983230072969 + 3 ^ 40 * 6251082 * 2
def baseEnd_6251082 : Nat := 3209809676668816846626803

theorem tailTrace_6251082 : CollatzResearch.WordTrace tailWord_6251082 prefixEnd_6251082 3209809676668816846626803 := by
  unfold tailWord_6251082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56998922784851247163686875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151997127426269992436498333 56998922784851247163686875)
  ·
    refine ⟨85498384177276870745530313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56998922784851247163686875 85498384177276870745530313)
    ·
      refine ⟨64123788132957653059147735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85498384177276870745530313 64123788132957653059147735)
      ·
        refine ⟨96185682199436479588721603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64123788132957653059147735 96185682199436479588721603)
        ·
          refine ⟨144278523299154719383082405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96185682199436479588721603 144278523299154719383082405)
          ·
            refine ⟨27052223118591509884327951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144278523299154719383082405 27052223118591509884327951)
            ·
              refine ⟨40578334677887264826491927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27052223118591509884327951 40578334677887264826491927)
              ·
                refine ⟨60867502016830897239737891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40578334677887264826491927 60867502016830897239737891)
                ·
                  refine ⟨91301253025246345859606837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60867502016830897239737891 91301253025246345859606837)
                  ·
                    refine ⟨8559492471116844924338141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91301253025246345859606837 8559492471116844924338141)
                    ·
                      refine ⟨3209809676668816846626803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559492471116844924338141 3209809676668816846626803)
                      ·
                        rfl

theorem cell23_6251082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_6251082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251082 prefixEnd_6251082 := by exact prefixLift 6251082
  have htrace : WordTrace (prefixWord ++ tailWord_6251082) baseStart_6251082 baseEnd_6251082 := by
    simpa [prefixWord, tailWord_6251082, baseEnd_6251082] using wordTrace_append hprefix tailTrace_6251082
  have hstable : (prefixWord ++ tailWord_6251082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251082).length < 2 ^ (prefixWord ++ tailWord_6251082).sum := by decide
  have hdescent : baseEnd_6251082 < baseStart_6251082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251139 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 2, 4, 2]
def baseStart_6251139 : Nat := 118140960795 + 6251139 * 2 ^ 59
def prefixEnd_6251139 : Nat := 4983230072969 + 3 ^ 40 * 6251139 * 2
def baseEnd_6251139 : Nat := 3209838945066123123614041

theorem tailTrace_6251139 : CollatzResearch.WordTrace tailWord_6251139 prefixEnd_6251139 3209838945066123123614041 := by
  unfold tailWord_6251139
  simp only [CollatzResearch.WordTrace]
  refine ⟨227997770100198487389572471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151998513400132324926381647 227997770100198487389572471)
  ·
    refine ⟨341996655150297731084358707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227997770100198487389572471 341996655150297731084358707)
    ·
      refine ⟨512994982725446596626538061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341996655150297731084358707 512994982725446596626538061)
      ·
        refine ⟨192373118522042473734951773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512994982725446596626538061 192373118522042473734951773)
        ·
          refine ⟨72139919445765927650606915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192373118522042473734951773 72139919445765927650606915)
          ·
            refine ⟨108209879168648891475910373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72139919445765927650606915 108209879168648891475910373)
            ·
              refine ⟨20289352344121667151733195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108209879168648891475910373 20289352344121667151733195)
              ·
                refine ⟨30434028516182500727599793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20289352344121667151733195 30434028516182500727599793)
                ·
                  refine ⟨22825521387136875545699845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30434028516182500727599793 22825521387136875545699845)
                  ·
                    refine ⟨4279785260088164164818721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22825521387136875545699845 4279785260088164164818721)
                    ·
                      refine ⟨3209838945066123123614041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279785260088164164818721 3209838945066123123614041)
                      ·
                        rfl

theorem cell23_6251139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_6251139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251139 prefixEnd_6251139 := by exact prefixLift 6251139
  have htrace : WordTrace (prefixWord ++ tailWord_6251139) baseStart_6251139 baseEnd_6251139 := by
    simpa [prefixWord, tailWord_6251139, baseEnd_6251139] using wordTrace_append hprefix tailTrace_6251139
  have hstable : (prefixWord ++ tailWord_6251139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251139).length < 2 ^ (prefixWord ++ tailWord_6251139).sum := by decide
  have hdescent : baseEnd_6251139 < baseStart_6251139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251159 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_6251159 : Nat := 118140960795 + 6251159 * 2 ^ 59
def prefixEnd_6251159 : Nat := 4983230072969 + 3 ^ 40 * 6251159 * 2
def baseEnd_6251159 : Nat := 3209849214679213045363949

theorem tailTrace_6251159 : CollatzResearch.WordTrace tailWord_6251159 prefixEnd_6251159 3209849214679213045363949 := by
  unfold tailWord_6251159
  simp only [CollatzResearch.WordTrace]
  refine ⟨227998499560126030805300531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151998999706750687203533687 227998499560126030805300531)
  ·
    refine ⟨341997749340189046207950797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227998499560126030805300531 341997749340189046207950797)
    ·
      refine ⟨128249156002570892327981549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341997749340189046207950797 128249156002570892327981549)
      ·
        refine ⟨48093433500964084622993081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128249156002570892327981549 48093433500964084622993081)
        ·
          refine ⟨36070075125723063467244811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48093433500964084622993081 36070075125723063467244811)
          ·
            refine ⟨54105112688584595200867217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36070075125723063467244811 54105112688584595200867217)
            ·
              refine ⟨40578834516438446400650413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54105112688584595200867217 40578834516438446400650413)
              ·
                refine ⟨15217062943664417400243905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40578834516438446400650413 15217062943664417400243905)
                ·
                  refine ⟨11412797207748313050182929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15217062943664417400243905 11412797207748313050182929)
                  ·
                    refine ⟨8559597905811234787637197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11412797207748313050182929 8559597905811234787637197)
                    ·
                      refine ⟨3209849214679213045363949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559597905811234787637197 3209849214679213045363949)
                      ·
                        rfl

theorem cell23_6251159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_6251159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251159 prefixEnd_6251159 := by exact prefixLift 6251159
  have htrace : WordTrace (prefixWord ++ tailWord_6251159) baseStart_6251159 baseEnd_6251159 := by
    simpa [prefixWord, tailWord_6251159, baseEnd_6251159] using wordTrace_append hprefix tailTrace_6251159
  have hstable : (prefixWord ++ tailWord_6251159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251159).length < 2 ^ (prefixWord ++ tailWord_6251159).sum := by decide
  have hdescent : baseEnd_6251159 < baseStart_6251159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251183 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 1, 4]
def baseStart_6251183 : Nat := 118140960795 + 6251183 * 2 ^ 59
def prefixEnd_6251183 : Nat := 4983230072969 + 3 ^ 40 * 6251183 * 2
def baseEnd_6251183 : Nat := 1069953846071640317154613

theorem tailTrace_6251183 : CollatzResearch.WordTrace tailWord_6251183 prefixEnd_6251183 1069953846071640317154613 := by
  unfold tailWord_6251183
  simp only [CollatzResearch.WordTrace]
  refine ⟨227999374912039082904174203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151999583274692721936116135 227999374912039082904174203)
  ·
    refine ⟨341999062368058624356261305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227999374912039082904174203 341999062368058624356261305)
    ·
      refine ⟨256499296776043968267195979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341999062368058624356261305 256499296776043968267195979)
      ·
        refine ⟨384748945164065952400793969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256499296776043968267195979 384748945164065952400793969)
        ·
          refine ⟨288561708873049464300595477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384748945164065952400793969 288561708873049464300595477)
          ·
            refine ⟨13526330103424193639090413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 288561708873049464300595477 13526330103424193639090413)
            ·
              refine ⟨5072373788784072614658905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13526330103424193639090413 5072373788784072614658905)
              ·
                refine ⟨3804280341588054460994179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072373788784072614658905 3804280341588054460994179)
                ·
                  refine ⟨5706420512382081691491269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804280341588054460994179 5706420512382081691491269)
                  ·
                    refine ⟨1069953846071640317154613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706420512382081691491269 1069953846071640317154613)
                    ·
                      rfl

theorem cell23_6251183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 4].length) (baseStart_6251183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251183 prefixEnd_6251183 := by exact prefixLift 6251183
  have htrace : WordTrace (prefixWord ++ tailWord_6251183) baseStart_6251183 baseEnd_6251183 := by
    simpa [prefixWord, tailWord_6251183, baseEnd_6251183] using wordTrace_append hprefix tailTrace_6251183
  have hstable : (prefixWord ++ tailWord_6251183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251183).length < 2 ^ (prefixWord ++ tailWord_6251183).sum := by decide
  have hdescent : baseEnd_6251183 < baseStart_6251183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251226 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_6251226 : Nat := 118140960795 + 6251226 * 2 ^ 59
def prefixEnd_6251226 : Nat := 4983230072969 + 3 ^ 40 * 6251226 * 2
def baseEnd_6251226 : Nat := 1069961205961021427742047

theorem tailTrace_6251226 : CollatzResearch.WordTrace tailWord_6251226 prefixEnd_6251226 1069961205961021427742047 := by
  unfold tailWord_6251226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57000235812720825311997383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152000628833922200831993021 57000235812720825311997383)
  ·
    refine ⟨85500353719081237967996075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57000235812720825311997383 85500353719081237967996075)
    ·
      refine ⟨128250530578621856951994113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85500353719081237967996075 128250530578621856951994113)
      ·
        refine ⟨96187897933966392713995585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128250530578621856951994113 96187897933966392713995585)
        ·
          refine ⟨72140923450474794535496689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96187897933966392713995585 72140923450474794535496689)
          ·
            refine ⟨54105692587856095901622517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72140923450474794535496689 54105692587856095901622517)
            ·
              refine ⟨5072408680111508990777111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54105692587856095901622517 5072408680111508990777111)
              ·
                refine ⟨7608613020167263486165667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072408680111508990777111 7608613020167263486165667)
                ·
                  refine ⟨11412919530250895229248501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608613020167263486165667 11412919530250895229248501)
                  ·
                    refine ⟨1069961205961021427742047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11412919530250895229248501 1069961205961021427742047)
                    ·
                      rfl

theorem cell23_6251226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_6251226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251226 prefixEnd_6251226 := by exact prefixLift 6251226
  have htrace : WordTrace (prefixWord ++ tailWord_6251226) baseStart_6251226 baseEnd_6251226 := by
    simpa [prefixWord, tailWord_6251226, baseEnd_6251226] using wordTrace_append hprefix tailTrace_6251226
  have hstable : (prefixWord ++ tailWord_6251226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251226).length < 2 ^ (prefixWord ++ tailWord_6251226).sum := by decide
  have hdescent : baseEnd_6251226 < baseStart_6251226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251240 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6251240 : Nat := 118140960795 + 6251240 * 2 ^ 59
def prefixEnd_6251240 : Nat := 4983230072969 + 3 ^ 40 * 6251240 * 2
def baseEnd_6251240 : Nat := 3209890806612227228451077

theorem tailTrace_6251240 : CollatzResearch.WordTrace tailWord_6251240 prefixEnd_6251240 3209890806612227228451077 := by
  unfold tailWord_6251240
  simp only [CollatzResearch.WordTrace]
  refine ⟨114000726936416290819499587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152000969248555054425999449 114000726936416290819499587)
  ·
    refine ⟨171001090404624436229249381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114000726936416290819499587 171001090404624436229249381)
    ·
      refine ⟨32062704450867081792984259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171001090404624436229249381 32062704450867081792984259)
      ·
        refine ⟨48094056676300622689476389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32062704450867081792984259 48094056676300622689476389)
        ·
          refine ⟨9017635626806366754276823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48094056676300622689476389 9017635626806366754276823)
          ·
            refine ⟨13526453440209550131415235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017635626806366754276823 13526453440209550131415235)
            ·
              refine ⟨20289680160314325197122853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13526453440209550131415235 20289680160314325197122853)
              ·
                refine ⟨3804315030058935974460535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20289680160314325197122853 3804315030058935974460535)
                ·
                  refine ⟨5706472545088403961690803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804315030058935974460535 5706472545088403961690803)
                  ·
                    refine ⟨8559708817632605942536205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5706472545088403961690803 8559708817632605942536205)
                    ·
                      refine ⟨3209890806612227228451077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559708817632605942536205 3209890806612227228451077)
                      ·
                        rfl

theorem cell23_6251240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6251240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251240 prefixEnd_6251240 := by exact prefixLift 6251240
  have htrace : WordTrace (prefixWord ++ tailWord_6251240) baseStart_6251240 baseEnd_6251240 := by
    simpa [prefixWord, tailWord_6251240, baseEnd_6251240] using wordTrace_append hprefix tailTrace_6251240
  have hstable : (prefixWord ++ tailWord_6251240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251240).length < 2 ^ (prefixWord ++ tailWord_6251240).sum := by decide
  have hdescent : baseEnd_6251240 < baseStart_6251240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251249 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_6251249 : Nat := 118140960795 + 6251249 * 2 ^ 59
def prefixEnd_6251249 : Nat := 4983230072969 + 3 ^ 40 * 6251249 * 2
def baseEnd_6251249 : Nat := 3209895427938117693238535

theorem tailTrace_6251249 : CollatzResearch.WordTrace tailWord_6251249 prefixEnd_6251249 3209895427938117693238535 := by
  unfold tailWord_6251249
  simp only [CollatzResearch.WordTrace]
  refine ⟨228001782129799976176076801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152001188086533317450717867 228001782129799976176076801)
  ·
    refine ⟨171001336597349982132057601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228001782129799976176076801 171001336597349982132057601)
    ·
      refine ⟨128251002448012486599043201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171001336597349982132057601 128251002448012486599043201)
      ·
        refine ⟨96188251836009364949282401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128251002448012486599043201 96188251836009364949282401)
        ·
          refine ⟨72141188877007023711961801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96188251836009364949282401 72141188877007023711961801)
          ·
            refine ⟨54105891657755267783971351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72141188877007023711961801 54105891657755267783971351)
            ·
              refine ⟨81158837486632901675957027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54105891657755267783971351 81158837486632901675957027)
              ·
                refine ⟨121738256229949352513935541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81158837486632901675957027 121738256229949352513935541)
                ·
                  refine ⟨11412961521557751798181457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121738256229949352513935541 11412961521557751798181457)
                  ·
                    refine ⟨8559721141168313848636093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11412961521557751798181457 8559721141168313848636093)
                    ·
                      refine ⟨3209895427938117693238535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559721141168313848636093 3209895427938117693238535)
                      ·
                        rfl

theorem cell23_6251249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_6251249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251249 prefixEnd_6251249 := by exact prefixLift 6251249
  have htrace : WordTrace (prefixWord ++ tailWord_6251249) baseStart_6251249 baseEnd_6251249 := by
    simpa [prefixWord, tailWord_6251249, baseEnd_6251249] using wordTrace_append hprefix tailTrace_6251249
  have hstable : (prefixWord ++ tailWord_6251249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251249).length < 2 ^ (prefixWord ++ tailWord_6251249).sum := by decide
  have hdescent : baseEnd_6251249 < baseStart_6251249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251279 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_6251279 : Nat := 118140960795 + 6251279 * 2 ^ 59
def prefixEnd_6251279 : Nat := 4983230072969 + 3 ^ 40 * 6251279 * 2
def baseEnd_6251279 : Nat := 3209910832357752575863397

theorem tailTrace_6251279 : CollatzResearch.WordTrace tailWord_6251279 prefixEnd_6251279 3209910832357752575863397 := by
  unfold tailWord_6251279
  simp only [CollatzResearch.WordTrace]
  refine ⟨228002876319691291299668891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152001917546460860866445927 228002876319691291299668891)
  ·
    refine ⟨342004314479536936949503337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228002876319691291299668891 342004314479536936949503337)
    ·
      refine ⟨256503235859652702712127503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342004314479536936949503337 256503235859652702712127503)
      ·
        refine ⟨384754853789479054068191255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256503235859652702712127503 384754853789479054068191255)
        ·
          refine ⟨577132280684218581102286883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384754853789479054068191255 577132280684218581102286883)
          ·
            refine ⟨865698421026327871653430325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577132280684218581102286883 865698421026327871653430325)
            ·
              refine ⟨81159226971218237967509093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 865698421026327871653430325 81159226971218237967509093)
              ·
                refine ⟨15217355057103419618907955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81159226971218237967509093 15217355057103419618907955)
                ·
                  refine ⟨22826032585655129428361933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15217355057103419618907955 22826032585655129428361933)
                  ·
                    refine ⟨8559762219620673535635725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22826032585655129428361933 8559762219620673535635725)
                    ·
                      refine ⟨3209910832357752575863397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8559762219620673535635725 3209910832357752575863397)
                      ·
                        rfl

theorem cell23_6251279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_6251279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251279 prefixEnd_6251279 := by exact prefixLift 6251279
  have htrace : WordTrace (prefixWord ++ tailWord_6251279) baseStart_6251279 baseEnd_6251279 := by
    simpa [prefixWord, tailWord_6251279, baseEnd_6251279] using wordTrace_append hprefix tailTrace_6251279
  have hstable : (prefixWord ++ tailWord_6251279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251279).length < 2 ^ (prefixWord ++ tailWord_6251279).sum := by decide
  have hdescent : baseEnd_6251279 < baseStart_6251279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251336 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_6251336 : Nat := 118140960795 + 6251336 * 2 ^ 59
def prefixEnd_6251336 : Nat := 4983230072969 + 3 ^ 40 * 6251336 * 2
def baseEnd_6251336 : Nat := 3209940100755058852850635

theorem tailTrace_6251336 : CollatzResearch.WordTrace tailWord_6251336 prefixEnd_6251336 3209940100755058852850635 := by
  unfold tailWord_6251336
  simp only [CollatzResearch.WordTrace]
  refine ⟨114002477640242395017246931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152003303520323193356329241 114002477640242395017246931)
  ·
    refine ⟨171003716460363592525870397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114002477640242395017246931 171003716460363592525870397)
    ·
      refine ⟨64126393672636347197201399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171003716460363592525870397 64126393672636347197201399)
      ·
        refine ⟨96189590508954520795802099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64126393672636347197201399 96189590508954520795802099)
        ·
          refine ⟨144284385763431781193703149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96189590508954520795802099 144284385763431781193703149)
          ·
            refine ⟨54106644661286917947638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144284385763431781193703149 54106644661286917947638681)
            ·
              refine ⟨40579983495965188460729011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54106644661286917947638681 40579983495965188460729011)
              ·
                refine ⟨60869975243947782691093517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40579983495965188460729011 60869975243947782691093517)
                ·
                  refine ⟨22826240716480418509160069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60869975243947782691093517 22826240716480418509160069)
                  ·
                    refine ⟨4279920134340078470467513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22826240716480418509160069 4279920134340078470467513)
                    ·
                      refine ⟨3209940100755058852850635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279920134340078470467513 3209940100755058852850635)
                      ·
                        rfl

theorem cell23_6251336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_6251336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251336 prefixEnd_6251336 := by exact prefixLift 6251336
  have htrace : WordTrace (prefixWord ++ tailWord_6251336) baseStart_6251336 baseEnd_6251336 := by
    simpa [prefixWord, tailWord_6251336, baseEnd_6251336] using wordTrace_append hprefix tailTrace_6251336
  have hstable : (prefixWord ++ tailWord_6251336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251336).length < 2 ^ (prefixWord ++ tailWord_6251336).sum := by decide
  have hdescent : baseEnd_6251336 < baseStart_6251336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251353 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 4, 2, 2]
def baseStart_6251353 : Nat := 118140960795 + 6251353 * 2 ^ 59
def prefixEnd_6251353 : Nat := 4983230072969 + 3 ^ 40 * 6251353 * 2
def baseEnd_6251353 : Nat := 3209948829926185286338057

theorem tailTrace_6251353 : CollatzResearch.WordTrace tailWord_6251353 prefixEnd_6251353 3209948829926185286338057 := by
  unfold tailWord_6251353
  simp only [CollatzResearch.WordTrace]
  refine ⟨228005575321423201937862713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152003716880948801291908475 228005575321423201937862713)
  ·
    refine ⟨171004181491067401453397035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228005575321423201937862713 171004181491067401453397035)
    ·
      refine ⟨256506272236601102180095553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171004181491067401453397035 256506272236601102180095553)
      ·
        refine ⟨192379704177450826635071665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256506272236601102180095553 192379704177450826635071665)
        ·
          refine ⟨144284778133088119976303749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192379704177450826635071665 144284778133088119976303749)
          ·
            refine ⟨27053395899954022495556953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144284778133088119976303749 27053395899954022495556953)
            ·
              refine ⟨20290046924965516871667715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27053395899954022495556953 20290046924965516871667715)
              ·
                refine ⟨30435070387448275307501573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20290046924965516871667715 30435070387448275307501573)
                ·
                  refine ⟨5706575697646551620156545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30435070387448275307501573 5706575697646551620156545)
                  ·
                    refine ⟨4279931773234913715117409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5706575697646551620156545 4279931773234913715117409)
                    ·
                      refine ⟨3209948829926185286338057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279931773234913715117409 3209948829926185286338057)
                      ·
                        rfl

theorem cell23_6251353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_6251353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251353 prefixEnd_6251353 := by exact prefixLift 6251353
  have htrace : WordTrace (prefixWord ++ tailWord_6251353) baseStart_6251353 baseEnd_6251353 := by
    simpa [prefixWord, tailWord_6251353, baseEnd_6251353] using wordTrace_append hprefix tailTrace_6251353
  have hstable : (prefixWord ++ tailWord_6251353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251353).length < 2 ^ (prefixWord ++ tailWord_6251353).sum := by decide
  have hdescent : baseEnd_6251353 < baseStart_6251353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251374 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_6251374 : Nat := 118140960795 + 6251374 * 2 ^ 59
def prefixEnd_6251374 : Nat := 4983230072969 + 3 ^ 40 * 6251374 * 2
def baseEnd_6251374 : Nat := 3209959613019929704175461

theorem tailTrace_6251374 : CollatzResearch.WordTrace tailWord_6251374 prefixEnd_6251374 3209959613019929704175461 := by
  unfold tailWord_6251374
  simp only [CollatzResearch.WordTrace]
  refine ⟨28500792656793390315547147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152004227502898081682918117 28500792656793390315547147)
  ·
    refine ⟨42751188985190085473320721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28500792656793390315547147 42751188985190085473320721)
    ·
      refine ⟨32063391738892564104990541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42751188985190085473320721 32063391738892564104990541)
      ·
        refine ⟨12023771902084711539371453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32063391738892564104990541 12023771902084711539371453)
        ·
          refine ⟨4508914463281766827264295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12023771902084711539371453 4508914463281766827264295)
          ·
            refine ⟨6763371694922650240896443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508914463281766827264295 6763371694922650240896443)
            ·
              refine ⟨10145057542383975361344665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763371694922650240896443 10145057542383975361344665)
              ·
                refine ⟨7608793156787981521008499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10145057542383975361344665 7608793156787981521008499)
                ·
                  refine ⟨11413189735181972281512749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608793156787981521008499 11413189735181972281512749)
                  ·
                    refine ⟨4279946150693239605567281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11413189735181972281512749 4279946150693239605567281)
                    ·
                      refine ⟨3209959613019929704175461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4279946150693239605567281 3209959613019929704175461)
                      ·
                        rfl

theorem cell23_6251374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_6251374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251374 prefixEnd_6251374 := by exact prefixLift 6251374
  have htrace : WordTrace (prefixWord ++ tailWord_6251374) baseStart_6251374 baseEnd_6251374 := by
    simpa [prefixWord, tailWord_6251374, baseEnd_6251374] using wordTrace_append hprefix tailTrace_6251374
  have hstable : (prefixWord ++ tailWord_6251374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251374).length < 2 ^ (prefixWord ++ tailWord_6251374).sum := by decide
  have hdescent : baseEnd_6251374 < baseStart_6251374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251389 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_6251389 : Nat := 118140960795 + 6251389 * 2 ^ 59
def prefixEnd_6251389 : Nat := 4983230072969 + 3 ^ 40 * 6251389 * 2
def baseEnd_6251389 : Nat := 1069989105076582381829297

theorem tailTrace_6251389 : CollatzResearch.WordTrace tailWord_6251389 prefixEnd_6251389 1069989105076582381829297 := by
  unfold tailWord_6251389
  simp only [CollatzResearch.WordTrace]
  refine ⟨228006888349292780086173221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152004592232861853390782147 228006888349292780086173221)
  ·
    refine ⟨42751291565492396266157479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228006888349292780086173221 42751291565492396266157479)
    ·
      refine ⟨64126937348238594399236219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42751291565492396266157479 64126937348238594399236219)
      ·
        refine ⟨96190406022357891598854329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64126937348238594399236219 96190406022357891598854329)
        ·
          refine ⟨72142804516768418699140747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96190406022357891598854329 72142804516768418699140747)
          ·
            refine ⟨108214206775152628048711121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72142804516768418699140747 108214206775152628048711121)
            ·
              refine ⟨81160655081364471036533341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108214206775152628048711121 81160655081364471036533341)
              ·
                refine ⟨30435245655511676638700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81160655081364471036533341 30435245655511676638700003)
                ·
                  refine ⟨45652868483267514958050005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30435245655511676638700003 45652868483267514958050005)
                  ·
                    refine ⟨1069989105076582381829297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45652868483267514958050005 1069989105076582381829297)
                    ·
                      rfl

theorem cell23_6251389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_6251389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251389 prefixEnd_6251389 := by exact prefixLift 6251389
  have htrace : WordTrace (prefixWord ++ tailWord_6251389) baseStart_6251389 baseEnd_6251389 := by
    simpa [prefixWord, tailWord_6251389, baseEnd_6251389] using wordTrace_append hprefix tailTrace_6251389
  have hstable : (prefixWord ++ tailWord_6251389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251389).length < 2 ^ (prefixWord ++ tailWord_6251389).sum := by decide
  have hdescent : baseEnd_6251389 < baseStart_6251389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251409 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_6251409 : Nat := 118140960795 + 6251409 * 2 ^ 59
def prefixEnd_6251409 : Nat := 4983230072969 + 3 ^ 40 * 6251409 * 2
def baseEnd_6251409 : Nat := 3209977584842837067237799

theorem tailTrace_6251409 : CollatzResearch.WordTrace tailWord_6251409 prefixEnd_6251409 3209977584842837067237799 := by
  unfold tailWord_6251409
  simp only [CollatzResearch.WordTrace]
  refine ⟨228007617809220323501901281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152005078539480215667934187 228007617809220323501901281)
  ·
    refine ⟨171005713356915242626425961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228007617809220323501901281 171005713356915242626425961)
    ·
      refine ⟨128254285017686431969819471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171005713356915242626425961 128254285017686431969819471)
      ·
        refine ⟨192381427526529647954729207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128254285017686431969819471 192381427526529647954729207)
        ·
          refine ⟨288572141289794471932093811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192381427526529647954729207 288572141289794471932093811)
          ·
            refine ⟨432858211934691707898140717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288572141289794471932093811 432858211934691707898140717)
            ·
              refine ⟨162321829475509390461802769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432858211934691707898140717 162321829475509390461802769)
              ·
                refine ⟨121741372106632042846352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162321829475509390461802769 121741372106632042846352077)
                ·
                  refine ⟨45653014539987016067382029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121741372106632042846352077 45653014539987016067382029)
                  ·
                    refine ⟨17119880452495131025268261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45653014539987016067382029 17119880452495131025268261)
                    ·
                      refine ⟨3209977584842837067237799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17119880452495131025268261 3209977584842837067237799)
                      ·
                        rfl

theorem cell23_6251409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_6251409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251409 prefixEnd_6251409 := by exact prefixLift 6251409
  have htrace : WordTrace (prefixWord ++ tailWord_6251409) baseStart_6251409 baseEnd_6251409 := by
    simpa [prefixWord, tailWord_6251409, baseEnd_6251409] using wordTrace_append hprefix tailTrace_6251409
  have hstable : (prefixWord ++ tailWord_6251409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251409).length < 2 ^ (prefixWord ++ tailWord_6251409).sum := by decide
  have hdescent : baseEnd_6251409 < baseStart_6251409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251410 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_6251410 : Nat := 118140960795 + 6251410 * 2 ^ 59
def prefixEnd_6251410 : Nat := 4983230072969 + 3 ^ 40 * 6251410 * 2
def baseEnd_6251410 : Nat := 356664233147054618147255

theorem tailTrace_6251410 : CollatzResearch.WordTrace tailWord_6251410 prefixEnd_6251410 356664233147054618147255 := by
  unfold tailWord_6251410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57001913570554175168171921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152005102854811133781791789 57001913570554175168171921)
  ·
    refine ⟨42751435177915631376128941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57001913570554175168171921 42751435177915631376128941)
    ·
      refine ⟨16031788191718361766048353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42751435177915631376128941 16031788191718361766048353)
      ·
        refine ⟨12023841143788771324536265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16031788191718361766048353 12023841143788771324536265)
        ·
          refine ⟨9017880857841578493402199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12023841143788771324536265 9017880857841578493402199)
          ·
            refine ⟨13526821286762367740103299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017880857841578493402199 13526821286762367740103299)
            ·
              refine ⟨20290231930143551610154949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13526821286762367740103299 20290231930143551610154949)
              ·
                refine ⟨3804418486901915926904053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20290231930143551610154949 3804418486901915926904053)
                ·
                  refine ⟨356664233147054618147255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3804418486901915926904053 356664233147054618147255)
                  ·
                    rfl

theorem cell23_6251410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_6251410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251410 prefixEnd_6251410 := by exact prefixLift 6251410
  have htrace : WordTrace (prefixWord ++ tailWord_6251410) baseStart_6251410 baseEnd_6251410 := by
    simpa [prefixWord, tailWord_6251410, baseEnd_6251410] using wordTrace_append hprefix tailTrace_6251410
  have hstable : (prefixWord ++ tailWord_6251410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251410).length < 2 ^ (prefixWord ++ tailWord_6251410).sum := by decide
  have hdescent : baseEnd_6251410 < baseStart_6251410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251436 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_6251436 : Nat := 118140960795 + 6251436 * 2 ^ 59
def prefixEnd_6251436 : Nat := 4983230072969 + 3 ^ 40 * 6251436 * 2
def baseEnd_6251436 : Nat := 1069997149606836153866725

theorem tailTrace_6251436 : CollatzResearch.WordTrace tailWord_6251436 prefixEnd_6251436 1069997149606836153866725 := by
  unfold tailWord_6251436
  simp only [CollatzResearch.WordTrace]
  refine ⟨114004301290061253556567081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152005735053415004742089441 114004301290061253556567081)
  ·
    refine ⟨85503225967545940167425311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114004301290061253556567081 85503225967545940167425311)
    ·
      refine ⟨128254838951318910251137967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85503225967545940167425311 128254838951318910251137967)
      ·
        refine ⟨192382258426978365376706951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128254838951318910251137967 192382258426978365376706951)
        ·
          refine ⟨288573387640467548065060427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192382258426978365376706951 288573387640467548065060427)
          ·
            refine ⟨432860081460701322097590641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288573387640467548065060427 432860081460701322097590641)
            ·
              refine ⟨324645061095525991573192981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432860081460701322097590641 324645061095525991573192981)
              ·
                refine ⟨15217737238852780854993421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324645061095525991573192981 15217737238852780854993421)
                ·
                  refine ⟨5706651464569792820622533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15217737238852780854993421 5706651464569792820622533)
                  ·
                    refine ⟨1069997149606836153866725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706651464569792820622533 1069997149606836153866725)
                    ·
                      rfl

theorem cell23_6251436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_6251436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251436 prefixEnd_6251436 := by exact prefixLift 6251436
  have htrace : WordTrace (prefixWord ++ tailWord_6251436) baseStart_6251436 baseEnd_6251436 := by
    simpa [prefixWord, tailWord_6251436, baseEnd_6251436] using wordTrace_append hprefix tailTrace_6251436
  have hstable : (prefixWord ++ tailWord_6251436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251436).length < 2 ^ (prefixWord ++ tailWord_6251436).sum := by decide
  have hdescent : baseEnd_6251436 < baseStart_6251436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251439 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_6251439 : Nat := 118140960795 + 6251439 * 2 ^ 59
def prefixEnd_6251439 : Nat := 4983230072969 + 3 ^ 40 * 6251439 * 2
def baseEnd_6251439 : Nat := 3209992989262471949862661

theorem tailTrace_6251439 : CollatzResearch.WordTrace tailWord_6251439 prefixEnd_6251439 3209992989262471949862661 := by
  unfold tailWord_6251439
  simp only [CollatzResearch.WordTrace]
  refine ⟨228008711999111638625493371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152005807999407759083662247 228008711999111638625493371)
  ·
    refine ⟨342013067998667457938240057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228008711999111638625493371 342013067998667457938240057)
    ·
      refine ⟨256509800999000593453680043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342013067998667457938240057 256509800999000593453680043)
      ·
        refine ⟨384764701498500890180520065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256509800999000593453680043 384764701498500890180520065)
        ·
          refine ⟨288573526123875667635390049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384764701498500890180520065 288573526123875667635390049)
          ·
            refine ⟨216430144592906750726542537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288573526123875667635390049 216430144592906750726542537)
            ·
              refine ⟨162322608444680063044906903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216430144592906750726542537 162322608444680063044906903)
              ·
                refine ⟨243483912667020094567360355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162322608444680063044906903 243483912667020094567360355)
                ·
                  refine ⟨365225869000530141851040533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243483912667020094567360355 365225869000530141851040533)
                  ·
                    refine ⟨17119962609399850399267525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 365225869000530141851040533 17119962609399850399267525)
                    ·
                      refine ⟨3209992989262471949862661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17119962609399850399267525 3209992989262471949862661)
                      ·
                        rfl

theorem cell23_6251439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_6251439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251439 prefixEnd_6251439 := by exact prefixLift 6251439
  have htrace : WordTrace (prefixWord ++ tailWord_6251439) baseStart_6251439 baseEnd_6251439 := by
    simpa [prefixWord, tailWord_6251439, baseEnd_6251439] using wordTrace_append hprefix tailTrace_6251439
  have hstable : (prefixWord ++ tailWord_6251439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251439).length < 2 ^ (prefixWord ++ tailWord_6251439).sum := by decide
  have hdescent : baseEnd_6251439 < baseStart_6251439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251470 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_6251470 : Nat := 118140960795 + 6251470 * 2 ^ 59
def prefixEnd_6251470 : Nat := 4983230072969 + 3 ^ 40 * 6251470 * 2
def baseEnd_6251470 : Nat := 1070002969054253776191673

theorem tailTrace_6251470 : CollatzResearch.WordTrace tailWord_6251470 prefixEnd_6251470 1070002969054253776191673 := by
  unfold tailWord_6251470
  simp only [CollatzResearch.WordTrace]
  refine ⟨28501230332749916364983983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152006561774666220613247909 28501230332749916364983983)
  ·
    refine ⟨42751845499124874547475975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28501230332749916364983983 42751845499124874547475975)
    ·
      refine ⟨64127768248687311821213963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42751845499124874547475975 64127768248687311821213963)
      ·
        refine ⟨96191652373030967731820945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64127768248687311821213963 96191652373030967731820945)
        ·
          refine ⟨72143739279773225798865709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96191652373030967731820945 72143739279773225798865709)
          ·
            refine ⟨27053902229914959674574641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72143739279773225798865709 27053902229914959674574641)
            ·
              refine ⟨20290426672436219755930981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27053902229914959674574641 20290426672436219755930981)
              ·
                refine ⟨3804455001081791204237059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20290426672436219755930981 3804455001081791204237059)
                ·
                  refine ⟨5706682501622686806355589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804455001081791204237059 5706682501622686806355589)
                  ·
                    refine ⟨1070002969054253776191673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706682501622686806355589 1070002969054253776191673)
                    ·
                      rfl

theorem cell23_6251470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_6251470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251470 prefixEnd_6251470 := by exact prefixLift 6251470
  have htrace : WordTrace (prefixWord ++ tailWord_6251470) baseStart_6251470 baseEnd_6251470 := by
    simpa [prefixWord, tailWord_6251470, baseEnd_6251470] using wordTrace_append hprefix tailTrace_6251470
  have hstable : (prefixWord ++ tailWord_6251470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251470).length < 2 ^ (prefixWord ++ tailWord_6251470).sum := by decide
  have hdescent : baseEnd_6251470 < baseStart_6251470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251479 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 9]
def baseStart_6251479 : Nat := 118140960795 + 6251479 * 2 ^ 59
def prefixEnd_6251479 : Nat := 4983230072969 + 3 ^ 40 * 6251479 * 2
def baseEnd_6251479 : Nat := 1070004509496217264454159

theorem tailTrace_6251479 : CollatzResearch.WordTrace tailWord_6251479 prefixEnd_6251479 1070004509496217264454159 := by
  unfold tailWord_6251479
  simp only [CollatzResearch.WordTrace]
  refine ⟨228010170918966725456949491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152006780612644483637966327 228010170918966725456949491)
  ·
    refine ⟨342015256378450088185424237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228010170918966725456949491 342015256378450088185424237)
    ·
      refine ⟨128255721141918783069534089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342015256378450088185424237 128255721141918783069534089)
      ·
        refine ⟨96191790856439087302150567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128255721141918783069534089 96191790856439087302150567)
        ·
          refine ⟨144287686284658630953225851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96191790856439087302150567 144287686284658630953225851)
          ·
            refine ⟨216431529426987946429838777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144287686284658630953225851 216431529426987946429838777)
            ·
              refine ⟨162323647070240959822379083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216431529426987946429838777 162323647070240959822379083)
              ·
                refine ⟨243485470605361439733568625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162323647070240959822379083 243485470605361439733568625)
                ·
                  refine ⟨182614102954021079800176469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243485470605361439733568625 182614102954021079800176469)
                  ·
                    refine ⟨1070004509496217264454159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182614102954021079800176469 1070004509496217264454159)
                    ·
                      rfl

theorem cell23_6251479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_6251479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251479 prefixEnd_6251479 := by exact prefixLift 6251479
  have htrace : WordTrace (prefixWord ++ tailWord_6251479) baseStart_6251479 baseEnd_6251479 := by
    simpa [prefixWord, tailWord_6251479, baseEnd_6251479] using wordTrace_append hprefix tailTrace_6251479
  have hstable : (prefixWord ++ tailWord_6251479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251479).length < 2 ^ (prefixWord ++ tailWord_6251479).sum := by decide
  have hdescent : baseEnd_6251479 < baseStart_6251479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251496 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6251496 : Nat := 118140960795 + 6251496 * 2 ^ 59
def prefixEnd_6251496 : Nat := 4983230072969 + 3 ^ 40 * 6251496 * 2
def baseEnd_6251496 : Nat := 1070007419219926075616633

theorem tailTrace_6251496 : CollatzResearch.WordTrace tailWord_6251496 prefixEnd_6251496 1070007419219926075616633 := by
  unfold tailWord_6251496
  simp only [CollatzResearch.WordTrace]
  refine ⟨114005395479952568680159171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152007193973270091573545561 114005395479952568680159171)
  ·
    refine ⟨171008093219928853020238757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114005395479952568680159171 171008093219928853020238757)
    ·
      refine ⟨32064017478736659941294767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171008093219928853020238757 32064017478736659941294767)
      ·
        refine ⟨48096026218104989911942151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32064017478736659941294767 48096026218104989911942151)
        ·
          refine ⟨72144039327157484867913227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48096026218104989911942151 72144039327157484867913227)
          ·
            refine ⟨108216058990736227301869841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72144039327157484867913227 108216058990736227301869841)
            ·
              refine ⟨81162044243052170476402381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108216058990736227301869841 81162044243052170476402381)
              ·
                refine ⟨30435766591144563928650893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81162044243052170476402381 30435766591144563928650893)
                ·
                  refine ⟨11413412471679211473244085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30435766591144563928650893 11413412471679211473244085)
                  ·
                    refine ⟨1070007419219926075616633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11413412471679211473244085 1070007419219926075616633)
                    ·
                      rfl

theorem cell23_6251496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6251496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251496 prefixEnd_6251496 := by exact prefixLift 6251496
  have htrace : WordTrace (prefixWord ++ tailWord_6251496) baseStart_6251496 baseEnd_6251496 := by
    simpa [prefixWord, tailWord_6251496, baseEnd_6251496] using wordTrace_append hprefix tailTrace_6251496
  have hstable : (prefixWord ++ tailWord_6251496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251496).length < 2 ^ (prefixWord ++ tailWord_6251496).sum := by decide
  have hdescent : baseEnd_6251496 < baseStart_6251496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251503 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 5, 2]
def baseStart_6251503 : Nat := 118140960795 + 6251503 * 2 ^ 59
def prefixEnd_6251503 : Nat := 4983230072969 + 3 ^ 40 * 6251503 * 2
def baseEnd_6251503 : Nat := 3210025852024359699462367

theorem tailTrace_6251503 : CollatzResearch.WordTrace tailWord_6251503 prefixEnd_6251503 3210025852024359699462367 := by
  unfold tailWord_6251503
  simp only [CollatzResearch.WordTrace]
  refine ⟨228011046270879777555823163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152007364180586518370548775 228011046270879777555823163)
  ·
    refine ⟨342016569406319666333734745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228011046270879777555823163 342016569406319666333734745)
    ·
      refine ⟨256512427054739749750301059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342016569406319666333734745 256512427054739749750301059)
      ·
        refine ⟨384768640582109624625451589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256512427054739749750301059 384768640582109624625451589)
        ·
          refine ⟨72144120109145554617272173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384768640582109624625451589 72144120109145554617272173)
          ·
            refine ⟨27054045040929582981477065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72144120109145554617272173 27054045040929582981477065)
            ·
              refine ⟨20290533780697187236107799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27054045040929582981477065 20290533780697187236107799)
              ·
                refine ⟨30435800671045780854161699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20290533780697187236107799 30435800671045780854161699)
                ·
                  refine ⟨45653701006568671281242549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30435800671045780854161699 45653701006568671281242549)
                  ·
                    refine ⟨4280034469365812932616489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45653701006568671281242549 4280034469365812932616489)
                    ·
                      refine ⟨3210025852024359699462367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280034469365812932616489 3210025852024359699462367)
                      ·
                        rfl

theorem cell23_6251503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5, 2].length) (baseStart_6251503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251503 prefixEnd_6251503 := by exact prefixLift 6251503
  have htrace : WordTrace (prefixWord ++ tailWord_6251503) baseStart_6251503 baseEnd_6251503 := by
    simpa [prefixWord, tailWord_6251503, baseEnd_6251503] using wordTrace_append hprefix tailTrace_6251503
  have hstable : (prefixWord ++ tailWord_6251503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251503).length < 2 ^ (prefixWord ++ tailWord_6251503).sum := by decide
  have hdescent : baseEnd_6251503 < baseStart_6251503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251546 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_6251546 : Nat := 118140960795 + 6251546 * 2 ^ 59
def prefixEnd_6251546 : Nat := 4983230072969 + 3 ^ 40 * 6251546 * 2
def baseEnd_6251546 : Nat := 3210047931692503031224669

theorem tailTrace_6251546 : CollatzResearch.WordTrace tailWord_6251546 prefixEnd_6251546 3210047931692503031224669 := by
  unfold tailWord_6251546
  simp only [CollatzResearch.WordTrace]
  refine ⟨57003153652430998974909623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152008409739815997266425661 57003153652430998974909623)
  ·
    refine ⟨85504730478646498462364435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57003153652430998974909623 85504730478646498462364435)
    ·
      refine ⟨128257095717969747693546653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85504730478646498462364435 128257095717969747693546653)
      ·
        refine ⟨48096410894238655385079995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128257095717969747693546653 48096410894238655385079995)
        ·
          refine ⟨72144616341357983077619993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48096410894238655385079995 72144616341357983077619993)
          ·
            refine ⟨54108462256018487308214995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72144616341357983077619993 54108462256018487308214995)
            ·
              refine ⟨81162693384027730962322493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54108462256018487308214995 81162693384027730962322493)
              ·
                refine ⟨30436010019010399110870935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81162693384027730962322493 30436010019010399110870935)
                ·
                  refine ⟨45654015028515598666306403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30436010019010399110870935 45654015028515598666306403)
                  ·
                    refine ⟨68481022542773397999459605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45654015028515598666306403 68481022542773397999459605)
                    ·
                      refine ⟨3210047931692503031224669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68481022542773397999459605 3210047931692503031224669)
                      ·
                        rfl

theorem cell23_6251546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_6251546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251546 prefixEnd_6251546 := by exact prefixLift 6251546
  have htrace : WordTrace (prefixWord ++ tailWord_6251546) baseStart_6251546 baseEnd_6251546 := by
    simpa [prefixWord, tailWord_6251546, baseEnd_6251546] using wordTrace_append hprefix tailTrace_6251546
  have hstable : (prefixWord ++ tailWord_6251546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251546).length < 2 ^ (prefixWord ++ tailWord_6251546).sum := by decide
  have hdescent : baseEnd_6251546 < baseStart_6251546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251590 : List Nat := [6, 1, 1, 1, 1, 2, 3, 8]
def baseStart_6251590 : Nat := 118140960795 + 6251590 * 2 ^ 59
def prefixEnd_6251590 : Nat := 4983230072969 + 3 ^ 40 * 6251590 * 2
def baseEnd_6251590 : Nat := 118891500920048179965721

theorem tailTrace_6251590 : CollatzResearch.WordTrace tailWord_6251590 prefixEnd_6251590 118891500920048179965721 := by
  unfold tailWord_6251590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125444356923893481695007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152009479614376394276160149 7125444356923893481695007)
  ·
    refine ⟨10688166535385840222542511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7125444356923893481695007 10688166535385840222542511)
    ·
      refine ⟨16032249803078760333813767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10688166535385840222542511 16032249803078760333813767)
      ·
        refine ⟨24048374704618140500720651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16032249803078760333813767 24048374704618140500720651)
        ·
          refine ⟨36072562056927210751080977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24048374704618140500720651 36072562056927210751080977)
          ·
            refine ⟨27054421542695408063310733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36072562056927210751080977 27054421542695408063310733)
            ·
              refine ⟨10145408078510778023741525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27054421542695408063310733 10145408078510778023741525)
              ·
                refine ⟨118891500920048179965721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10145408078510778023741525 118891500920048179965721)
                ·
                  rfl

theorem cell23_6251590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_6251590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251590 prefixEnd_6251590 := by exact prefixLift 6251590
  have htrace : WordTrace (prefixWord ++ tailWord_6251590) baseStart_6251590 baseEnd_6251590 := by
    simpa [prefixWord, tailWord_6251590, baseEnd_6251590] using wordTrace_append hprefix tailTrace_6251590
  have hstable : (prefixWord ++ tailWord_6251590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251590).length < 2 ^ (prefixWord ++ tailWord_6251590).sum := by decide
  have hdescent : baseEnd_6251590 < baseStart_6251590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251596 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6251596 : Nat := 118140960795 + 6251596 * 2 ^ 59
def prefixEnd_6251596 : Nat := 4983230072969 + 3 ^ 40 * 6251596 * 2
def baseEnd_6251596 : Nat := 3210073605725227835599439

theorem tailTrace_6251596 : CollatzResearch.WordTrace tailWord_6251596 prefixEnd_6251596 3210073605725227835599439 := by
  unfold tailWord_6251596
  simp only [CollatzResearch.WordTrace]
  refine ⟨114007219129771427219479321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152009625506361902959305761 114007219129771427219479321)
  ·
    refine ⟨85505414347328570414609491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114007219129771427219479321 85505414347328570414609491)
    ·
      refine ⟨128258121520992855621914237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85505414347328570414609491 128258121520992855621914237)
      ·
        refine ⟨48096795570372320858217839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128258121520992855621914237 48096795570372320858217839)
        ·
          refine ⟨72145193355558481287326759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48096795570372320858217839 72145193355558481287326759)
          ·
            refine ⟨108217790033337721930990139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72145193355558481287326759 108217790033337721930990139)
            ·
              refine ⟨162326685050006582896485209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108217790033337721930990139 162326685050006582896485209)
              ·
                refine ⟨121745013787504937172363907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162326685050006582896485209 121745013787504937172363907)
                ·
                  refine ⟨182617520681257405758545861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121745013787504937172363907 182617520681257405758545861)
                  ·
                    refine ⟨34240785127735763579727349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182617520681257405758545861 34240785127735763579727349)
                    ·
                      refine ⟨3210073605725227835599439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34240785127735763579727349 3210073605725227835599439)
                      ·
                        rfl

theorem cell23_6251596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6251596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251596 prefixEnd_6251596 := by exact prefixLift 6251596
  have htrace : WordTrace (prefixWord ++ tailWord_6251596) baseStart_6251596 baseEnd_6251596 := by
    simpa [prefixWord, tailWord_6251596, baseEnd_6251596] using wordTrace_append hprefix tailTrace_6251596
  have hstable : (prefixWord ++ tailWord_6251596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251596).length < 2 ^ (prefixWord ++ tailWord_6251596).sum := by decide
  have hdescent : baseEnd_6251596 < baseStart_6251596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251616 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_6251616 : Nat := 118140960795 + 6251616 * 2 ^ 59
def prefixEnd_6251616 : Nat := 4983230072969 + 3 ^ 40 * 6251616 * 2
def baseEnd_6251616 : Nat := 1070027958446105919116449

theorem tailTrace_6251616 : CollatzResearch.WordTrace tailWord_6251616 prefixEnd_6251616 1070027958446105919116449 := by
  unfold tailWord_6251616
  simp only [CollatzResearch.WordTrace]
  refine ⟨114007583859735198927343351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152010111812980265236457801 114007583859735198927343351)
  ·
    refine ⟨171011375789602798391015027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114007583859735198927343351 171011375789602798391015027)
    ·
      refine ⟨256517063684404197586522541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171011375789602798391015027 256517063684404197586522541)
      ·
        refine ⟨96193898881651574094945953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256517063684404197586522541 96193898881651574094945953)
        ·
          refine ⟨72145424161238680571209465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96193898881651574094945953 72145424161238680571209465)
          ·
            refine ⟨54109068120929010428407099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72145424161238680571209465 54109068120929010428407099)
            ·
              refine ⟨81163602181393515642610649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54109068120929010428407099 81163602181393515642610649)
              ·
                refine ⟨60872701636045136731957987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81163602181393515642610649 60872701636045136731957987)
                ·
                  refine ⟨91309052454067705097936981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60872701636045136731957987 91309052454067705097936981)
                  ·
                    refine ⟨1070027958446105919116449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91309052454067705097936981 1070027958446105919116449)
                    ·
                      rfl

theorem cell23_6251616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_6251616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251616 prefixEnd_6251616 := by exact prefixLift 6251616
  have htrace : WordTrace (prefixWord ++ tailWord_6251616) baseStart_6251616 baseEnd_6251616 := by
    simpa [prefixWord, tailWord_6251616, baseEnd_6251616] using wordTrace_append hprefix tailTrace_6251616
  have hstable : (prefixWord ++ tailWord_6251616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251616).length < 2 ^ (prefixWord ++ tailWord_6251616).sum := by decide
  have hdescent : baseEnd_6251616 < baseStart_6251616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251657 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 1, 4, 2]
def baseStart_6251657 : Nat := 118140960795 + 6251657 * 2 ^ 59
def prefixEnd_6251657 : Nat := 4983230072969 + 3 ^ 40 * 6251657 * 2
def baseEnd_6251657 : Nat := 3210104928045152096936659

theorem tailTrace_6251657 : CollatzResearch.WordTrace tailWord_6251657 prefixEnd_6251657 3210104928045152096936659 := by
  unfold tailWord_6251657
  simp only [CollatzResearch.WordTrace]
  refine ⟨228016663112321861856929225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152011108741547907904619483 228016663112321861856929225)
  ·
    refine ⟨171012497334241396392696919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228016663112321861856929225 171012497334241396392696919)
    ·
      refine ⟨256518746001362094589045379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171012497334241396392696919 256518746001362094589045379)
      ·
        refine ⟨384778119002043141883568069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256518746001362094589045379 384778119002043141883568069)
        ·
          refine ⟨72145897312883089103169013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384778119002043141883568069 72145897312883089103169013)
          ·
            refine ⟨6763677873082789603422095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72145897312883089103169013 6763677873082789603422095)
            ·
              refine ⟨10145516809624184405133143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763677873082789603422095 10145516809624184405133143)
              ·
                refine ⟨15218275214436276607699715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145516809624184405133143 15218275214436276607699715)
                ·
                  refine ⟨22827412821654414911549573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15218275214436276607699715 22827412821654414911549573)
                  ·
                    refine ⟨4280139904060202795915545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22827412821654414911549573 4280139904060202795915545)
                    ·
                      refine ⟨3210104928045152096936659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280139904060202795915545 3210104928045152096936659)
                      ·
                        rfl

theorem cell23_6251657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4, 2].length) (baseStart_6251657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251657 prefixEnd_6251657 := by exact prefixLift 6251657
  have htrace : WordTrace (prefixWord ++ tailWord_6251657) baseStart_6251657 baseEnd_6251657 := by
    simpa [prefixWord, tailWord_6251657, baseEnd_6251657] using wordTrace_append hprefix tailTrace_6251657
  have hstable : (prefixWord ++ tailWord_6251657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251657).length < 2 ^ (prefixWord ++ tailWord_6251657).sum := by decide
  have hdescent : baseEnd_6251657 < baseStart_6251657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251703 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_6251703 : Nat := 118140960795 + 6251703 * 2 ^ 59
def prefixEnd_6251703 : Nat := 4983230072969 + 3 ^ 40 * 6251703 * 2
def baseEnd_6251703 : Nat := 3210128548155258916961447

theorem tailTrace_6251703 : CollatzResearch.WordTrace tailWord_6251703 prefixEnd_6251703 3210128548155258916961447 := by
  unfold tailWord_6251703
  simp only [CollatzResearch.WordTrace]
  refine ⟨228018340870155211713103763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152012227246770141142069175 228018340870155211713103763)
  ·
    refine ⟨342027511305232817569655645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228018340870155211713103763 342027511305232817569655645)
    ·
      refine ⟨128260316739462306588620867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342027511305232817569655645 128260316739462306588620867)
      ·
        refine ⟨192390475109193459882931301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128260316739462306588620867 192390475109193459882931301)
        ·
          refine ⟨36073214082973773728049619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192390475109193459882931301 36073214082973773728049619)
          ·
            refine ⟨54109821124460660592074429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36073214082973773728049619 54109821124460660592074429)
            ·
              refine ⟨20291182921672747722027911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54109821124460660592074429 20291182921672747722027911)
              ·
                refine ⟨30436774382509121583041867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20291182921672747722027911 30436774382509121583041867)
                ·
                  refine ⟨45655161573763682374562801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30436774382509121583041867 45655161573763682374562801)
                  ·
                    refine ⟨34241371180322761780922101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45655161573763682374562801 34241371180322761780922101)
                    ·
                      refine ⟨3210128548155258916961447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34241371180322761780922101 3210128548155258916961447)
                      ·
                        rfl

theorem cell23_6251703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_6251703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251703 prefixEnd_6251703 := by exact prefixLift 6251703
  have htrace : WordTrace (prefixWord ++ tailWord_6251703) baseStart_6251703 baseEnd_6251703 := by
    simpa [prefixWord, tailWord_6251703, baseEnd_6251703] using wordTrace_append hprefix tailTrace_6251703
  have hstable : (prefixWord ++ tailWord_6251703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251703).length < 2 ^ (prefixWord ++ tailWord_6251703).sum := by decide
  have hdescent : baseEnd_6251703 < baseStart_6251703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251784 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_6251784 : Nat := 118140960795 + 6251784 * 2 ^ 59
def prefixEnd_6251784 : Nat := 4983230072969 + 3 ^ 40 * 6251784 * 2
def baseEnd_6251784 : Nat := 3210170140088273100048575

theorem tailTrace_6251784 : CollatzResearch.WordTrace tailWord_6251784 prefixEnd_6251784 3210170140088273100048575 := by
  unfold tailWord_6251784
  simp only [CollatzResearch.WordTrace]
  refine ⟨114010647591430881273401203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152014196788574508364534937 114010647591430881273401203)
  ·
    refine ⟨171015971387146321910101805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114010647591430881273401203 171015971387146321910101805)
    ·
      refine ⟨64130989270179870716288177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171015971387146321910101805 64130989270179870716288177)
      ·
        refine ⟨48098241952634903037216133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64130989270179870716288177 48098241952634903037216133)
        ·
          refine ⟨9018420366119044319478025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48098241952634903037216133 9018420366119044319478025)
          ·
            refine ⟨6763815274589283239608519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9018420366119044319478025 6763815274589283239608519)
            ·
              refine ⟨10145722911883924859412779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763815274589283239608519 10145722911883924859412779)
              ·
                refine ⟨15218584367825887289119169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145722911883924859412779 15218584367825887289119169)
                ·
                  refine ⟨11413938275869415466839377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15218584367825887289119169 11413938275869415466839377)
                  ·
                    refine ⟨8560453706902061600129533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11413938275869415466839377 8560453706902061600129533)
                    ·
                      refine ⟨3210170140088273100048575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8560453706902061600129533 3210170140088273100048575)
                      ·
                        rfl

theorem cell23_6251784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_6251784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251784 prefixEnd_6251784 := by exact prefixLift 6251784
  have htrace : WordTrace (prefixWord ++ tailWord_6251784) baseStart_6251784 baseEnd_6251784 := by
    simpa [prefixWord, tailWord_6251784, baseEnd_6251784] using wordTrace_append hprefix tailTrace_6251784
  have hstable : (prefixWord ++ tailWord_6251784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251784).length < 2 ^ (prefixWord ++ tailWord_6251784).sum := by decide
  have hdescent : baseEnd_6251784 < baseStart_6251784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251850 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_6251850 : Nat := 118140960795 + 6251850 * 2 ^ 59
def prefixEnd_6251850 : Nat := 4983230072969 + 3 ^ 40 * 6251850 * 2
def baseEnd_6251850 : Nat := 3210204029811469841823271

theorem tailTrace_6251850 : CollatzResearch.WordTrace tailWord_6251850 prefixEnd_6251850 3210204029811469841823271 := by
  unfold tailWord_6251850
  simp only [CollatzResearch.WordTrace]
  refine ⟨57005925600155663954676251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152015801600415103879136669 57005925600155663954676251)
  ·
    refine ⟨85508888400233495932014377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57005925600155663954676251 85508888400233495932014377)
    ·
      refine ⟨64131666300175121949010783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85508888400233495932014377 64131666300175121949010783)
      ·
        refine ⟨96197499450262682923516175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64131666300175121949010783 96197499450262682923516175)
        ·
          refine ⟨144296249175394024385274263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96197499450262682923516175 144296249175394024385274263)
          ·
            refine ⟨216444373763091036577911395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144296249175394024385274263 216444373763091036577911395)
            ·
              refine ⟨324666560644636554866867093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216444373763091036577911395 324666560644636554866867093)
              ·
                refine ⟨15218745030217338509384395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324666560644636554866867093 15218745030217338509384395)
                ·
                  refine ⟨22828117545326007764076593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15218745030217338509384395 22828117545326007764076593)
                  ·
                    refine ⟨17121088158994505823057445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22828117545326007764076593 17121088158994505823057445)
                    ·
                      refine ⟨3210204029811469841823271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17121088158994505823057445 3210204029811469841823271)
                      ·
                        rfl

theorem cell23_6251850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_6251850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251850 prefixEnd_6251850 := by exact prefixLift 6251850
  have htrace : WordTrace (prefixWord ++ tailWord_6251850) baseStart_6251850 baseEnd_6251850 := by
    simpa [prefixWord, tailWord_6251850, baseEnd_6251850] using wordTrace_append hprefix tailTrace_6251850
  have hstable : (prefixWord ++ tailWord_6251850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251850).length < 2 ^ (prefixWord ++ tailWord_6251850).sum := by decide
  have hdescent : baseEnd_6251850 < baseStart_6251850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251857 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_6251857 : Nat := 118140960795 + 6251857 * 2 ^ 59
def prefixEnd_6251857 : Nat := 4983230072969 + 3 ^ 40 * 6251857 * 2
def baseEnd_6251857 : Nat := 3210207624176051314435739

theorem tailTrace_6251857 : CollatzResearch.WordTrace tailWord_6251857 prefixEnd_6251857 3210207624176051314435739 := by
  unfold tailWord_6251857
  simp only [CollatzResearch.WordTrace]
  refine ⟨228023957711597296014209825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152015971807731530676139883 228023957711597296014209825)
  ·
    refine ⟨171017968283697972010657369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228023957711597296014209825 171017968283697972010657369)
    ·
      refine ⟨128263476212773479007993027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171017968283697972010657369 128263476212773479007993027)
      ·
        refine ⟨192395214319160218511989541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128263476212773479007993027 192395214319160218511989541)
        ·
          refine ⟨36074102684842540970998039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192395214319160218511989541 36074102684842540970998039)
          ·
            refine ⟨54111154027263811456497059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36074102684842540970998039 54111154027263811456497059)
            ·
              refine ⟨81166731040895717184745589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54111154027263811456497059 81166731040895717184745589)
              ·
                refine ⟨7609381035083973486069899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81166731040895717184745589 7609381035083973486069899)
                ·
                  refine ⟨11414071552625960229104849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7609381035083973486069899 11414071552625960229104849)
                  ·
                    refine ⟨8560553664469470171828637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11414071552625960229104849 8560553664469470171828637)
                    ·
                      refine ⟨3210207624176051314435739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8560553664469470171828637 3210207624176051314435739)
                      ·
                        rfl

theorem cell23_6251857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_6251857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251857 prefixEnd_6251857 := by exact prefixLift 6251857
  have htrace : WordTrace (prefixWord ++ tailWord_6251857) baseStart_6251857 baseEnd_6251857 := by
    simpa [prefixWord, tailWord_6251857, baseEnd_6251857] using wordTrace_append hprefix tailTrace_6251857
  have hstable : (prefixWord ++ tailWord_6251857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251857).length < 2 ^ (prefixWord ++ tailWord_6251857).sum := by decide
  have hdescent : baseEnd_6251857 < baseStart_6251857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
