import V185TrunkScan23Chunk0983

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5825407 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 1, 2, 3]
def baseStart_5825407 : Nat := 118140960795 + 5825407 * 2 ^ 59
def prefixEnd_5825407 : Nat := 4983230072969 + 3 ^ 40 * 5825407 * 2
def baseEnd_5825407 : Nat := 2991233799066194802021947

theorem tailTrace_5825407 : CollatzResearch.WordTrace tailWord_5825407 prefixEnd_5825407 2991233799066194802021947 := by
  unfold tailWord_5825407
  simp only [CollatzResearch.WordTrace]
  refine ⟨212470048406552814152650475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141646698937701876101766983 212470048406552814152650475)
  ·
    refine ⟨318705072609829221228975713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212470048406552814152650475 318705072609829221228975713)
    ·
      refine ⟨239028804457371915921731785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318705072609829221228975713 239028804457371915921731785)
      ·
        refine ⟨179271603343028936941298839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239028804457371915921731785 179271603343028936941298839)
        ·
          refine ⟨268907405014543405411948259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179271603343028936941298839 268907405014543405411948259)
          ·
            refine ⟨403361107521815108117922389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268907405014543405411948259 403361107521815108117922389)
            ·
              refine ⟨4726887978771270798256903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 403361107521815108117922389 4726887978771270798256903)
              ·
                refine ⟨7090331968156906197385355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726887978771270798256903 7090331968156906197385355)
                ·
                  refine ⟨10635497952235359296078033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7090331968156906197385355 10635497952235359296078033)
                  ·
                    refine ⟨7976623464176519472058525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10635497952235359296078033 7976623464176519472058525)
                    ·
                      refine ⟨2991233799066194802021947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976623464176519472058525 2991233799066194802021947)
                      ·
                        rfl

theorem cell23_5825407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_5825407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825407 prefixEnd_5825407 := by exact prefixLift 5825407
  have htrace : WordTrace (prefixWord ++ tailWord_5825407) baseStart_5825407 baseEnd_5825407 := by
    simpa [prefixWord, tailWord_5825407, baseEnd_5825407] using wordTrace_append hprefix tailTrace_5825407
  have hstable : (prefixWord ++ tailWord_5825407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825407).length < 2 ^ (prefixWord ++ tailWord_5825407).sum := by decide
  have hdescent : baseEnd_5825407 < baseStart_5825407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825434 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5825434 : Nat := 118140960795 + 5825434 * 2 ^ 59
def prefixEnd_5825434 : Nat := 4983230072969 + 3 ^ 40 * 5825434 * 2
def baseEnd_5825434 : Nat := 2991247663043866196384323

theorem tailTrace_5825434 : CollatzResearch.WordTrace tailWord_5825434 prefixEnd_5825434 2991247663043866196384323 := by
  unfold tailWord_5825434
  simp only [CollatzResearch.WordTrace]
  refine ⟨53117758294363749440970839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141647355451636665175922237 53117758294363749440970839)
  ·
    refine ⟨79676637441545624161456259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53117758294363749440970839 79676637441545624161456259)
    ·
      refine ⟨119514956162318436242184389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79676637441545624161456259 119514956162318436242184389)
      ·
        refine ⟨22409054280434706795409573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119514956162318436242184389 22409054280434706795409573)
        ·
          refine ⟨4201697677581507524139295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22409054280434706795409573 4201697677581507524139295)
          ·
            refine ⟨6302546516372261286208943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201697677581507524139295 6302546516372261286208943)
            ·
              refine ⟨9453819774558391929313415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302546516372261286208943 9453819774558391929313415)
              ·
                refine ⟨14180729661837587893970123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9453819774558391929313415 14180729661837587893970123)
                ·
                  refine ⟨21271094492756381840955185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14180729661837587893970123 21271094492756381840955185)
                  ·
                    refine ⟨15953320869567286380716389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21271094492756381840955185 15953320869567286380716389)
                    ·
                      refine ⟨2991247663043866196384323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15953320869567286380716389 2991247663043866196384323)
                      ·
                        rfl

theorem cell23_5825434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5825434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825434 prefixEnd_5825434 := by exact prefixLift 5825434
  have htrace : WordTrace (prefixWord ++ tailWord_5825434) baseStart_5825434 baseEnd_5825434 := by
    simpa [prefixWord, tailWord_5825434, baseEnd_5825434] using wordTrace_append hprefix tailTrace_5825434
  have hstable : (prefixWord ++ tailWord_5825434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825434).length < 2 ^ (prefixWord ++ tailWord_5825434).sum := by decide
  have hdescent : baseEnd_5825434 < baseStart_5825434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825443 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_5825443 : Nat := 118140960795 + 5825443 * 2 ^ 59
def prefixEnd_5825443 : Nat := 4983230072969 + 3 ^ 40 * 5825443 * 2
def baseEnd_5825443 : Nat := 2991252284369756661171781

theorem tailTrace_5825443 : CollatzResearch.WordTrace tailWord_5825443 prefixEnd_5825443 2991252284369756661171781 := by
  unfold tailWord_5825443
  simp only [CollatzResearch.WordTrace]
  refine ⟨212471361434422392300960983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141647574289614928200640655 212471361434422392300960983)
  ·
    refine ⟨318707042151633588451441475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212471361434422392300960983 318707042151633588451441475)
    ·
      refine ⟨478060563227450382677162213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318707042151633588451441475 478060563227450382677162213)
      ·
        refine ⟨89636355605146946751967915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 478060563227450382677162213 89636355605146946751967915)
        ·
          refine ⟨134454533407720420127951873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89636355605146946751967915 134454533407720420127951873)
          ·
            refine ⟨100840900055790315095963905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134454533407720420127951873 100840900055790315095963905)
            ·
              refine ⟨75630675041842736321972929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100840900055790315095963905 75630675041842736321972929)
              ·
                refine ⟨56723006281382052241479697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75630675041842736321972929 56723006281382052241479697)
                ·
                  refine ⟨42542254711036539181109773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56723006281382052241479697 42542254711036539181109773)
                  ·
                    refine ⟨15953345516638702192916165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42542254711036539181109773 15953345516638702192916165)
                    ·
                      refine ⟨2991252284369756661171781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15953345516638702192916165 2991252284369756661171781)
                      ·
                        rfl

theorem cell23_5825443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_5825443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825443 prefixEnd_5825443 := by exact prefixLift 5825443
  have htrace : WordTrace (prefixWord ++ tailWord_5825443) baseStart_5825443 baseEnd_5825443 := by
    simpa [prefixWord, tailWord_5825443, baseEnd_5825443] using wordTrace_append hprefix tailTrace_5825443
  have hstable : (prefixWord ++ tailWord_5825443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825443).length < 2 ^ (prefixWord ++ tailWord_5825443).sum := by decide
  have hdescent : baseEnd_5825443 < baseStart_5825443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825463 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_5825463 : Nat := 118140960795 + 5825463 * 2 ^ 59
def prefixEnd_5825463 : Nat := 4983230072969 + 3 ^ 40 * 5825463 * 2
def baseEnd_5825463 : Nat := 2991262553982846582921689

theorem tailTrace_5825463 : CollatzResearch.WordTrace tailWord_5825463 prefixEnd_5825463 2991262553982846582921689 := by
  unfold tailWord_5825463
  simp only [CollatzResearch.WordTrace]
  refine ⟨212472090894349935716689043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141648060596233290477792695 212472090894349935716689043)
  ·
    refine ⟨318708136341524903575033565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212472090894349935716689043 318708136341524903575033565)
    ·
      refine ⟨119515551128071838840637587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318708136341524903575033565 119515551128071838840637587)
      ·
        refine ⟨179273326692107758260956381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119515551128071838840637587 179273326692107758260956381)
        ·
          refine ⟨67227497509540409347858643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179273326692107758260956381 67227497509540409347858643)
          ·
            refine ⟨100841246264310614021787965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67227497509540409347858643 100841246264310614021787965)
            ·
              refine ⟨37815467349116480258170487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100841246264310614021787965 37815467349116480258170487)
              ·
                refine ⟨56723201023674720387255731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37815467349116480258170487 56723201023674720387255731)
                ·
                  refine ⟨85084801535512080580883597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56723201023674720387255731 85084801535512080580883597)
                  ·
                    refine ⟨31906800575817030217831349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85084801535512080580883597 31906800575817030217831349)
                    ·
                      refine ⟨2991262553982846582921689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31906800575817030217831349 2991262553982846582921689)
                      ·
                        rfl

theorem cell23_5825463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_5825463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825463 prefixEnd_5825463 := by exact prefixLift 5825463
  have htrace : WordTrace (prefixWord ++ tailWord_5825463) baseStart_5825463 baseEnd_5825463 := by
    simpa [prefixWord, tailWord_5825463, baseEnd_5825463] using wordTrace_append hprefix tailTrace_5825463
  have hstable : (prefixWord ++ tailWord_5825463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825463).length < 2 ^ (prefixWord ++ tailWord_5825463).sum := by decide
  have hdescent : baseEnd_5825463 < baseStart_5825463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825537 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_5825537 : Nat := 118140960795 + 5825537 * 2 ^ 59
def prefixEnd_5825537 : Nat := 4983230072969 + 3 ^ 40 * 5825537 * 2
def baseEnd_5825537 : Nat := 2991300551551279293396349

theorem tailTrace_5825537 : CollatzResearch.WordTrace tailWord_5825537 prefixEnd_5825537 2991300551551279293396349 := by
  unfold tailWord_5825537
  simp only [CollatzResearch.WordTrace]
  refine ⟨212474789896081846354882865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141649859930721230903255243 212474789896081846354882865)
  ·
    refine ⟨159356092422061384766162149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212474789896081846354882865 159356092422061384766162149)
    ·
      refine ⟨29879267329136509643655403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159356092422061384766162149 29879267329136509643655403)
      ·
        refine ⟨44818900993704764465483105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29879267329136509643655403 44818900993704764465483105)
        ·
          refine ⟨33614175745278573349112329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44818900993704764465483105 33614175745278573349112329)
          ·
            refine ⟨25210631808958930011834247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33614175745278573349112329 25210631808958930011834247)
            ·
              refine ⟨37815947713438395017751371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25210631808958930011834247 37815947713438395017751371)
              ·
                refine ⟨56723921570157592526627057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37815947713438395017751371 56723921570157592526627057)
                ·
                  refine ⟨42542941177618194394970293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56723921570157592526627057 42542941177618194394970293)
                  ·
                    refine ⟨3988400735401705724528465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42542941177618194394970293 3988400735401705724528465)
                    ·
                      refine ⟨2991300551551279293396349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988400735401705724528465 2991300551551279293396349)
                      ·
                        rfl

theorem cell23_5825537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_5825537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825537 prefixEnd_5825537 := by exact prefixLift 5825537
  have htrace : WordTrace (prefixWord ++ tailWord_5825537) baseStart_5825537 baseEnd_5825537 := by
    simpa [prefixWord, tailWord_5825537, baseEnd_5825537] using wordTrace_append hprefix tailTrace_5825537
  have hstable : (prefixWord ++ tailWord_5825537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825537).length < 2 ^ (prefixWord ++ tailWord_5825537).sum := by decide
  have hdescent : baseEnd_5825537 < baseStart_5825537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825564 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_5825564 : Nat := 118140960795 + 5825564 * 2 ^ 59
def prefixEnd_5825564 : Nat := 4983230072969 + 3 ^ 40 * 5825564 * 2
def baseEnd_5825564 : Nat := 997104805176316895919575

theorem tailTrace_5825564 : CollatzResearch.WordTrace tailWord_5825564 prefixEnd_5825564 997104805176316895919575 := by
  unfold tailWord_5825564
  simp only [CollatzResearch.WordTrace]
  refine ⟨106237887333492014983057873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141650516444656019977410497 106237887333492014983057873)
  ·
    refine ⟨79678415500119011237293405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106237887333492014983057873 79678415500119011237293405)
    ·
      refine ⟨29879405812544629213985027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79678415500119011237293405 29879405812544629213985027)
      ·
        refine ⟨44819108718816943820977541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29879405812544629213985027 44819108718816943820977541)
        ·
          refine ⟨8403582884778176966433289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44819108718816943820977541 8403582884778176966433289)
          ·
            refine ⟨6302687163583632724824967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8403582884778176966433289 6302687163583632724824967)
            ·
              refine ⟨9454030745375449087237451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302687163583632724824967 9454030745375449087237451)
              ·
                refine ⟨14181046118063173630856177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454030745375449087237451 14181046118063173630856177)
                ·
                  refine ⟨10635784588547380223142133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14181046118063173630856177 10635784588547380223142133)
                  ·
                    refine ⟨997104805176316895919575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10635784588547380223142133 997104805176316895919575)
                    ·
                      rfl

theorem cell23_5825564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_5825564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825564 prefixEnd_5825564 := by exact prefixLift 5825564
  have htrace : WordTrace (prefixWord ++ tailWord_5825564) baseStart_5825564 baseEnd_5825564 := by
    simpa [prefixWord, tailWord_5825564, baseEnd_5825564] using wordTrace_append hprefix tailTrace_5825564
  have hstable : (prefixWord ++ tailWord_5825564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825564).length < 2 ^ (prefixWord ++ tailWord_5825564).sum := by decide
  have hdescent : baseEnd_5825564 < baseStart_5825564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825567 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_5825567 : Nat := 118140960795 + 5825567 * 2 ^ 59
def prefixEnd_5825567 : Nat := 4983230072969 + 3 ^ 40 * 5825567 * 2
def baseEnd_5825567 : Nat := 2991315955970914176021211

theorem tailTrace_5825567 : CollatzResearch.WordTrace tailWord_5825567 prefixEnd_5825567 2991315955970914176021211 := by
  unfold tailWord_5825567
  simp only [CollatzResearch.WordTrace]
  refine ⟨212475884085973161478474955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141650589390648774318983303 212475884085973161478474955)
  ·
    refine ⟨318713826128959742217712433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212475884085973161478474955 318713826128959742217712433)
    ·
      refine ⟨239035369596719806663284325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318713826128959742217712433 239035369596719806663284325)
      ·
        refine ⟨44819131799384963749365811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239035369596719806663284325 44819131799384963749365811)
        ·
          refine ⟨67228697699077445624048717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44819131799384963749365811 67228697699077445624048717)
          ·
            refine ⟨25210761637154042109018269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67228697699077445624048717 25210761637154042109018269)
            ·
              refine ⟨9454035613932765790881851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25210761637154042109018269 9454035613932765790881851)
              ·
                refine ⟨14181053420899148686322777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454035613932765790881851 14181053420899148686322777)
                ·
                  refine ⟨10635790065674361514742083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14181053420899148686322777 10635790065674361514742083)
                  ·
                    refine ⟨15953685098511542272113125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10635790065674361514742083 15953685098511542272113125)
                    ·
                      refine ⟨2991315955970914176021211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15953685098511542272113125 2991315955970914176021211)
                      ·
                        rfl

theorem cell23_5825567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_5825567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825567 prefixEnd_5825567 := by exact prefixLift 5825567
  have htrace : WordTrace (prefixWord ++ tailWord_5825567) baseStart_5825567 baseEnd_5825567 := by
    simpa [prefixWord, tailWord_5825567, baseEnd_5825567] using wordTrace_append hprefix tailTrace_5825567
  have hstable : (prefixWord ++ tailWord_5825567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825567).length < 2 ^ (prefixWord ++ tailWord_5825567).sum := by decide
  have hdescent : baseEnd_5825567 < baseStart_5825567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825594 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_5825594 : Nat := 118140960795 + 5825594 * 2 ^ 59
def prefixEnd_5825594 : Nat := 4983230072969 + 3 ^ 40 * 5825594 * 2
def baseEnd_5825594 : Nat := 997109939982861856794529

theorem tailTrace_5825594 : CollatzResearch.WordTrace tailWord_5825594 prefixEnd_5825594 997109939982861856794529 := by
  unfold tailWord_5825594
  simp only [CollatzResearch.WordTrace]
  refine ⟨53119217214218836272426959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141651245904583563393138557 53119217214218836272426959)
  ·
    refine ⟨79678825821328254408640439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53119217214218836272426959 79678825821328254408640439)
    ·
      refine ⟨119518238731992381612960659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79678825821328254408640439 119518238731992381612960659)
      ·
        refine ⟨179277358097988572419440989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119518238731992381612960659 179277358097988572419440989)
        ·
          refine ⟨67229009286745714657290371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179277358097988572419440989 67229009286745714657290371)
          ·
            refine ⟨100843513930118571985935557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67229009286745714657290371 100843513930118571985935557)
            ·
              refine ⟨18908158861897232247362917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100843513930118571985935557 18908158861897232247362917)
              ·
                refine ⟨3545279786605731046380547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18908158861897232247362917 3545279786605731046380547)
                ·
                  refine ⟨5317919679908596569570821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545279786605731046380547 5317919679908596569570821)
                  ·
                    refine ⟨997109939982861856794529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5317919679908596569570821 997109939982861856794529)
                    ·
                      rfl

theorem cell23_5825594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_5825594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825594 prefixEnd_5825594 := by exact prefixLift 5825594
  have htrace : WordTrace (prefixWord ++ tailWord_5825594) baseStart_5825594 baseEnd_5825594 := by
    simpa [prefixWord, tailWord_5825594, baseEnd_5825594] using wordTrace_append hprefix tailTrace_5825594
  have hstable : (prefixWord ++ tailWord_5825594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825594).length < 2 ^ (prefixWord ++ tailWord_5825594).sum := by decide
  have hdescent : baseEnd_5825594 < baseStart_5825594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825637 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_5825637 : Nat := 118140960795 + 5825637 * 2 ^ 59
def prefixEnd_5825637 : Nat := 4983230072969 + 3 ^ 40 * 5825637 * 2
def baseEnd_5825637 : Nat := 997117299872242967381963

theorem tailTrace_5825637 : CollatzResearch.WordTrace tailWord_5825637 prefixEnd_5825637 997117299872242967381963 := by
  unfold tailWord_5825637
  simp only [CollatzResearch.WordTrace]
  refine ⟨212478437195719563433523165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141652291463813042289015443 212478437195719563433523165)
  ·
    refine ⟨79679413948394836287571187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212478437195719563433523165 79679413948394836287571187)
    ·
      refine ⟨119519120922592254431356781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79679413948394836287571187 119519120922592254431356781)
      ·
        refine ⟨44819670345972095411758793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119519120922592254431356781 44819670345972095411758793)
        ·
          refine ⟨33614752759479071558819095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44819670345972095411758793 33614752759479071558819095)
          ·
            refine ⟨50422129139218607338228643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33614752759479071558819095 50422129139218607338228643)
            ·
              refine ⟨75633193708827911007342965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50422129139218607338228643 75633193708827911007342965)
              ·
                refine ⟨7090611910202616656938403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75633193708827911007342965 7090611910202616656938403)
                ·
                  refine ⟨10635917865303924985407605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7090611910202616656938403 10635917865303924985407605)
                  ·
                    refine ⟨997117299872242967381963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10635917865303924985407605 997117299872242967381963)
                    ·
                      rfl

theorem cell23_5825637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_5825637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825637 prefixEnd_5825637 := by exact prefixLift 5825637
  have htrace : WordTrace (prefixWord ++ tailWord_5825637) baseStart_5825637 baseEnd_5825637 := by
    simpa [prefixWord, tailWord_5825637, baseEnd_5825637] using wordTrace_append hprefix tailTrace_5825637
  have hstable : (prefixWord ++ tailWord_5825637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825637).length < 2 ^ (prefixWord ++ tailWord_5825637).sum := by decide
  have hdescent : baseEnd_5825637 < baseStart_5825637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825644 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_5825644 : Nat := 118140960795 + 5825644 * 2 ^ 59
def prefixEnd_5825644 : Nat := 4983230072969 + 3 ^ 40 * 5825644 * 2
def baseEnd_5825644 : Nat := 2991355493981310374758357

theorem tailTrace_5825644 : CollatzResearch.WordTrace tailWord_5825644 prefixEnd_5825644 2991355493981310374758357 := by
  unfold tailWord_5825644
  simp only [CollatzResearch.WordTrace]
  refine ⟨106239346253347101814513993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141652461671129469086018657 106239346253347101814513993)
  ·
    refine ⟨79679509690010326360885495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106239346253347101814513993 79679509690010326360885495)
    ·
      refine ⟨119519264535015489541328243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79679509690010326360885495 119519264535015489541328243)
      ·
        refine ⟨179278896802523234311992365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119519264535015489541328243 179278896802523234311992365)
        ·
          refine ⟨67229586300946212866997137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179278896802523234311992365 67229586300946212866997137)
          ·
            refine ⟨50422189725709659650247853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67229586300946212866997137 50422189725709659650247853)
            ·
              refine ⟨18908321147141122368842945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50422189725709659650247853 18908321147141122368842945)
              ·
                refine ⟨14181240860355841776632209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18908321147141122368842945 14181240860355841776632209)
                ·
                  refine ⟨10635930645266881332474157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14181240860355841776632209 10635930645266881332474157)
                  ·
                    refine ⟨3988473991975080499677809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10635930645266881332474157 3988473991975080499677809)
                    ·
                      refine ⟨2991355493981310374758357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988473991975080499677809 2991355493981310374758357)
                      ·
                        rfl

theorem cell23_5825644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_5825644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825644 prefixEnd_5825644 := by exact prefixLift 5825644
  have htrace : WordTrace (prefixWord ++ tailWord_5825644) baseStart_5825644 baseEnd_5825644 := by
    simpa [prefixWord, tailWord_5825644, baseEnd_5825644] using wordTrace_append hprefix tailTrace_5825644
  have hstable : (prefixWord ++ tailWord_5825644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825644).length < 2 ^ (prefixWord ++ tailWord_5825644).sum := by decide
  have hdescent : baseEnd_5825644 < baseStart_5825644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825687 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5825687 : Nat := 118140960795 + 5825687 * 2 ^ 59
def prefixEnd_5825687 : Nat := 4983230072969 + 3 ^ 40 * 5825687 * 2
def baseEnd_5825687 : Nat := 2991377573649453706520659

theorem tailTrace_5825687 : CollatzResearch.WordTrace tailWord_5825687 prefixEnd_5825687 2991377573649453706520659 := by
  unfold tailWord_5825687
  simp only [CollatzResearch.WordTrace]
  refine ⟨212480260845538421972843315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141653507230358947981895543 212480260845538421972843315)
  ·
    refine ⟨318720391268307632959264973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212480260845538421972843315 318720391268307632959264973)
    ·
      refine ⟨119520146725615362359724365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318720391268307632959264973 119520146725615362359724365)
      ·
        refine ⟨44820055022105760884896637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119520146725615362359724365 44820055022105760884896637)
        ·
          refine ⟨16807520633289660331836239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44820055022105760884896637 16807520633289660331836239)
          ·
            refine ⟨25211280949934490497754359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16807520633289660331836239 25211280949934490497754359)
            ·
              refine ⟨37816921424901735746631539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25211280949934490497754359 37816921424901735746631539)
              ·
                refine ⟨56725382137352603619947309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37816921424901735746631539 56725382137352603619947309)
                ·
                  refine ⟨21272018301507226357480241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56725382137352603619947309 21272018301507226357480241)
                  ·
                    refine ⟨15954013726130419768110181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21272018301507226357480241 15954013726130419768110181)
                    ·
                      refine ⟨2991377573649453706520659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15954013726130419768110181 2991377573649453706520659)
                      ·
                        rfl

theorem cell23_5825687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5825687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825687 prefixEnd_5825687 := by exact prefixLift 5825687
  have htrace : WordTrace (prefixWord ++ tailWord_5825687) baseStart_5825687 baseEnd_5825687 := by
    simpa [prefixWord, tailWord_5825687, baseEnd_5825687] using wordTrace_append hprefix tailTrace_5825687
  have hstable : (prefixWord ++ tailWord_5825687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825687).length < 2 ^ (prefixWord ++ tailWord_5825687).sum := by decide
  have hdescent : baseEnd_5825687 < baseStart_5825687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825718 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5825718 : Nat := 118140960795 + 5825718 * 2 ^ 59
def prefixEnd_5825718 : Nat := 4983230072969 + 3 ^ 40 * 5825718 * 2
def baseEnd_5825718 : Nat := 997131163849914361744339

theorem tailTrace_5825718 : CollatzResearch.WordTrace tailWord_5825718 prefixEnd_5825718 997131163849914361744339 := by
  unfold tailWord_5825718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13280086969276632141701363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141654261005617409511481205 13280086969276632141701363)
  ·
    refine ⟨19920130453914948212552045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13280086969276632141701363 19920130453914948212552045)
    ·
      refine ⟨7470048920218105579707017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19920130453914948212552045 7470048920218105579707017)
      ·
        refine ⟨5602536690163579184780263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7470048920218105579707017 5602536690163579184780263)
        ·
          refine ⟨8403805035245368777170395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5602536690163579184780263 8403805035245368777170395)
          ·
            refine ⟨12605707552868053165755593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8403805035245368777170395 12605707552868053165755593)
            ·
              refine ⟨9454280664651039874316695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12605707552868053165755593 9454280664651039874316695)
              ·
                refine ⟨14181420996976559811475043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454280664651039874316695 14181420996976559811475043)
                ·
                  refine ⟨21272131495464839717212565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14181420996976559811475043 21272131495464839717212565)
                  ·
                    refine ⟨997131163849914361744339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21272131495464839717212565 997131163849914361744339)
                    ·
                      rfl

theorem cell23_5825718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5825718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825718 prefixEnd_5825718 := by exact prefixLift 5825718
  have htrace : WordTrace (prefixWord ++ tailWord_5825718) baseStart_5825718 baseEnd_5825718 := by
    simpa [prefixWord, tailWord_5825718, baseEnd_5825718] using wordTrace_append hprefix tailTrace_5825718
  have hstable : (prefixWord ++ tailWord_5825718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825718).length < 2 ^ (prefixWord ++ tailWord_5825718).sum := by decide
  have hdescent : baseEnd_5825718 < baseStart_5825718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825724 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5825724 : Nat := 118140960795 + 5825724 * 2 ^ 59
def prefixEnd_5825724 : Nat := 4983230072969 + 3 ^ 40 * 5825724 * 2
def baseEnd_5825724 : Nat := 2991396572433670061757989

theorem tailTrace_5825724 : CollatzResearch.WordTrace tailWord_5825724 prefixEnd_5825724 2991396572433670061757989 := by
  unfold tailWord_5825724
  simp only [CollatzResearch.WordTrace]
  refine ⟨106240805173202188645970113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141654406897602918194626817 106240805173202188645970113)
  ·
    refine ⟨79680603879901641484477585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106240805173202188645970113 79680603879901641484477585)
    ·
      refine ⟨59760452909926231113358189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79680603879901641484477585 59760452909926231113358189)
      ·
        refine ⟨22410169841222336667509321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59760452909926231113358189 22410169841222336667509321)
        ·
          refine ⟨16807627380916752500631991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22410169841222336667509321 16807627380916752500631991)
          ·
            refine ⟨25211441071375128750947987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16807627380916752500631991 25211441071375128750947987)
            ·
              refine ⟨37817161607062693126421981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25211441071375128750947987 37817161607062693126421981)
              ·
                refine ⟨14181435602648509922408243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37817161607062693126421981 14181435602648509922408243)
                ·
                  refine ⟨21272153403972764883612365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14181435602648509922408243 21272153403972764883612365)
                  ·
                    refine ⟨7977057526489786831354637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21272153403972764883612365 7977057526489786831354637)
                    ·
                      refine ⟨2991396572433670061757989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7977057526489786831354637 2991396572433670061757989)
                      ·
                        rfl

theorem cell23_5825724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5825724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825724 prefixEnd_5825724 := by exact prefixLift 5825724
  have htrace : WordTrace (prefixWord ++ tailWord_5825724) baseStart_5825724 baseEnd_5825724 := by
    simpa [prefixWord, tailWord_5825724, baseEnd_5825724] using wordTrace_append hprefix tailTrace_5825724
  have hstable : (prefixWord ++ tailWord_5825724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825724).length < 2 ^ (prefixWord ++ tailWord_5825724).sum := by decide
  have hdescent : baseEnd_5825724 < baseStart_5825724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825764 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_5825764 : Nat := 118140960795 + 5825764 * 2 ^ 59
def prefixEnd_5825764 : Nat := 4983230072969 + 3 ^ 40 * 5825764 * 2
def baseEnd_5825764 : Nat := 2991417111659849905257805

theorem tailTrace_5825764 : CollatzResearch.WordTrace tailWord_5825764 prefixEnd_5825764 2991417111659849905257805 := by
  unfold tailWord_5825764
  simp only [CollatzResearch.WordTrace]
  refine ⟨106241534633129732061698173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141655379510839642748930897 106241534633129732061698173)
  ·
    refine ⟨39840575487423649523136815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106241534633129732061698173 39840575487423649523136815)
    ·
      refine ⟨59760863231135474284705223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39840575487423649523136815 59760863231135474284705223)
      ·
        refine ⟨89641294846703211427057835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59760863231135474284705223 89641294846703211427057835)
        ·
          refine ⟨134461942270054817140586753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89641294846703211427057835 134461942270054817140586753)
          ·
            refine ⟨100846456702541112855440065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134461942270054817140586753 100846456702541112855440065)
            ·
              refine ⟨75634842526905834641580049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100846456702541112855440065 75634842526905834641580049)
              ·
                refine ⟨56726131895179375981185037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75634842526905834641580049 56726131895179375981185037)
                ·
                  refine ⟨21272299460692265992944389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56726131895179375981185037 21272299460692265992944389)
                  ·
                    refine ⟨3988556148879799873677073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21272299460692265992944389 3988556148879799873677073)
                    ·
                      refine ⟨2991417111659849905257805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988556148879799873677073 2991417111659849905257805)
                      ·
                        rfl

theorem cell23_5825764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_5825764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825764 prefixEnd_5825764 := by exact prefixLift 5825764
  have htrace : WordTrace (prefixWord ++ tailWord_5825764) baseStart_5825764 baseEnd_5825764 := by
    simpa [prefixWord, tailWord_5825764, baseEnd_5825764] using wordTrace_append hprefix tailTrace_5825764
  have hstable : (prefixWord ++ tailWord_5825764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825764).length < 2 ^ (prefixWord ++ tailWord_5825764).sum := by decide
  have hdescent : baseEnd_5825764 < baseStart_5825764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825821 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 7]
def baseStart_5825821 : Nat := 118140960795 + 5825821 * 2 ^ 59
def prefixEnd_5825821 : Nat := 4983230072969 + 3 ^ 40 * 5825821 * 2
def baseEnd_5825821 : Nat := 332382931117461798027227

theorem tailTrace_5825821 : CollatzResearch.WordTrace tailWord_5825821 prefixEnd_5825821 332382931117461798027227 := by
  unfold tailWord_5825821
  simp only [CollatzResearch.WordTrace]
  refine ⟨212485148227052962858221317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141656765484701975238814211 212485148227052962858221317)
  ·
    refine ⟨39840965292572430535916497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212485148227052962858221317 39840965292572430535916497)
    ·
      refine ⟨29880723969429322901937373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39840965292572430535916497 29880723969429322901937373)
      ·
        refine ⟨11205271488535996088226515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29880723969429322901937373 11205271488535996088226515)
        ·
          refine ⟨16807907232803994132339773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11205271488535996088226515 16807907232803994132339773)
          ·
            refine ⟨6302965212301497799627415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16807907232803994132339773 6302965212301497799627415)
            ·
              refine ⟨9454447818452246699441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302965212301497799627415 9454447818452246699441123)
              ·
                refine ⟨14181671727678370049161685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454447818452246699441123 14181671727678370049161685)
                ·
                  refine ⟨332382931117461798027227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14181671727678370049161685 332382931117461798027227)
                  ·
                    rfl

theorem cell23_5825821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_5825821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825821 prefixEnd_5825821 := by exact prefixLift 5825821
  have htrace : WordTrace (prefixWord ++ tailWord_5825821) baseStart_5825821 baseEnd_5825821 := by
    simpa [prefixWord, tailWord_5825821, baseEnd_5825821] using wordTrace_append hprefix tailTrace_5825821
  have hstable : (prefixWord ++ tailWord_5825821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825821).length < 2 ^ (prefixWord ++ tailWord_5825821).sum := by decide
  have hdescent : baseEnd_5825821 < baseStart_5825821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825827 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_5825827 : Nat := 118140960795 + 5825827 * 2 ^ 59
def prefixEnd_5825827 : Nat := 4983230072969 + 3 ^ 40 * 5825827 * 2
def baseEnd_5825827 : Nat := 2991449460941083158770015

theorem tailTrace_5825827 : CollatzResearch.WordTrace tailWord_5825827 prefixEnd_5825827 2991449460941083158770015 := by
  unfold tailWord_5825827
  simp only [CollatzResearch.WordTrace]
  refine ⟨212485367065031225882939735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141656911376687483921959823 212485367065031225882939735)
  ·
    refine ⟨318728050597546838824409603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212485367065031225882939735 318728050597546838824409603)
    ·
      refine ⟨478092075896320258236614405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318728050597546838824409603 478092075896320258236614405)
      ·
        refine ⟨89642264230560048419365201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 478092075896320258236614405 89642264230560048419365201)
        ·
          refine ⟨67231698172920036314523901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89642264230560048419365201 67231698172920036314523901)
          ·
            refine ⟨25211886814845013617946463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67231698172920036314523901 25211886814845013617946463)
            ·
              refine ⟨37817830222267520426919695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25211886814845013617946463 37817830222267520426919695)
              ·
                refine ⟨56726745333401280640379543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37817830222267520426919695 56726745333401280640379543)
                ·
                  refine ⟨85090118000101920960569315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56726745333401280640379543 85090118000101920960569315)
                  ·
                    refine ⟨127635177000152881440853973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85090118000101920960569315 127635177000152881440853973)
                    ·
                      refine ⟨2991449460941083158770015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127635177000152881440853973 2991449460941083158770015)
                      ·
                        rfl

theorem cell23_5825827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_5825827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825827 prefixEnd_5825827 := by exact prefixLift 5825827
  have htrace : WordTrace (prefixWord ++ tailWord_5825827) baseStart_5825827 baseEnd_5825827 := by
    simpa [prefixWord, tailWord_5825827, baseEnd_5825827] using wordTrace_append hprefix tailTrace_5825827
  have hstable : (prefixWord ++ tailWord_5825827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825827).length < 2 ^ (prefixWord ++ tailWord_5825827).sum := by decide
  have hdescent : baseEnd_5825827 < baseStart_5825827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825832 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5825832 : Nat := 118140960795 + 5825832 * 2 ^ 59
def prefixEnd_5825832 : Nat := 4983230072969 + 3 ^ 40 * 5825832 * 2
def baseEnd_5825832 : Nat := 2991452028344355639207493

theorem tailTrace_5825832 : CollatzResearch.WordTrace tailWord_5825832 prefixEnd_5825832 2991452028344355639207493 := by
  unfold tailWord_5825832
  simp only [CollatzResearch.WordTrace]
  refine ⟨106242774715006555868435875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141657032953342074491247833 106242774715006555868435875)
  ·
    refine ⟨159364162072509833802653813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106242774715006555868435875 159364162072509833802653813)
    ·
      refine ⟨14940390194297796918998795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159364162072509833802653813 14940390194297796918998795)
      ·
        refine ⟨22410585291446695378498193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14940390194297796918998795 22410585291446695378498193)
        ·
          refine ⟨16807938968585021533873645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22410585291446695378498193 16807938968585021533873645)
          ·
            refine ⟨6302977113219383075202617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16807938968585021533873645 6302977113219383075202617)
            ·
              refine ⟨4727232834914537306401963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6302977113219383075202617 4727232834914537306401963)
              ·
                refine ⟨7090849252371805959602945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727232834914537306401963 7090849252371805959602945)
                ·
                  refine ⟨5318136939278854469702209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090849252371805959602945 5318136939278854469702209)
                  ·
                    refine ⟨3988602704459140852276657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318136939278854469702209 3988602704459140852276657)
                    ·
                      refine ⟨2991452028344355639207493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988602704459140852276657 2991452028344355639207493)
                      ·
                        rfl

theorem cell23_5825832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5825832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825832 prefixEnd_5825832 := by exact prefixLift 5825832
  have htrace : WordTrace (prefixWord ++ tailWord_5825832) baseStart_5825832 baseEnd_5825832 := by
    simpa [prefixWord, tailWord_5825832, baseEnd_5825832] using wordTrace_append hprefix tailTrace_5825832
  have hstable : (prefixWord ++ tailWord_5825832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825832).length < 2 ^ (prefixWord ++ tailWord_5825832).sum := by decide
  have hdescent : baseEnd_5825832 < baseStart_5825832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825844 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5825844 : Nat := 118140960795 + 5825844 * 2 ^ 59
def prefixEnd_5825844 : Nat := 4983230072969 + 3 ^ 40 * 5825844 * 2
def baseEnd_5825844 : Nat := 2991458190112209592257437

theorem tailTrace_5825844 : CollatzResearch.WordTrace tailWord_5825844 prefixEnd_5825844 2991458190112209592257437 := by
  unfold tailWord_5825844
  simp only [CollatzResearch.WordTrace]
  refine ⟨106242993552984818893154293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141657324737313091857539057 106242993552984818893154293)
  ·
    refine ⟨9960280645592326771233215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106242993552984818893154293 9960280645592326771233215)
    ·
      refine ⟨14940420968388490156849823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9960280645592326771233215 14940420968388490156849823)
      ·
        refine ⟨22410631452582735235274735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14940420968388490156849823 22410631452582735235274735)
        ·
          refine ⟨33615947178874102852912103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22410631452582735235274735 33615947178874102852912103)
          ·
            refine ⟨50423920768311154279368155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33615947178874102852912103 50423920768311154279368155)
            ·
              refine ⟨75635881152466731419052233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50423920768311154279368155 75635881152466731419052233)
              ·
                refine ⟨56726910864350048564289175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75635881152466731419052233 56726910864350048564289175)
                ·
                  refine ⟨85090366296525072846433763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56726910864350048564289175 85090366296525072846433763)
                  ·
                    refine ⟨127635549444787609269650645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85090366296525072846433763 127635549444787609269650645)
                    ·
                      refine ⟨2991458190112209592257437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127635549444787609269650645 2991458190112209592257437)
                      ·
                        rfl

theorem cell23_5825844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5825844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825844 prefixEnd_5825844 := by exact prefixLift 5825844
  have htrace : WordTrace (prefixWord ++ tailWord_5825844) baseStart_5825844 baseEnd_5825844 := by
    simpa [prefixWord, tailWord_5825844, baseEnd_5825844] using wordTrace_append hprefix tailTrace_5825844
  have hstable : (prefixWord ++ tailWord_5825844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825844).length < 2 ^ (prefixWord ++ tailWord_5825844).sum := by decide
  have hdescent : baseEnd_5825844 < baseStart_5825844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825867 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_5825867 : Nat := 118140960795 + 5825867 * 2 ^ 59
def prefixEnd_5825867 : Nat := 4983230072969 + 3 ^ 40 * 5825867 * 2
def baseEnd_5825867 : Nat := 2991470000167263002269831

theorem tailTrace_5825867 : CollatzResearch.WordTrace tailWord_5825867 prefixEnd_5825867 2991470000167263002269831 := by
  unfold tailWord_5825867
  simp only [CollatzResearch.WordTrace]
  refine ⟨212486825984886312714395855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141657883989924208476263903 212486825984886312714395855)
  ·
    refine ⟨318730238977329469071593783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212486825984886312714395855 318730238977329469071593783)
    ·
      refine ⟨478095358465994203607390675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318730238977329469071593783 478095358465994203607390675)
      ·
        refine ⟨717143037698991305411086013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478095358465994203607390675 717143037698991305411086013)
        ·
          refine ⟨268928639137121739529157255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 717143037698991305411086013 268928639137121739529157255)
          ·
            refine ⟨403392958705682609293735883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268928639137121739529157255 403392958705682609293735883)
            ·
              refine ⟨605089438058523913940603825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403392958705682609293735883 605089438058523913940603825)
              ·
                refine ⟨453817078543892935455452869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605089438058523913940603825 453817078543892935455452869)
                ·
                  refine ⟨85090702226979925397897413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453817078543892935455452869 85090702226979925397897413)
                  ·
                    refine ⟨15954506667558736012105765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85090702226979925397897413 15954506667558736012105765)
                    ·
                      refine ⟨2991470000167263002269831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15954506667558736012105765 2991470000167263002269831)
                      ·
                        rfl

theorem cell23_5825867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_5825867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825867 prefixEnd_5825867 := by exact prefixLift 5825867
  have htrace : WordTrace (prefixWord ++ tailWord_5825867) baseStart_5825867 baseEnd_5825867 := by
    simpa [prefixWord, tailWord_5825867, baseEnd_5825867] using wordTrace_append hprefix tailTrace_5825867
  have hstable : (prefixWord ++ tailWord_5825867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825867).length < 2 ^ (prefixWord ++ tailWord_5825867).sum := by decide
  have hdescent : baseEnd_5825867 < baseStart_5825867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825874 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_5825874 : Nat := 118140960795 + 5825874 * 2 ^ 59
def prefixEnd_5825874 : Nat := 4983230072969 + 3 ^ 40 * 5825874 * 2
def baseEnd_5825874 : Nat := 2991473594531844474882299

theorem tailTrace_5825874 : CollatzResearch.WordTrace tailWord_5825874 prefixEnd_5825874 2991473594531844474882299 := by
  unfold tailWord_5825874
  simp only [CollatzResearch.WordTrace]
  refine ⟨53121770323965238227475169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141658054197240635273267117 53121770323965238227475169)
  ·
    refine ⟨39841327742973928670606377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53121770323965238227475169 39841327742973928670606377)
    ·
      refine ⟨29880995807230446502954783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39841327742973928670606377 29880995807230446502954783)
      ·
        refine ⟨44821493710845669754432175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29880995807230446502954783 44821493710845669754432175)
        ·
          refine ⟨67232240566268504631648263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44821493710845669754432175 67232240566268504631648263)
          ·
            refine ⟨100848360849402756947472395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67232240566268504631648263 100848360849402756947472395)
            ·
              refine ⟨151272541274104135421208593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100848360849402756947472395 151272541274104135421208593)
              ·
                refine ⟨113454405955578101565906445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151272541274104135421208593 113454405955578101565906445)
                ·
                  refine ⟨42545402233341788087214917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113454405955578101565906445 42545402233341788087214917)
                  ·
                    refine ⟨7977262918751585266352797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42545402233341788087214917 7977262918751585266352797)
                    ·
                      refine ⟨2991473594531844474882299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7977262918751585266352797 2991473594531844474882299)
                      ·
                        rfl

theorem cell23_5825874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_5825874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825874 prefixEnd_5825874 := by exact prefixLift 5825874
  have htrace : WordTrace (prefixWord ++ tailWord_5825874) baseStart_5825874 baseEnd_5825874 := by
    simpa [prefixWord, tailWord_5825874, baseEnd_5825874] using wordTrace_append hprefix tailTrace_5825874
  have hstable : (prefixWord ++ tailWord_5825874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825874).length < 2 ^ (prefixWord ++ tailWord_5825874).sum := by decide
  have hdescent : baseEnd_5825874 < baseStart_5825874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825897 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_5825897 : Nat := 118140960795 + 5825897 * 2 ^ 59
def prefixEnd_5825897 : Nat := 4983230072969 + 3 ^ 40 * 5825897 * 2
def baseEnd_5825897 : Nat := 2991485404586897884894693

theorem tailTrace_5825897 : CollatzResearch.WordTrace tailWord_5825897 prefixEnd_5825897 2991485404586897884894693 := by
  unfold tailWord_5825897
  simp only [CollatzResearch.WordTrace]
  refine ⟨212487920174777627837987945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141658613449851751891991963 212487920174777627837987945)
  ·
    refine ⟨159365940131083220878490959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212487920174777627837987945 159365940131083220878490959)
    ·
      refine ⟨239048910196624831317736439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159365940131083220878490959 239048910196624831317736439)
      ·
        refine ⟨358573365294937246976604659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239048910196624831317736439 358573365294937246976604659)
        ·
          refine ⟨537860047942405870464906989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358573365294937246976604659 537860047942405870464906989)
          ·
            refine ⟨201697517978402201424340121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537860047942405870464906989 201697517978402201424340121)
            ·
              refine ⟨151273138483801651068255091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201697517978402201424340121 151273138483801651068255091)
              ·
                refine ⟨226909707725702476602382637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151273138483801651068255091 226909707725702476602382637)
                ·
                  refine ⟨85091140397138428725893489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226909707725702476602382637 85091140397138428725893489)
                  ·
                    refine ⟨63818355297853821544420117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85091140397138428725893489 63818355297853821544420117)
                    ·
                      refine ⟨2991485404586897884894693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63818355297853821544420117 2991485404586897884894693)
                      ·
                        rfl

theorem cell23_5825897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_5825897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825897 prefixEnd_5825897 := by exact prefixLift 5825897
  have htrace : WordTrace (prefixWord ++ tailWord_5825897) baseStart_5825897 baseEnd_5825897 := by
    simpa [prefixWord, tailWord_5825897, baseEnd_5825897] using wordTrace_append hprefix tailTrace_5825897
  have hstable : (prefixWord ++ tailWord_5825897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825897).length < 2 ^ (prefixWord ++ tailWord_5825897).sum := by decide
  have hdescent : baseEnd_5825897 < baseStart_5825897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825898 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_5825898 : Nat := 118140960795 + 5825898 * 2 ^ 59
def prefixEnd_5825898 : Nat := 4983230072969 + 3 ^ 40 * 5825898 * 2
def baseEnd_5825898 : Nat := 997161972689184126994063

theorem tailTrace_5825898 : CollatzResearch.WordTrace tailWord_5825898 prefixEnd_5825898 997161972689184126994063 := by
  unfold tailWord_5825898
  simp only [CollatzResearch.WordTrace]
  refine ⟨53121989161943501252193587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141658637765182670005849565 53121989161943501252193587)
  ·
    refine ⟨79682983742915251878290381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53121989161943501252193587 79682983742915251878290381)
    ·
      refine ⟨29881118903593219454358893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79682983742915251878290381 29881118903593219454358893)
      ·
        refine ⟨11205419588847457295384585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29881118903593219454358893 11205419588847457295384585)
        ·
          refine ⟨8404064691635592971538439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11205419588847457295384585 8404064691635592971538439)
          ·
            refine ⟨12606097037453389457307659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404064691635592971538439 12606097037453389457307659)
            ·
              refine ⟨18909145556180084185961489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12606097037453389457307659 18909145556180084185961489)
              ·
                refine ⟨14181859167135063139471117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18909145556180084185961489 14181859167135063139471117)
                ·
                  refine ⟨5318197187675648677301669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14181859167135063139471117 5318197187675648677301669)
                  ·
                    refine ⟨997161972689184126994063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318197187675648677301669 997161972689184126994063)
                    ·
                      rfl

theorem cell23_5825898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_5825898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825898 prefixEnd_5825898 := by exact prefixLift 5825898
  have htrace : WordTrace (prefixWord ++ tailWord_5825898) baseStart_5825898 baseEnd_5825898 := by
    simpa [prefixWord, tailWord_5825898, baseEnd_5825898] using wordTrace_append hprefix tailTrace_5825898
  have hstable : (prefixWord ++ tailWord_5825898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825898).length < 2 ^ (prefixWord ++ tailWord_5825898).sum := by decide
  have hdescent : baseEnd_5825898 < baseStart_5825898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825931 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 4, 3, 2]
def baseStart_5825931 : Nat := 118140960795 + 5825931 * 2 ^ 59
def prefixEnd_5825931 : Nat := 4983230072969 + 3 ^ 40 * 5825931 * 2
def baseEnd_5825931 : Nat := 2991502862929150751869537

theorem tailTrace_5825931 : CollatzResearch.WordTrace tailWord_5825931 prefixEnd_5825931 2991502862929150751869537 := by
  unfold tailWord_5825931
  simp only [CollatzResearch.WordTrace]
  refine ⟨212489160256654451644725647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141659440171102967763150431 212489160256654451644725647)
  ·
    refine ⟨318733740384981677467088471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212489160256654451644725647 318733740384981677467088471)
    ·
      refine ⟨478100610577472516200632707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318733740384981677467088471 478100610577472516200632707)
      ·
        refine ⟨717150915866208774300949061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478100610577472516200632707 717150915866208774300949061)
        ·
          refine ⟨134465796724914145181427949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 717150915866208774300949061 134465796724914145181427949)
          ·
            refine ⟨50424673771842804443035481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134465796724914145181427949 50424673771842804443035481)
            ·
              refine ⟨37818505328882103332276611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50424673771842804443035481 37818505328882103332276611)
              ·
                refine ⟨56727757993323154998414917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37818505328882103332276611 56727757993323154998414917)
                ·
                  refine ⟨10636454623748091562202797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56727757993323154998414917 10636454623748091562202797)
                  ·
                    refine ⟨3988670483905534335826049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10636454623748091562202797 3988670483905534335826049)
                    ·
                      refine ⟨2991502862929150751869537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988670483905534335826049 2991502862929150751869537)
                      ·
                        rfl

theorem cell23_5825931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3, 2].length) (baseStart_5825931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825931 prefixEnd_5825931 := by exact prefixLift 5825931
  have htrace : WordTrace (prefixWord ++ tailWord_5825931) baseStart_5825931 baseEnd_5825931 := by
    simpa [prefixWord, tailWord_5825931, baseEnd_5825931] using wordTrace_append hprefix tailTrace_5825931
  have hstable : (prefixWord ++ tailWord_5825931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825931).length < 2 ^ (prefixWord ++ tailWord_5825931).sum := by decide
  have hdescent : baseEnd_5825931 < baseStart_5825931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825981 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5825981 : Nat := 118140960795 + 5825981 * 2 ^ 59
def prefixEnd_5825981 : Nat := 4983230072969 + 3 ^ 40 * 5825981 * 2
def baseEnd_5825981 : Nat := 2991528536961875556244307

theorem tailTrace_5825981 : CollatzResearch.WordTrace tailWord_5825981 prefixEnd_5825981 2991528536961875556244307 := by
  unfold tailWord_5825981
  simp only [CollatzResearch.WordTrace]
  refine ⟨212490983906473310184045797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141660655937648873456030531 212490983906473310184045797)
  ·
    refine ⟨39842059482463745659508587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212490983906473310184045797 39842059482463745659508587)
    ·
      refine ⟨59763089223695618489262881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39842059482463745659508587 59763089223695618489262881)
      ·
        refine ⟨44822316917771713866947161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59763089223695618489262881 44822316917771713866947161)
        ·
          refine ⟨33616737688328785400210371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44822316917771713866947161 33616737688328785400210371)
          ·
            refine ⟨50425106532493178100315557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33616737688328785400210371 50425106532493178100315557)
            ·
              refine ⟨9454707474842470893809167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50425106532493178100315557 9454707474842470893809167)
              ·
                refine ⟨14182061212263706340713751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454707474842470893809167 14182061212263706340713751)
                ·
                  refine ⟨21273091818395559511070627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14182061212263706340713751 21273091818395559511070627)
                  ·
                    refine ⟨31909637727593339266605941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21273091818395559511070627 31909637727593339266605941)
                    ·
                      refine ⟨2991528536961875556244307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31909637727593339266605941 2991528536961875556244307)
                      ·
                        rfl

theorem cell23_5825981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5825981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825981 prefixEnd_5825981 := by exact prefixLift 5825981
  have htrace : WordTrace (prefixWord ++ tailWord_5825981) baseStart_5825981 baseEnd_5825981 := by
    simpa [prefixWord, tailWord_5825981, baseEnd_5825981] using wordTrace_append hprefix tailTrace_5825981
  have hstable : (prefixWord ++ tailWord_5825981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825981).length < 2 ^ (prefixWord ++ tailWord_5825981).sum := by decide
  have hdescent : baseEnd_5825981 < baseStart_5825981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825988 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5825988 : Nat := 118140960795 + 5825988 * 2 ^ 59
def prefixEnd_5825988 : Nat := 4983230072969 + 3 ^ 40 * 5825988 * 2
def baseEnd_5825988 : Nat := 997177377108819009618925

theorem tailTrace_5825988 : CollatzResearch.WordTrace tailWord_5825988 prefixEnd_5825988 997177377108819009618925 := by
  unfold tailWord_5825988
  simp only [CollatzResearch.WordTrace]
  refine ⟨106245619608723975189775309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141660826144965300253033745 106245619608723975189775309)
  ·
    refine ⟨39842107353271490696165741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106245619608723975189775309 39842107353271490696165741)
    ·
      refine ⟨14940790257476809011062153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39842107353271490696165741 14940790257476809011062153)
      ·
        refine ⟨11205592693107606758296615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14940790257476809011062153 11205592693107606758296615)
        ·
          refine ⟨16808389039661410137444923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11205592693107606758296615 16808389039661410137444923)
          ·
            refine ⟨25212583559492115206167385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16808389039661410137444923 25212583559492115206167385)
            ·
              refine ⟨18909437669619086404625539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25212583559492115206167385 18909437669619086404625539)
              ·
                refine ⟨28364156504428629606938309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18909437669619086404625539 28364156504428629606938309)
                ·
                  refine ⟨5318279344580368051300933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28364156504428629606938309 5318279344580368051300933)
                  ·
                    refine ⟨997177377108819009618925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318279344580368051300933 997177377108819009618925)
                    ·
                      rfl

theorem cell23_5825988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5825988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825988 prefixEnd_5825988 := by exact prefixLift 5825988
  have htrace : WordTrace (prefixWord ++ tailWord_5825988) baseStart_5825988 baseEnd_5825988 := by
    simpa [prefixWord, tailWord_5825988, baseEnd_5825988] using wordTrace_append hprefix tailTrace_5825988
  have hstable : (prefixWord ++ tailWord_5825988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825988).length < 2 ^ (prefixWord ++ tailWord_5825988).sum := by decide
  have hdescent : baseEnd_5825988 < baseStart_5825988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825995 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 1, 2, 2]
def baseStart_5825995 : Nat := 118140960795 + 5825995 * 2 ^ 59
def prefixEnd_5825995 : Nat := 4983230072969 + 3 ^ 40 * 5825995 * 2
def baseEnd_5825995 : Nat := 2991535725691038501469243

theorem tailTrace_5825995 : CollatzResearch.WordTrace tailWord_5825995 prefixEnd_5825995 2991535725691038501469243 := by
  unfold tailWord_5825995
  simp only [CollatzResearch.WordTrace]
  refine ⟨212491494528422590575055439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141660996352281727050036959 212491494528422590575055439)
  ·
    refine ⟨318737241792633885862583159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212491494528422590575055439 318737241792633885862583159)
    ·
      refine ⟨478105862688950828793874739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318737241792633885862583159 478105862688950828793874739)
      ·
        refine ⟨717158794033426243190812109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478105862688950828793874739 717158794033426243190812109)
        ·
          refine ⟨268934547762534841196554541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 717158794033426243190812109 268934547762534841196554541)
          ·
            refine ⟨100850455410950565448707953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268934547762534841196554541 100850455410950565448707953)
            ·
              refine ⟨75637841558212924086530965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100850455410950565448707953 75637841558212924086530965)
              ·
                refine ⟨3545523823041230816556139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75637841558212924086530965 3545523823041230816556139)
                ·
                  refine ⟨5318285734561846224834209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545523823041230816556139 5318285734561846224834209)
                  ·
                    refine ⟨3988714300921384668625657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318285734561846224834209 3988714300921384668625657)
                    ·
                      refine ⟨2991535725691038501469243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988714300921384668625657 2991535725691038501469243)
                      ·
                        rfl

theorem cell23_5825995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 2, 2].length) (baseStart_5825995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825995 prefixEnd_5825995 := by exact prefixLift 5825995
  have htrace : WordTrace (prefixWord ++ tailWord_5825995) baseStart_5825995 baseEnd_5825995 := by
    simpa [prefixWord, tailWord_5825995, baseEnd_5825995] using wordTrace_append hprefix tailTrace_5825995
  have hstable : (prefixWord ++ tailWord_5825995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825995).length < 2 ^ (prefixWord ++ tailWord_5825995).sum := by decide
  have hdescent : baseEnd_5825995 < baseStart_5825995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826045 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_5826045 : Nat := 118140960795 + 5826045 * 2 ^ 59
def prefixEnd_5826045 : Nat := 4983230072969 + 3 ^ 40 * 5826045 * 2
def baseEnd_5826045 : Nat := 2991561399723763305844013

theorem tailTrace_5826045 : CollatzResearch.WordTrace tailWord_5826045 prefixEnd_5826045 2991561399723763305844013 := by
  unfold tailWord_5826045
  simp only [CollatzResearch.WordTrace]
  refine ⟨212493318178241449114375589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141662212118827632742917059 212493318178241449114375589)
  ·
    refine ⟨39842497158420271708945423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212493318178241449114375589 39842497158420271708945423)
    ·
      refine ⟨59763745737630407563418135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39842497158420271708945423 59763745737630407563418135)
      ·
        refine ⟨89645618606445611345127203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59763745737630407563418135 89645618606445611345127203)
        ·
          refine ⟨134468427909668417017690805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89645618606445611345127203 134468427909668417017690805)
          ·
            refine ⟨12606415116531414095408513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134468427909668417017690805 12606415116531414095408513)
            ·
              refine ⟨9454811337398560571556385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12606415116531414095408513 9454811337398560571556385)
              ·
                refine ⟨7091108503048920428667289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9454811337398560571556385 7091108503048920428667289)
                ·
                  refine ⟨5318331377286690321500467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091108503048920428667289 5318331377286690321500467)
                  ·
                    refine ⟨7977497065930035482250701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5318331377286690321500467 7977497065930035482250701)
                    ·
                      refine ⟨2991561399723763305844013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7977497065930035482250701 2991561399723763305844013)
                      ·
                        rfl

theorem cell23_5826045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_5826045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826045 prefixEnd_5826045 := by exact prefixLift 5826045
  have htrace : WordTrace (prefixWord ++ tailWord_5826045) baseStart_5826045 baseEnd_5826045 := by
    simpa [prefixWord, tailWord_5826045, baseEnd_5826045] using wordTrace_append hprefix tailTrace_5826045
  have hstable : (prefixWord ++ tailWord_5826045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826045).length < 2 ^ (prefixWord ++ tailWord_5826045).sum := by decide
  have hdescent : baseEnd_5826045 < baseStart_5826045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826046 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5826046 : Nat := 118140960795 + 5826046 * 2 ^ 59
def prefixEnd_5826046 : Nat := 4983230072969 + 3 ^ 40 * 5826046 * 2
def baseEnd_5826046 : Nat := 2991561913204417801931509

theorem tailTrace_5826046 : CollatzResearch.WordTrace tailWord_5826046 prefixEnd_5826046 2991561913204417801931509 := by
  unfold tailWord_5826046
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561669331404728285645249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141662236434158550856774661 26561669331404728285645249)
  ·
    refine ⟨19921251998553546214233937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26561669331404728285645249 19921251998553546214233937)
    ·
      refine ⟨14940938998915159660675453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19921251998553546214233937 14940938998915159660675453)
      ·
        refine ⟨5602852124593184872753295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14940938998915159660675453 5602852124593184872753295)
        ·
          refine ⟨8404278186889777309129943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5602852124593184872753295 8404278186889777309129943)
          ·
            refine ⟨12606417280334665963694915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404278186889777309129943 12606417280334665963694915)
            ·
              refine ⟨18909625920501998945542373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12606417280334665963694915 18909625920501998945542373)
              ·
                refine ⟨3545554860094124802289195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18909625920501998945542373 3545554860094124802289195)
                ·
                  refine ⟨5318332290141187203433793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545554860094124802289195 5318332290141187203433793)
                  ·
                    refine ⟨3988749217605890402575345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318332290141187203433793 3988749217605890402575345)
                    ·
                      refine ⟨2991561913204417801931509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988749217605890402575345 2991561913204417801931509)
                      ·
                        rfl

theorem cell23_5826046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5826046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826046 prefixEnd_5826046 := by exact prefixLift 5826046
  have htrace : WordTrace (prefixWord ++ tailWord_5826046) baseStart_5826046 baseEnd_5826046 := by
    simpa [prefixWord, tailWord_5826046, baseEnd_5826046] using wordTrace_append hprefix tailTrace_5826046
  have hstable : (prefixWord ++ tailWord_5826046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826046).length < 2 ^ (prefixWord ++ tailWord_5826046).sum := by decide
  have hdescent : baseEnd_5826046 < baseStart_5826046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826108 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 7]
def baseStart_5826108 : Nat := 118140960795 + 5826108 * 2 ^ 59
def prefixEnd_5826108 : Nat := 4983230072969 + 3 ^ 40 * 5826108 * 2
def baseEnd_5826108 : Nat := 332399305444999617706247

theorem tailTrace_5826108 : CollatzResearch.WordTrace tailWord_5826108 prefixEnd_5826108 332399305444999617706247 := by
  unfold tailWord_5826108
  simp only [CollatzResearch.WordTrace]
  refine ⟨106247807988506605436959489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141663743984675473915945985 106247807988506605436959489)
  ·
    refine ⟨79685855991379954077719617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106247807988506605436959489 79685855991379954077719617)
    ·
      refine ⟨59764391993534965558289713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79685855991379954077719617 59764391993534965558289713)
      ·
        refine ⟨44823293995151224168717285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59764391993534965558289713 44823293995151224168717285)
        ·
          refine ⟨8404367624090854531634491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44823293995151224168717285 8404367624090854531634491)
          ·
            refine ⟨12606551436136281797451737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404367624090854531634491 12606551436136281797451737)
            ·
              refine ⟨9454913577102211348088803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12606551436136281797451737 9454913577102211348088803)
              ·
                refine ⟨14182370365653317022133205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454913577102211348088803 14182370365653317022133205)
                ·
                  refine ⟨332399305444999617706247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14182370365653317022133205 332399305444999617706247)
                  ·
                    rfl

theorem cell23_5826108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_5826108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826108 prefixEnd_5826108 := by exact prefixLift 5826108
  have htrace : WordTrace (prefixWord ++ tailWord_5826108) baseStart_5826108 baseEnd_5826108 := by
    simpa [prefixWord, tailWord_5826108, baseEnd_5826108] using wordTrace_append hprefix tailTrace_5826108
  have hstable : (prefixWord ++ tailWord_5826108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826108).length < 2 ^ (prefixWord ++ tailWord_5826108).sum := by decide
  have hdescent : baseEnd_5826108 < baseStart_5826108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826119 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_5826119 : Nat := 118140960795 + 5826119 * 2 ^ 59
def prefixEnd_5826119 : Nat := 4983230072969 + 3 ^ 40 * 5826119 * 2
def baseEnd_5826119 : Nat := 2991599397292196016318673

theorem tailTrace_5826119 : CollatzResearch.WordTrace tailWord_5826119 prefixEnd_5826119 2991599397292196016318673 := by
  unfold tailWord_5826119
  simp only [CollatzResearch.WordTrace]
  refine ⟨212496017179973359752569411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141664011453315573168379607 212496017179973359752569411)
  ·
    refine ⟨318744025769960039628854117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212496017179973359752569411 318744025769960039628854117)
    ·
      refine ⟨59764504831867507430410147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318744025769960039628854117 59764504831867507430410147)
      ·
        refine ⟨89646757247801261145615221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59764504831867507430410147 89646757247801261145615221)
        ·
          refine ⟨8404383491981368232401427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89646757247801261145615221 8404383491981368232401427)
          ·
            refine ⟨12606575237972052348602141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404383491981368232401427 12606575237972052348602141)
            ·
              refine ⟨4727465714239519630725803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12606575237972052348602141 4727465714239519630725803)
              ·
                refine ⟨7091198571359279446088705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727465714239519630725803 7091198571359279446088705)
                ·
                  refine ⟨5318398928519459584566529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091198571359279446088705 5318398928519459584566529)
                  ·
                    refine ⟨3988799196389594688424897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318398928519459584566529 3988799196389594688424897)
                    ·
                      refine ⟨2991599397292196016318673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988799196389594688424897 2991599397292196016318673)
                      ·
                        rfl

theorem cell23_5826119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_5826119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826119 prefixEnd_5826119 := by exact prefixLift 5826119
  have htrace : WordTrace (prefixWord ++ tailWord_5826119) baseStart_5826119 baseEnd_5826119 := by
    simpa [prefixWord, tailWord_5826119, baseEnd_5826119] using wordTrace_append hprefix tailTrace_5826119
  have hstable : (prefixWord ++ tailWord_5826119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826119).length < 2 ^ (prefixWord ++ tailWord_5826119).sum := by decide
  have hdescent : baseEnd_5826119 < baseStart_5826119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826246 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5826246 : Nat := 118140960795 + 5826246 * 2 ^ 59
def prefixEnd_5826246 : Nat := 4983230072969 + 3 ^ 40 * 5826246 * 2
def baseEnd_5826246 : Nat := 2991664609335317019430589

theorem tailTrace_5826246 : CollatzResearch.WordTrace tailWord_5826246 prefixEnd_5826246 2991664609335317019430589 := by
  unfold tailWord_5826246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640645289078539388826331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141667099500342173628295061 6640645289078539388826331)
  ·
    refine ⟨9960967933617809083239497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640645289078539388826331 9960967933617809083239497)
    ·
      refine ⟨7470725950213356812429623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9960967933617809083239497 7470725950213356812429623)
      ·
        refine ⟨11206088925320035218644435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7470725950213356812429623 11206088925320035218644435)
        ·
          refine ⟨16809133387980052827966653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11206088925320035218644435 16809133387980052827966653)
          ·
            refine ⟨6303425020492519810487495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16809133387980052827966653 6303425020492519810487495)
            ·
              refine ⟨9455137530738779715731243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303425020492519810487495 9455137530738779715731243)
              ·
                refine ⟨14182706296108169573596865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9455137530738779715731243 14182706296108169573596865)
                ·
                  refine ⟨10637029722081127180197649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14182706296108169573596865 10637029722081127180197649)
                  ·
                    refine ⟨7977772291560845385148237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10637029722081127180197649 7977772291560845385148237)
                    ·
                      refine ⟨2991664609335317019430589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7977772291560845385148237 2991664609335317019430589)
                      ·
                        rfl

theorem cell23_5826246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5826246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826246 prefixEnd_5826246 := by exact prefixLift 5826246
  have htrace : WordTrace (prefixWord ++ tailWord_5826246) baseStart_5826246 baseEnd_5826246 := by
    simpa [prefixWord, tailWord_5826246, baseEnd_5826246] using wordTrace_append hprefix tailTrace_5826246
  have hstable : (prefixWord ++ tailWord_5826246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826246).length < 2 ^ (prefixWord ++ tailWord_5826246).sum := by decide
  have hdescent : baseEnd_5826246 < baseStart_5826246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826248 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_5826248 : Nat := 118140960795 + 5826248 * 2 ^ 59
def prefixEnd_5826248 : Nat := 4983230072969 + 3 ^ 40 * 5826248 * 2
def baseEnd_5826248 : Nat := 2991665636296626011605579

theorem tailTrace_5826248 : CollatzResearch.WordTrace tailWord_5826248 prefixEnd_5826248 2991665636296626011605579 := by
  unfold tailWord_5826248
  simp only [CollatzResearch.WordTrace]
  refine ⟨106250361098253007392007699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141667148131004009856010265 106250361098253007392007699)
  ·
    refine ⟨159375541647379511088011549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106250361098253007392007699 159375541647379511088011549)
    ·
      refine ⟨59765828117767316658004331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159375541647379511088011549 59765828117767316658004331)
      ·
        refine ⟨89648742176650974987006497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59765828117767316658004331 89648742176650974987006497)
        ·
          refine ⟨67236556632488231240254873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89648742176650974987006497 67236556632488231240254873)
          ·
            refine ⟨50427417474366173430191155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67236556632488231240254873 50427417474366173430191155)
            ·
              refine ⟨75641126211549260145286733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50427417474366173430191155 75641126211549260145286733)
              ·
                refine ⟨28365422329330972554482525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75641126211549260145286733 28365422329330972554482525)
                ·
                  refine ⟨10637033373499114707930947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28365422329330972554482525 10637033373499114707930947)
                  ·
                    refine ⟨15955550060248672061896421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10637033373499114707930947 15955550060248672061896421)
                    ·
                      refine ⟨2991665636296626011605579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15955550060248672061896421 2991665636296626011605579)
                      ·
                        rfl

theorem cell23_5826248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_5826248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826248 prefixEnd_5826248 := by exact prefixLift 5826248
  have htrace : WordTrace (prefixWord ++ tailWord_5826248) baseStart_5826248 baseEnd_5826248 := by
    simpa [prefixWord, tailWord_5826248, baseEnd_5826248] using wordTrace_append hprefix tailTrace_5826248
  have hstable : (prefixWord ++ tailWord_5826248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826248).length < 2 ^ (prefixWord ++ tailWord_5826248).sum := by decide
  have hdescent : baseEnd_5826248 < baseStart_5826248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826252 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5826252 : Nat := 118140960795 + 5826252 * 2 ^ 59
def prefixEnd_5826252 : Nat := 4983230072969 + 3 ^ 40 * 5826252 * 2
def baseEnd_5826252 : Nat := 2991667690219243995955561

theorem tailTrace_5826252 : CollatzResearch.WordTrace tailWord_5826252 prefixEnd_5826252 2991667690219243995955561 := by
  unfold tailWord_5826252
  simp only [CollatzResearch.WordTrace]
  refine ⟨106250434044245761733580505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141667245392327682311440673 106250434044245761733580505)
  ·
    refine ⟨79687825533184321300185379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106250434044245761733580505 79687825533184321300185379)
    ·
      refine ⟨119531738299776481950278069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79687825533184321300185379 119531738299776481950278069)
      ·
        refine ⟨11206100465604045182838569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119531738299776481950278069 11206100465604045182838569)
        ·
          refine ⟨8404575349203033887128927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11206100465604045182838569 8404575349203033887128927)
          ·
            refine ⟨12606863023804550830693391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404575349203033887128927 12606863023804550830693391)
            ·
              refine ⟨18910294535706826246040087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12606863023804550830693391 18910294535706826246040087)
              ·
                refine ⟨28365441803560239369060131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18910294535706826246040087 28365441803560239369060131)
                ·
                  refine ⟨42548162705340359053590197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28365441803560239369060131 42548162705340359053590197)
                  ·
                    refine ⟨3988890253625658661274081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42548162705340359053590197 3988890253625658661274081)
                    ·
                      refine ⟨2991667690219243995955561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988890253625658661274081 2991667690219243995955561)
                      ·
                        rfl

theorem cell23_5826252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5826252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826252 prefixEnd_5826252 := by exact prefixLift 5826252
  have htrace : WordTrace (prefixWord ++ tailWord_5826252) baseStart_5826252 baseEnd_5826252 := by
    simpa [prefixWord, tailWord_5826252, baseEnd_5826252] using wordTrace_append hprefix tailTrace_5826252
  have hstable : (prefixWord ++ tailWord_5826252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826252).length < 2 ^ (prefixWord ++ tailWord_5826252).sum := by decide
  have hdescent : baseEnd_5826252 < baseStart_5826252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826265 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_5826265 : Nat := 118140960795 + 5826265 * 2 ^ 59
def prefixEnd_5826265 : Nat := 4983230072969 + 3 ^ 40 * 5826265 * 2
def baseEnd_5826265 : Nat := 2991674365467752445093001

theorem tailTrace_5826265 : CollatzResearch.WordTrace tailWord_5826265 prefixEnd_5826265 2991674365467752445093001 := by
  unfold tailWord_5826265
  simp only [CollatzResearch.WordTrace]
  refine ⟨212501342237444426687384249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141667561491629617791589499 212501342237444426687384249)
  ·
    refine ⟨159376006678083320015538187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212501342237444426687384249 159376006678083320015538187)
    ·
      refine ⟨239064010017124980023307281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159376006678083320015538187 239064010017124980023307281)
      ·
        refine ⟨179298007512843735017480461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239064010017124980023307281 179298007512843735017480461)
        ·
          refine ⟨67236752817316400631555173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179298007512843735017480461 67236752817316400631555173)
          ·
            refine ⟨12606891153246825118416595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67236752817316400631555173 12606891153246825118416595)
            ·
              refine ⟨18910336729870237677624893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12606891153246825118416595 18910336729870237677624893)
              ·
                refine ⟨7091376273701339129109335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18910336729870237677624893 7091376273701339129109335)
                ·
                  refine ⟨10637064410552008693664003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091376273701339129109335 10637064410552008693664003)
                  ·
                    refine ⟨15955596615828013040496005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10637064410552008693664003 15955596615828013040496005)
                    ·
                      refine ⟨2991674365467752445093001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15955596615828013040496005 2991674365467752445093001)
                      ·
                        rfl

theorem cell23_5826265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_5826265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826265 prefixEnd_5826265 := by exact prefixLift 5826265
  have htrace : WordTrace (prefixWord ++ tailWord_5826265) baseStart_5826265 baseEnd_5826265 := by
    simpa [prefixWord, tailWord_5826265, baseEnd_5826265] using wordTrace_append hprefix tailTrace_5826265
  have hstable : (prefixWord ++ tailWord_5826265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826265).length < 2 ^ (prefixWord ++ tailWord_5826265).sum := by decide
  have hdescent : baseEnd_5826265 < baseStart_5826265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826271 : List Nat := [1, 1, 2, 3, 2, 2, 12]
def baseStart_5826271 : Nat := 118140960795 + 5826271 * 2 ^ 59
def prefixEnd_5826271 : Nat := 4983230072969 + 3 ^ 40 * 5826271 * 2
def baseEnd_5826271 : Nat := 36934289461131844711333

theorem tailTrace_5826271 : CollatzResearch.WordTrace tailWord_5826271 prefixEnd_5826271 36934289461131844711333 := by
  unfold tailWord_5826271
  simp only [CollatzResearch.WordTrace]
  refine ⟨212501561075422689712102667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141667707383615126474735111 212501561075422689712102667)
  ·
    refine ⟨318752341613134034568154001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212501561075422689712102667 318752341613134034568154001)
    ·
      refine ⟨239064256209850525926115501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318752341613134034568154001 239064256209850525926115501)
      ·
        refine ⟨89649096078693947222293313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239064256209850525926115501 89649096078693947222293313)
        ·
          refine ⟨67236822059020460416719985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89649096078693947222293313 67236822059020460416719985)
          ·
            refine ⟨50427616544265345312539989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67236822059020460416719985 50427616544265345312539989)
            ·
              refine ⟨36934289461131844711333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50427616544265345312539989 36934289461131844711333)
              ·
                rfl

theorem cell23_5826271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 12].length) (baseStart_5826271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826271 prefixEnd_5826271 := by exact prefixLift 5826271
  have htrace : WordTrace (prefixWord ++ tailWord_5826271) baseStart_5826271 baseEnd_5826271 := by
    simpa [prefixWord, tailWord_5826271, baseEnd_5826271] using wordTrace_append hprefix tailTrace_5826271
  have hstable : (prefixWord ++ tailWord_5826271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826271).length < 2 ^ (prefixWord ++ tailWord_5826271).sum := by decide
  have hdescent : baseEnd_5826271 < baseStart_5826271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826281 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_5826281 : Nat := 118140960795 + 5826281 * 2 ^ 59
def prefixEnd_5826281 : Nat := 4983230072969 + 3 ^ 40 * 5826281 * 2
def baseEnd_5826281 : Nat := 2991682581158224382492927

theorem tailTrace_5826281 : CollatzResearch.WordTrace tailWord_5826281 prefixEnd_5826281 2991682581158224382492927 := by
  unfold tailWord_5826281
  simp only [CollatzResearch.WordTrace]
  refine ⟨212501925805386461419966697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141667950536924307613311131 212501925805386461419966697)
  ·
    refine ⟨159376444354039846064975023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212501925805386461419966697 159376444354039846064975023)
    ·
      refine ⟨239064666531059769097462535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159376444354039846064975023 239064666531059769097462535)
      ·
        refine ⟨358596999796589653646193803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239064666531059769097462535 358596999796589653646193803)
        ·
          refine ⟨537895499694884480469290705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358596999796589653646193803 537895499694884480469290705)
          ·
            refine ⟨403421624771163360351968029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537895499694884480469290705 403421624771163360351968029)
            ·
              refine ⟨151283109289186260131988011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403421624771163360351968029 151283109289186260131988011)
              ·
                refine ⟨226924663933779390197982017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151283109289186260131988011 226924663933779390197982017)
                ·
                  refine ⟨170193497950334542648486513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226924663933779390197982017 170193497950334542648486513)
                  ·
                    refine ⟨127645123462750906986364885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170193497950334542648486513 127645123462750906986364885)
                    ·
                      refine ⟨2991682581158224382492927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127645123462750906986364885 2991682581158224382492927)
                      ·
                        rfl

theorem cell23_5826281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_5826281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826281 prefixEnd_5826281 := by exact prefixLift 5826281
  have htrace : WordTrace (prefixWord ++ tailWord_5826281) baseStart_5826281 baseEnd_5826281 := by
    simpa [prefixWord, tailWord_5826281, baseEnd_5826281] using wordTrace_append hprefix tailTrace_5826281
  have hstable : (prefixWord ++ tailWord_5826281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826281).length < 2 ^ (prefixWord ++ tailWord_5826281).sum := by decide
  have hdescent : baseEnd_5826281 < baseStart_5826281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826282 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_5826282 : Nat := 118140960795 + 5826282 * 2 ^ 59
def prefixEnd_5826282 : Nat := 4983230072969 + 3 ^ 40 * 5826282 * 2
def baseEnd_5826282 : Nat := 2991683094638878878580423

theorem tailTrace_5826282 : CollatzResearch.WordTrace tailWord_5826282 prefixEnd_5826282 2991683094638878878580423 := by
  unfold tailWord_5826282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53125490569595709647688275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141667974852255225727168733 53125490569595709647688275)
  ·
    refine ⟨79688235854393564471532413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53125490569595709647688275 79688235854393564471532413)
    ·
      refine ⟨29883088445397586676824655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79688235854393564471532413 29883088445397586676824655)
      ·
        refine ⟨44824632668096380015236983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29883088445397586676824655 44824632668096380015236983)
        ·
          refine ⟨67236949002144570022855475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44824632668096380015236983 67236949002144570022855475)
          ·
            refine ⟨100855423503216855034283213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67236949002144570022855475 100855423503216855034283213)
            ·
              refine ⟨37820783813706320637856205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100855423503216855034283213 37820783813706320637856205)
              ·
                refine ⟨14182793930139870239196077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37820783813706320637856205 14182793930139870239196077)
                ·
                  refine ⟨5318547723802451339698529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14182793930139870239196077 5318547723802451339698529)
                  ·
                    refine ⟨3988910792851838504773897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318547723802451339698529 3988910792851838504773897)
                    ·
                      refine ⟨2991683094638878878580423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988910792851838504773897 2991683094638878878580423)
                      ·
                        rfl

theorem cell23_5826282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_5826282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826282 prefixEnd_5826282 := by exact prefixLift 5826282
  have htrace : WordTrace (prefixWord ++ tailWord_5826282) baseStart_5826282 baseEnd_5826282 := by
    simpa [prefixWord, tailWord_5826282, baseEnd_5826282] using wordTrace_append hprefix tailTrace_5826282
  have hstable : (prefixWord ++ tailWord_5826282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826282).length < 2 ^ (prefixWord ++ tailWord_5826282).sum := by decide
  have hdescent : baseEnd_5826282 < baseStart_5826282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826285 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5826285 : Nat := 118140960795 + 5826285 * 2 ^ 59
def prefixEnd_5826285 : Nat := 4983230072969 + 3 ^ 40 * 5826285 * 2
def baseEnd_5826285 : Nat := 2991684635080842366842909

theorem tailTrace_5826285 : CollatzResearch.WordTrace tailWord_5826285 prefixEnd_5826285 2991684635080842366842909 := by
  unfold tailWord_5826285
  simp only [CollatzResearch.WordTrace]
  refine ⟨212502071697371970103112309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141668047798247980068741539 212502071697371970103112309)
  ·
    refine ⟨19922069221628622197166779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212502071697371970103112309 19922069221628622197166779)
    ·
      refine ⟨29883103832442933295750169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19922069221628622197166779 29883103832442933295750169)
      ·
        refine ⟨22412327874332199971812627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29883103832442933295750169 22412327874332199971812627)
        ·
          refine ⟨33618491811498299957718941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22412327874332199971812627 33618491811498299957718941)
          ·
            refine ⟨12606934429311862484144603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33618491811498299957718941 12606934429311862484144603)
            ·
              refine ⟨18910401643967793726216905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12606934429311862484144603 18910401643967793726216905)
              ·
                refine ⟨14182801232975845294662679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18910401643967793726216905 14182801232975845294662679)
                ·
                  refine ⟨21274201849463767941994019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14182801232975845294662679 21274201849463767941994019)
                  ·
                    refine ⟨31911302774195651912991029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21274201849463767941994019 31911302774195651912991029)
                    ·
                      refine ⟨2991684635080842366842909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31911302774195651912991029 2991684635080842366842909)
                      ·
                        rfl

theorem cell23_5826285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5826285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826285 prefixEnd_5826285 := by exact prefixLift 5826285
  have htrace : WordTrace (prefixWord ++ tailWord_5826285) baseStart_5826285 baseEnd_5826285 := by
    simpa [prefixWord, tailWord_5826285, baseEnd_5826285] using wordTrace_append hprefix tailTrace_5826285
  have hstable : (prefixWord ++ tailWord_5826285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826285).length < 2 ^ (prefixWord ++ tailWord_5826285).sum := by decide
  have hdescent : baseEnd_5826285 < baseStart_5826285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826315 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 3]
def baseStart_5826315 : Nat := 118140960795 + 5826315 * 2 ^ 59
def prefixEnd_5826315 : Nat := 4983230072969 + 3 ^ 40 * 5826315 * 2
def baseEnd_5826315 : Nat := 2991700039500477249467771

theorem tailTrace_5826315 : CollatzResearch.WordTrace tailWord_5826315 prefixEnd_5826315 2991700039500477249467771 := by
  unfold tailWord_5826315
  simp only [CollatzResearch.WordTrace]
  refine ⟨212503165887263285226704399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141668777258175523484469599 212503165887263285226704399)
  ·
    refine ⟨318754748830894927840056599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212503165887263285226704399 318754748830894927840056599)
    ·
      refine ⟨478132123246342391760084899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318754748830894927840056599 478132123246342391760084899)
      ·
        refine ⟨717198184869513587640127349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478132123246342391760084899 717198184869513587640127349)
        ·
          refine ⟨67237329831516898841261939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 717198184869513587640127349 67237329831516898841261939)
          ·
            refine ⟨100855994747275348261892909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67237329831516898841261939 100855994747275348261892909)
            ·
              refine ⟨37820998030228255598209841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100855994747275348261892909 37820998030228255598209841)
              ·
                refine ⟨28365748522671191698657381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37820998030228255598209841 28365748522671191698657381)
                ·
                  refine ⟨5318577848000848443498259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28365748522671191698657381 5318577848000848443498259)
                  ·
                    refine ⟨7977866772001272665247389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5318577848000848443498259 7977866772001272665247389)
                    ·
                      refine ⟨2991700039500477249467771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7977866772001272665247389 2991700039500477249467771)
                      ·
                        rfl

theorem cell23_5826315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 3].length) (baseStart_5826315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826315 prefixEnd_5826315 := by exact prefixLift 5826315
  have htrace : WordTrace (prefixWord ++ tailWord_5826315) baseStart_5826315 baseEnd_5826315 := by
    simpa [prefixWord, tailWord_5826315, baseEnd_5826315] using wordTrace_append hprefix tailTrace_5826315
  have hstable : (prefixWord ++ tailWord_5826315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826315).length < 2 ^ (prefixWord ++ tailWord_5826315).sum := by decide
  have hdescent : baseEnd_5826315 < baseStart_5826315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826332 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5826332 : Nat := 118140960795 + 5826332 * 2 ^ 59
def prefixEnd_5826332 : Nat := 4983230072969 + 3 ^ 40 * 5826332 * 2
def baseEnd_5826332 : Nat := 2991708768671603682955193

theorem tailTrace_5826332 : CollatzResearch.WordTrace tailWord_5826332 prefixEnd_5826332 2991708768671603682955193 := by
  unfold tailWord_5826332
  simp only [CollatzResearch.WordTrace]
  refine ⟨106251892964100848565036625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141669190618801131420048833 106251892964100848565036625)
  ·
    refine ⟨79688919723075636423777469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106251892964100848565036625 79688919723075636423777469)
    ·
      refine ⟨29883344896153363658916551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79688919723075636423777469 29883344896153363658916551)
      ·
        refine ⟨44825017344230045488374827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29883344896153363658916551 44825017344230045488374827)
        ·
          refine ⟨67237526016345068232562241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44825017344230045488374827 67237526016345068232562241)
          ·
            refine ⟨50428144512258801174421681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67237526016345068232562241 50428144512258801174421681)
            ·
              refine ⟨37821108384194100880816261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50428144512258801174421681 37821108384194100880816261)
              ·
                refine ⟨7091457822036393915153049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37821108384194100880816261 7091457822036393915153049)
                ·
                  refine ⟨5318593366527295436364787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091457822036393915153049 5318593366527295436364787)
                  ·
                    refine ⟨7977890049790943154547181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5318593366527295436364787 7977890049790943154547181)
                    ·
                      refine ⟨2991708768671603682955193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7977890049790943154547181 2991708768671603682955193)
                      ·
                        rfl

theorem cell23_5826332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5826332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826332 prefixEnd_5826332 := by exact prefixLift 5826332
  have htrace : WordTrace (prefixWord ++ tailWord_5826332) baseStart_5826332 baseEnd_5826332 := by
    simpa [prefixWord, tailWord_5826332, baseEnd_5826332] using wordTrace_append hprefix tailTrace_5826332
  have hstable : (prefixWord ++ tailWord_5826332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826332).length < 2 ^ (prefixWord ++ tailWord_5826332).sum := by decide
  have hdescent : baseEnd_5826332 < baseStart_5826332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826368 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_5826368 : Nat := 118140960795 + 5826368 * 2 ^ 59
def prefixEnd_5826368 : Nat := 4983230072969 + 3 ^ 40 * 5826368 * 2
def baseEnd_5826368 : Nat := 2991727253975165542105027

theorem tailTrace_5826368 : CollatzResearch.WordTrace tailWord_5826368 prefixEnd_5826368 2991727253975165542105027 := by
  unfold tailWord_5826368
  simp only [CollatzResearch.WordTrace]
  refine ⟨106252549478035637639191879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141670065970714183518922505 106252549478035637639191879)
  ·
    refine ⟨159378824217053456458787819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106252549478035637639191879 159378824217053456458787819)
    ·
      refine ⟨239068236325580184688181729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159378824217053456458787819 239068236325580184688181729)
      ·
        refine ⟨179301177244185138516136297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239068236325580184688181729 179301177244185138516136297)
        ·
          refine ⟨134475882933138853887102223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179301177244185138516136297 134475882933138853887102223)
          ·
            refine ⟨201713824399708280830653335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134475882933138853887102223 201713824399708280830653335)
            ·
              refine ⟨302570736599562421245980003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201713824399708280830653335 302570736599562421245980003)
              ·
                refine ⟨453856104899343631868970005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302570736599562421245980003 453856104899343631868970005)
                ·
                  refine ⟨21274504917156732743857969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 453856104899343631868970005 21274504917156732743857969)
                  ·
                    refine ⟨15955878687867549557893477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21274504917156732743857969 15955878687867549557893477)
                    ·
                      refine ⟨2991727253975165542105027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15955878687867549557893477 2991727253975165542105027)
                      ·
                        rfl

theorem cell23_5826368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_5826368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826368 prefixEnd_5826368 := by exact prefixLift 5826368
  have htrace : WordTrace (prefixWord ++ tailWord_5826368) baseStart_5826368 baseEnd_5826368 := by
    simpa [prefixWord, tailWord_5826368, baseEnd_5826368] using wordTrace_append hprefix tailTrace_5826368
  have hstable : (prefixWord ++ tailWord_5826368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826368).length < 2 ^ (prefixWord ++ tailWord_5826368).sum := by decide
  have hdescent : baseEnd_5826368 < baseStart_5826368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826389 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5826389 : Nat := 118140960795 + 5826389 * 2 ^ 59
def prefixEnd_5826389 : Nat := 4983230072969 + 3 ^ 40 * 5826389 * 2
def baseEnd_5826389 : Nat := 2991738037068909959942431

theorem tailTrace_5826389 : CollatzResearch.WordTrace tailWord_5826389 prefixEnd_5826389 2991738037068909959942431 := by
  unfold tailWord_5826389
  simp only [CollatzResearch.WordTrace]
  refine ⟨212505864888995195864898221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141670576592663463909932147 212505864888995195864898221)
  ·
    refine ⟨79689699333373198449336833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212505864888995195864898221 79689699333373198449336833)
    ·
      refine ⟨59767274500029898837002625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79689699333373198449336833 59767274500029898837002625)
      ·
        refine ⟨44825455875022424127751969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59767274500029898837002625 44825455875022424127751969)
        ·
          refine ⟨33619091906266818095813977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44825455875022424127751969 33619091906266818095813977)
          ·
            refine ⟨25214318929700113571860483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33619091906266818095813977 25214318929700113571860483)
            ·
              refine ⟨37821478394550170357790725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25214318929700113571860483 37821478394550170357790725)
              ·
                refine ⟨7091527198978156942085761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37821478394550170357790725 7091527198978156942085761)
                ·
                  refine ⟨5318645399233617706564321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091527198978156942085761 5318645399233617706564321)
                  ·
                    refine ⟨3988984049425213279923241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318645399233617706564321 3988984049425213279923241)
                    ·
                      refine ⟨2991738037068909959942431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988984049425213279923241 2991738037068909959942431)
                      ·
                        rfl

theorem cell23_5826389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5826389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826389 prefixEnd_5826389 := by exact prefixLift 5826389
  have htrace : WordTrace (prefixWord ++ tailWord_5826389) baseStart_5826389 baseEnd_5826389 := by
    simpa [prefixWord, tailWord_5826389, baseEnd_5826389] using wordTrace_append hprefix tailTrace_5826389
  have hstable : (prefixWord ++ tailWord_5826389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826389).length < 2 ^ (prefixWord ++ tailWord_5826389).sum := by decide
  have hdescent : baseEnd_5826389 < baseStart_5826389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826402 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5826402 : Nat := 118140960795 + 5826402 * 2 ^ 59
def prefixEnd_5826402 : Nat := 4983230072969 + 3 ^ 40 * 5826402 * 2
def baseEnd_5826402 : Nat := 2991744712317418409079871

theorem tailTrace_5826402 : CollatzResearch.WordTrace tailWord_5826402 prefixEnd_5826402 2991744712317418409079871 := by
  unfold tailWord_5826402
  simp only [CollatzResearch.WordTrace]
  refine ⟨53126584759487024771280365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141670892691965399390080973 53126584759487024771280365)
  ·
    refine ⟨19922469284807634289230137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53126584759487024771280365 19922469284807634289230137)
    ·
      refine ⟨14941851963605725716922603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19922469284807634289230137 14941851963605725716922603)
      ·
        refine ⟨22412777945408588575383905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14941851963605725716922603 22412777945408588575383905)
        ·
          refine ⟨16809583459056441431537929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22412777945408588575383905 16809583459056441431537929)
          ·
            refine ⟨12607187594292331073653447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16809583459056441431537929 12607187594292331073653447)
            ·
              refine ⟨18910781391438496610480171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607187594292331073653447 18910781391438496610480171)
              ·
                refine ⟨28366172087157744915720257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18910781391438496610480171 28366172087157744915720257)
                ·
                  refine ⟨21274629065368308686790193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28366172087157744915720257 21274629065368308686790193)
                  ·
                    refine ⟨15955971799026231515092645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21274629065368308686790193 15955971799026231515092645)
                    ·
                      refine ⟨2991744712317418409079871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15955971799026231515092645 2991744712317418409079871)
                      ·
                        rfl

theorem cell23_5826402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5826402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826402 prefixEnd_5826402 := by exact prefixLift 5826402
  have htrace : WordTrace (prefixWord ++ tailWord_5826402) baseStart_5826402 baseEnd_5826402 := by
    simpa [prefixWord, tailWord_5826402, baseEnd_5826402] using wordTrace_append hprefix tailTrace_5826402
  have hstable : (prefixWord ++ tailWord_5826402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826402).length < 2 ^ (prefixWord ++ tailWord_5826402).sum := by decide
  have hdescent : baseEnd_5826402 < baseStart_5826402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826448 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_5826448 : Nat := 118140960795 + 5826448 * 2 ^ 59
def prefixEnd_5826448 : Nat := 4983230072969 + 3 ^ 40 * 5826448 * 2
def baseEnd_5826448 : Nat := 2991768332427525229104659

theorem tailTrace_5826448 : CollatzResearch.WordTrace tailWord_5826448 prefixEnd_5826448 2991768332427525229104659 := by
  unfold tailWord_5826448
  simp only [CollatzResearch.WordTrace]
  refine ⟨106254008397890724470647999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141672011197187632627530665 106254008397890724470647999)
  ·
    refine ⟨159381012596836086705971999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106254008397890724470647999 159381012596836086705971999)
    ·
      refine ⟨239071518895254130058957999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159381012596836086705971999 239071518895254130058957999)
      ·
        refine ⟨358607278342881195088436999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239071518895254130058957999 358607278342881195088436999)
        ·
          refine ⟨537910917514321792632655499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358607278342881195088436999 537910917514321792632655499)
          ·
            refine ⟨806866376271482688948983249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537910917514321792632655499 806866376271482688948983249)
            ·
              refine ⟨605149782203612016711737437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806866376271482688948983249 605149782203612016711737437)
              ·
                refine ⟨226931168326354506266901539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605149782203612016711737437 226931168326354506266901539)
                ·
                  refine ⟨340396752489531759400352309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226931168326354506266901539 340396752489531759400352309)
                  ·
                    refine ⟨31912195545893602443783029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 340396752489531759400352309 31912195545893602443783029)
                    ·
                      refine ⟨2991768332427525229104659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31912195545893602443783029 2991768332427525229104659)
                      ·
                        rfl

theorem cell23_5826448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_5826448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826448 prefixEnd_5826448 := by exact prefixLift 5826448
  have htrace : WordTrace (prefixWord ++ tailWord_5826448) baseStart_5826448 baseEnd_5826448 := by
    simpa [prefixWord, tailWord_5826448, baseEnd_5826448] using wordTrace_append hprefix tailTrace_5826448
  have hstable : (prefixWord ++ tailWord_5826448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826448).length < 2 ^ (prefixWord ++ tailWord_5826448).sum := by decide
  have hdescent : baseEnd_5826448 < baseStart_5826448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826485 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 8]
def baseStart_5826485 : Nat := 118140960795 + 5826485 * 2 ^ 59
def prefixEnd_5826485 : Nat := 4983230072969 + 3 ^ 40 * 5826485 * 2
def baseEnd_5826485 : Nat := 332420814579082398260221

theorem tailTrace_5826485 : CollatzResearch.WordTrace tailWord_5826485 prefixEnd_5826485 332420814579082398260221 := by
  unfold tailWord_5826485
  simp only [CollatzResearch.WordTrace]
  refine ⟨212509366296647404260392909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141672910864431602840261939 212509366296647404260392909)
  ·
    refine ⟨79691012361242776597647341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212509366296647404260392909 79691012361242776597647341)
    ·
      refine ⟨29884129635466041224117753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79691012361242776597647341 29884129635466041224117753)
      ·
        refine ⟨22413097226599530918088315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29884129635466041224117753 22413097226599530918088315)
        ·
          refine ⟨33619645839899296377132473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22413097226599530918088315 33619645839899296377132473)
          ·
            refine ⟨25214734379924472282849355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33619645839899296377132473 25214734379924472282849355)
            ·
              refine ⟨37822101569886708424274033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25214734379924472282849355 37822101569886708424274033)
              ·
                refine ⟨28366576177415031318205525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37822101569886708424274033 28366576177415031318205525)
                ·
                  refine ⟨332420814579082398260221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28366576177415031318205525 332420814579082398260221)
                  ·
                    rfl

theorem cell23_5826485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_5826485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826485 prefixEnd_5826485 := by exact prefixLift 5826485
  have htrace : WordTrace (prefixWord ++ tailWord_5826485) baseStart_5826485 baseEnd_5826485 := by
    simpa [prefixWord, tailWord_5826485, baseEnd_5826485] using wordTrace_append hprefix tailTrace_5826485
  have hstable : (prefixWord ++ tailWord_5826485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826485).length < 2 ^ (prefixWord ++ tailWord_5826485).sum := by decide
  have hdescent : baseEnd_5826485 < baseStart_5826485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826552 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_5826552 : Nat := 118140960795 + 5826552 * 2 ^ 59
def prefixEnd_5826552 : Nat := 4983230072969 + 3 ^ 40 * 5826552 * 2
def baseEnd_5826552 : Nat := 2991821734415592822204181

theorem tailTrace_5826552 : CollatzResearch.WordTrace tailWord_5826552 prefixEnd_5826552 2991821734415592822204181 := by
  unfold tailWord_5826552
  simp only [CollatzResearch.WordTrace]
  refine ⟨106255904993702337351540955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141674539991603116468721273 106255904993702337351540955)
  ·
    refine ⟨159383857490553506027311433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106255904993702337351540955 159383857490553506027311433)
    ·
      refine ⟨119537893117915129520483575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159383857490553506027311433 119537893117915129520483575)
      ·
        refine ⟨179306839676872694280725363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119537893117915129520483575 179306839676872694280725363)
        ·
          refine ⟨268960259515309041421088045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179306839676872694280725363 268960259515309041421088045)
          ·
            refine ⟨100860097318240890532908017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268960259515309041421088045 100860097318240890532908017)
            ·
              refine ⟨75645072988680667899681013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100860097318240890532908017 75645072988680667899681013)
              ·
                refine ⟨7091725592688812615595095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75645072988680667899681013 7091725592688812615595095)
                ·
                  refine ⟨10637588389033218923392643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091725592688812615595095 10637588389033218923392643)
                  ·
                    refine ⟨15956382583549828385088965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10637588389033218923392643 15956382583549828385088965)
                    ·
                      refine ⟨2991821734415592822204181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15956382583549828385088965 2991821734415592822204181)
                      ·
                        rfl

theorem cell23_5826552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_5826552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826552 prefixEnd_5826552 := by exact prefixLift 5826552
  have htrace : WordTrace (prefixWord ++ tailWord_5826552) baseStart_5826552 baseEnd_5826552 := by
    simpa [prefixWord, tailWord_5826552, baseEnd_5826552] using wordTrace_append hprefix tailTrace_5826552
  have hstable : (prefixWord ++ tailWord_5826552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826552).length < 2 ^ (prefixWord ++ tailWord_5826552).sum := by decide
  have hdescent : baseEnd_5826552 < baseStart_5826552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826572 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_5826572 : Nat := 118140960795 + 5826572 * 2 ^ 59
def prefixEnd_5826572 : Nat := 4983230072969 + 3 ^ 40 * 5826572 * 2
def baseEnd_5826572 : Nat := 2991832004028682743954089

theorem tailTrace_5826572 : CollatzResearch.WordTrace tailWord_5826572 prefixEnd_5826572 2991832004028682743954089 := by
  unfold tailWord_5826572
  simp only [CollatzResearch.WordTrace]
  refine ⟨106256269723666109059404985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141675026298221478745873313 106256269723666109059404985)
  ·
    refine ⟨79692202292749581794553739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106256269723666109059404985 79692202292749581794553739)
    ·
      refine ⟨119538303439124372691830609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79692202292749581794553739 119538303439124372691830609)
      ·
        refine ⟨89653727579343279518872957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119538303439124372691830609 89653727579343279518872957)
        ·
          refine ⟨33620147842253729819577359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89653727579343279518872957 33620147842253729819577359)
          ·
            refine ⟨50430221763380594729366039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33620147842253729819577359 50430221763380594729366039)
            ·
              refine ⟨75645332645070892094049059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50430221763380594729366039 75645332645070892094049059)
              ·
                refine ⟨113467998967606338141073589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75645332645070892094049059 113467998967606338141073589)
                ·
                  refine ⟨10637624903213094200725649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113467998967606338141073589 10637624903213094200725649)
                  ·
                    refine ⟨7978218677409820650544237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10637624903213094200725649 7978218677409820650544237)
                    ·
                      refine ⟨2991832004028682743954089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978218677409820650544237 2991832004028682743954089)
                      ·
                        rfl

theorem cell23_5826572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_5826572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826572 prefixEnd_5826572 := by exact prefixLift 5826572
  have htrace : WordTrace (prefixWord ++ tailWord_5826572) baseStart_5826572 baseEnd_5826572 := by
    simpa [prefixWord, tailWord_5826572, baseEnd_5826572] using wordTrace_append hprefix tailTrace_5826572
  have hstable : (prefixWord ++ tailWord_5826572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826572).length < 2 ^ (prefixWord ++ tailWord_5826572).sum := by decide
  have hdescent : baseEnd_5826572 < baseStart_5826572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826586 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_5826586 : Nat := 118140960795 + 5826586 * 2 ^ 59
def prefixEnd_5826586 : Nat := 4983230072969 + 3 ^ 40 * 5826586 * 2
def baseEnd_5826586 : Nat := 2991839192757845689179025

theorem tailTrace_5826586 : CollatzResearch.WordTrace tailWord_5826586 prefixEnd_5826586 2991839192757845689179025 := by
  unfold tailWord_5826586
  simp only [CollatzResearch.WordTrace]
  refine ⟨53128262517320374627454903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141675366712854332339879741 53128262517320374627454903)
  ·
    refine ⟨79692393775980561941182355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53128262517320374627454903 79692393775980561941182355)
    ·
      refine ⟨119538590663970842911773533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79692393775980561941182355 119538590663970842911773533)
      ·
        refine ⟨44826971498989066091915075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119538590663970842911773533 44826971498989066091915075)
        ·
          refine ⟨67240457248483599137872613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44826971498989066091915075 67240457248483599137872613)
          ·
            refine ⟨12607585734090674838351115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67240457248483599137872613 12607585734090674838351115)
            ·
              refine ⟨18911378601136012257526673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607585734090674838351115 18911378601136012257526673)
              ·
                refine ⟨14183533950852009193145005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18911378601136012257526673 14183533950852009193145005)
                ·
                  refine ⟨5318825231569503447429377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14183533950852009193145005 5318825231569503447429377)
                  ·
                    refine ⟨3989118923677127585572033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318825231569503447429377 3989118923677127585572033)
                    ·
                      refine ⟨2991839192757845689179025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989118923677127585572033 2991839192757845689179025)
                      ·
                        rfl

theorem cell23_5826586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_5826586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826586 prefixEnd_5826586 := by exact prefixLift 5826586
  have htrace : WordTrace (prefixWord ++ tailWord_5826586) baseStart_5826586 baseEnd_5826586 := by
    simpa [prefixWord, tailWord_5826586, baseEnd_5826586] using wordTrace_append hprefix tailTrace_5826586
  have hstable : (prefixWord ++ tailWord_5826586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826586).length < 2 ^ (prefixWord ++ tailWord_5826586).sum := by decide
  have hdescent : baseEnd_5826586 < baseStart_5826586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826589 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_5826589 : Nat := 118140960795 + 5826589 * 2 ^ 59
def prefixEnd_5826589 : Nat := 4983230072969 + 3 ^ 40 * 5826589 * 2
def baseEnd_5826589 : Nat := 2991840733199809177441511

theorem tailTrace_5826589 : CollatzResearch.WordTrace tailWord_5826589 prefixEnd_5826589 2991840733199809177441511 := by
  unfold tailWord_5826589
  simp only [CollatzResearch.WordTrace]
  refine ⟨212513159488270630022178821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141675439658847086681452547 212513159488270630022178821)
  ·
    refine ⟨39846217404050743129158529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212513159488270630022178821 39846217404050743129158529)
    ·
      refine ⟨29884663053038057346868897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39846217404050743129158529 29884663053038057346868897)
      ·
        refine ⟨22413497289778543010151673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29884663053038057346868897 22413497289778543010151673)
        ·
          refine ⟨16810122967333907257613755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22413497289778543010151673 16810122967333907257613755)
          ·
            refine ⟨25215184451000860886420633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16810122967333907257613755 25215184451000860886420633)
            ·
              refine ⟨18911388338250645664815475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25215184451000860886420633 18911388338250645664815475)
              ·
                refine ⟨28367082507375968497223213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18911388338250645664815475 28367082507375968497223213)
                ·
                  refine ⟨10637655940265988186458705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28367082507375968497223213 10637655940265988186458705)
                  ·
                    refine ⟨7978241955199491139844029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10637655940265988186458705 7978241955199491139844029)
                    ·
                      refine ⟨2991840733199809177441511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978241955199491139844029 2991840733199809177441511)
                      ·
                        rfl

theorem cell23_5826589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_5826589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826589 prefixEnd_5826589 := by exact prefixLift 5826589
  have htrace : WordTrace (prefixWord ++ tailWord_5826589) baseStart_5826589 baseEnd_5826589 := by
    simpa [prefixWord, tailWord_5826589, baseEnd_5826589] using wordTrace_append hprefix tailTrace_5826589
  have hstable : (prefixWord ++ tailWord_5826589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826589).length < 2 ^ (prefixWord ++ tailWord_5826589).sum := by decide
  have hdescent : baseEnd_5826589 < baseStart_5826589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826600 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 1, 5]
def baseStart_5826600 : Nat := 118140960795 + 5826600 * 2 ^ 59
def prefixEnd_5826600 : Nat := 4983230072969 + 3 ^ 40 * 5826600 * 2
def baseEnd_5826600 : Nat := 997282127162336211467987

theorem tailTrace_5826600 : CollatzResearch.WordTrace tailWord_5826600 prefixEnd_5826600 997282127162336211467987 := by
  unfold tailWord_5826600
  simp only [CollatzResearch.WordTrace]
  refine ⟨106256780345615389450414627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141675707127487185933886169 106256780345615389450414627)
  ·
    refine ⟨159385170518423084175621941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106256780345615389450414627 159385170518423084175621941)
    ·
      refine ⟨14942359736102164141464557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159385170518423084175621941 14942359736102164141464557)
      ·
        refine ⟨5603384901038311553049209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14942359736102164141464557 5603384901038311553049209)
        ·
          refine ⟨4202538675778733664786907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5603384901038311553049209 4202538675778733664786907)
          ·
            refine ⟨6303808013668100497180361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202538675778733664786907 6303808013668100497180361)
            ·
              refine ⟨4727856010251075372885271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303808013668100497180361 4727856010251075372885271)
              ·
                refine ⟨7091784015376613059327907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727856010251075372885271 7091784015376613059327907)
                ·
                  refine ⟨10637676023064919588991861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091784015376613059327907 10637676023064919588991861)
                  ·
                    refine ⟨997282127162336211467987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10637676023064919588991861 997282127162336211467987)
                    ·
                      rfl

theorem cell23_5826600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_5826600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826600 prefixEnd_5826600 := by exact prefixLift 5826600
  have htrace : WordTrace (prefixWord ++ tailWord_5826600) baseStart_5826600 baseEnd_5826600 := by
    simpa [prefixWord, tailWord_5826600, baseEnd_5826600] using wordTrace_append hprefix tailTrace_5826600
  have hstable : (prefixWord ++ tailWord_5826600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826600).length < 2 ^ (prefixWord ++ tailWord_5826600).sum := by decide
  have hdescent : baseEnd_5826600 < baseStart_5826600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826606 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5826606 : Nat := 118140960795 + 5826606 * 2 ^ 59
def prefixEnd_5826606 : Nat := 4983230072969 + 3 ^ 40 * 5826606 * 2
def baseEnd_5826606 : Nat := 2991849462370935610928933

theorem tailTrace_5826606 : CollatzResearch.WordTrace tailWord_5826606 prefixEnd_5826606 2991849462370935610928933 := by
  unfold tailWord_5826606
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564222441151130240693459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141675853019472694617031781 26564222441151130240693459)
  ·
    refine ⟨39846333661726695361040189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26564222441151130240693459 39846333661726695361040189)
    ·
      refine ⟨14942375123147510760390071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39846333661726695361040189 14942375123147510760390071)
      ·
        refine ⟨22413562684721266140585107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14942375123147510760390071 22413562684721266140585107)
        ·
          refine ⟨33620344027081899210877661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22413562684721266140585107 33620344027081899210877661)
          ·
            refine ⟨12607629010155712204079123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33620344027081899210877661 12607629010155712204079123)
            ·
              refine ⟨18911443515233568306118685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607629010155712204079123 18911443515233568306118685)
              ·
                refine ⟨7091791318212588114794507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18911443515233568306118685 7091791318212588114794507)
                ·
                  refine ⟨10637686977318882172191761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091791318212588114794507 10637686977318882172191761)
                  ·
                    refine ⟨7978265232989161629143821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10637686977318882172191761 7978265232989161629143821)
                    ·
                      refine ⟨2991849462370935610928933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978265232989161629143821 2991849462370935610928933)
                      ·
                        rfl

theorem cell23_5826606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5826606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826606 prefixEnd_5826606 := by exact prefixLift 5826606
  have htrace : WordTrace (prefixWord ++ tailWord_5826606) baseStart_5826606 baseEnd_5826606 := by
    simpa [prefixWord, tailWord_5826606, baseEnd_5826606] using wordTrace_append hprefix tailTrace_5826606
  have hstable : (prefixWord ++ tailWord_5826606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826606).length < 2 ^ (prefixWord ++ tailWord_5826606).sum := by decide
  have hdescent : baseEnd_5826606 < baseStart_5826606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826659 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5826659 : Nat := 118140960795 + 5826659 * 2 ^ 59
def prefixEnd_5826659 : Nat := 4983230072969 + 3 ^ 40 * 5826659 * 2
def baseEnd_5826659 : Nat := 2991876676845623903566189

theorem tailTrace_5826659 : CollatzResearch.WordTrace tailWord_5826659 prefixEnd_5826659 2991876676845623903566189 := by
  unfold tailWord_5826659
  simp only [CollatzResearch.WordTrace]
  refine ⟨212515712598017031977227031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141677141732011354651484687 212515712598017031977227031)
  ·
    refine ⟨318773568897025547965840547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212515712598017031977227031 318773568897025547965840547)
    ·
      refine ⟨478160353345538321948760821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318773568897025547965840547 478160353345538321948760821)
      ·
        refine ⟨44827533126144217682696327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 478160353345538321948760821 44827533126144217682696327)
        ·
          refine ⟨67241299689216326524044491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44827533126144217682696327 67241299689216326524044491)
          ·
            refine ⟨100861949533824489786066737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67241299689216326524044491 100861949533824489786066737)
            ·
              refine ⟨75646462150368367339550053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100861949533824489786066737 75646462150368367339550053)
              ·
                refine ⟨14183711653194068876165635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75646462150368367339550053 14183711653194068876165635)
                ·
                  refine ⟨21275567479791103314248453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14183711653194068876165635 21275567479791103314248453)
                  ·
                    refine ⟨3989168902460831871421585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21275567479791103314248453 3989168902460831871421585)
                    ·
                      refine ⟨2991876676845623903566189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989168902460831871421585 2991876676845623903566189)
                      ·
                        rfl

theorem cell23_5826659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5826659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826659 prefixEnd_5826659 := by exact prefixLift 5826659
  have htrace : WordTrace (prefixWord ++ tailWord_5826659) baseStart_5826659 baseEnd_5826659 := by
    simpa [prefixWord, tailWord_5826659, baseEnd_5826659] using wordTrace_append hprefix tailTrace_5826659
  have hstable : (prefixWord ++ tailWord_5826659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826659).length < 2 ^ (prefixWord ++ tailWord_5826659).sum := by decide
  have hdescent : baseEnd_5826659 < baseStart_5826659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826693 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_5826693 : Nat := 118140960795 + 5826693 * 2 ^ 59
def prefixEnd_5826693 : Nat := 4983230072969 + 3 ^ 40 * 5826693 * 2
def baseEnd_5826693 : Nat := 2991894135187876770541033

theorem tailTrace_5826693 : CollatzResearch.WordTrace tailWord_5826693 prefixEnd_5826693 2991894135187876770541033 := by
  unfold tailWord_5826693
  simp only [CollatzResearch.WordTrace]
  refine ⟨212516952679893855783964733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141677968453262570522643155 212516952679893855783964733)
  ·
    refine ⟨79693857254960195918986775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212516952679893855783964733 79693857254960195918986775)
    ·
      refine ⟨119540785882440293878480163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79693857254960195918986775 119540785882440293878480163)
      ·
        refine ⟨179311178823660440817720245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119540785882440293878480163 179311178823660440817720245)
        ·
          refine ⟨16810423014718166326661273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179311178823660440817720245 16810423014718166326661273)
          ·
            refine ⟨12607817261038624744995955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16810423014718166326661273 12607817261038624744995955)
            ·
              refine ⟨18911725891557937117493933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607817261038624744995955 18911725891557937117493933)
              ·
                refine ⟨7091897209334226419060225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18911725891557937117493933 7091897209334226419060225)
                ·
                  refine ⟨5318922907000669814295169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091897209334226419060225 5318922907000669814295169)
                  ·
                    refine ⟨3989192180250502360721377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318922907000669814295169 3989192180250502360721377)
                    ·
                      refine ⟨2991894135187876770541033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989192180250502360721377 2991894135187876770541033)
                      ·
                        rfl

theorem cell23_5826693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_5826693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826693 prefixEnd_5826693 := by exact prefixLift 5826693
  have htrace : WordTrace (prefixWord ++ tailWord_5826693) baseStart_5826693 baseEnd_5826693 := by
    simpa [prefixWord, tailWord_5826693, baseEnd_5826693] using wordTrace_append hprefix tailTrace_5826693
  have hstable : (prefixWord ++ tailWord_5826693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826693).length < 2 ^ (prefixWord ++ tailWord_5826693).sum := by decide
  have hdescent : baseEnd_5826693 < baseStart_5826693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826733 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 5]
def baseStart_5826733 : Nat := 118140960795 + 5826733 * 2 ^ 59
def prefixEnd_5826733 : Nat := 4983230072969 + 3 ^ 40 * 5826733 * 2
def baseEnd_5826733 : Nat := 332434963823784068226761

theorem tailTrace_5826733 : CollatzResearch.WordTrace tailWord_5826733 prefixEnd_5826733 332434963823784068226761 := by
  unfold tailWord_5826733
  simp only [CollatzResearch.WordTrace]
  refine ⟨212518411599748942615420853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141678941066499295076947235 212518411599748942615420853)
  ·
    refine ⟨19923601087476463370195705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212518411599748942615420853 19923601087476463370195705)
    ·
      refine ⟨14942700815607347527646779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19923601087476463370195705 14942700815607347527646779)
      ·
        refine ⟨22414051223411021291470169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14942700815607347527646779 22414051223411021291470169)
        ·
          refine ⟨16810538417558265968602627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22414051223411021291470169 16810538417558265968602627)
          ·
            refine ⟨25215807626337398952903941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16810538417558265968602627 25215807626337398952903941)
            ·
              refine ⟨4727963929938262303669489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25215807626337398952903941 4727963929938262303669489)
              ·
                refine ⟨3545972947453696727752117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727963929938262303669489 3545972947453696727752117)
                ·
                  refine ⟨332434963823784068226761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3545972947453696727752117 332434963823784068226761)
                  ·
                    rfl

theorem cell23_5826733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_5826733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826733 prefixEnd_5826733 := by exact prefixLift 5826733
  have htrace : WordTrace (prefixWord ++ tailWord_5826733) baseStart_5826733 baseEnd_5826733 := by
    simpa [prefixWord, tailWord_5826733, baseEnd_5826733] using wordTrace_append hprefix tailTrace_5826733
  have hstable : (prefixWord ++ tailWord_5826733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826733).length < 2 ^ (prefixWord ++ tailWord_5826733).sum := by decide
  have hdescent : baseEnd_5826733 < baseStart_5826733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826740 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5826740 : Nat := 118140960795 + 5826740 * 2 ^ 59
def prefixEnd_5826740 : Nat := 4983230072969 + 3 ^ 40 * 5826740 * 2
def baseEnd_5826740 : Nat := 2991918268778638086653317

theorem tailTrace_5826740 : CollatzResearch.WordTrace tailWord_5826740 prefixEnd_5826740 2991918268778638086653317 := by
  unfold tailWord_5826740
  simp only [CollatzResearch.WordTrace]
  refine ⟨106259333455361791405462837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141679111273815721873950449 106259333455361791405462837)
  ·
    refine ⟨9961812511440167944262141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106259333455361791405462837 9961812511440167944262141)
    ·
      refine ⟨3735679691790062979098303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9961812511440167944262141 3735679691790062979098303)
      ·
        refine ⟨5603519537685094468647455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735679691790062979098303 5603519537685094468647455)
        ·
          refine ⟨8405279306527641702971183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603519537685094468647455 8405279306527641702971183)
          ·
            refine ⟨12607918959791462554456775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8405279306527641702971183 12607918959791462554456775)
            ·
              refine ⟨18911878439687193831685163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607918959791462554456775 18911878439687193831685163)
              ·
                refine ⟨28367817659530790747527745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18911878439687193831685163 28367817659530790747527745)
                ·
                  refine ⟨21275863244648093060645809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28367817659530790747527745 21275863244648093060645809)
                  ·
                    refine ⟨15956897433486069795484357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21275863244648093060645809 15956897433486069795484357)
                    ·
                      refine ⟨2991918268778638086653317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15956897433486069795484357 2991918268778638086653317)
                      ·
                        rfl

theorem cell23_5826740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5826740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826740 prefixEnd_5826740 := by exact prefixLift 5826740
  have htrace : WordTrace (prefixWord ++ tailWord_5826740) baseStart_5826740 baseEnd_5826740 := by
    simpa [prefixWord, tailWord_5826740, baseEnd_5826740] using wordTrace_append hprefix tailTrace_5826740
  have hstable : (prefixWord ++ tailWord_5826740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826740).length < 2 ^ (prefixWord ++ tailWord_5826740).sum := by decide
  have hdescent : baseEnd_5826740 < baseStart_5826740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826766 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_5826766 : Nat := 118140960795 + 5826766 * 2 ^ 59
def prefixEnd_5826766 : Nat := 4983230072969 + 3 ^ 40 * 5826766 * 2
def baseEnd_5826766 : Nat := 2991931619275654984928197

theorem tailTrace_5826766 : CollatzResearch.WordTrace tailWord_5826766 prefixEnd_5826766 2991931619275654984928197 := by
  unfold tailWord_5826766
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564951901078673656421519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141679743472419592834248101 26564951901078673656421519)
  ·
    refine ⟨39847427851618010484632279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26564951901078673656421519 39847427851618010484632279)
    ·
      refine ⟨59771141777427015726948419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39847427851618010484632279 59771141777427015726948419)
      ·
        refine ⟨89656712666140523590422629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59771141777427015726948419 89656712666140523590422629)
        ·
          refine ⟨16810633624901348173204243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89656712666140523590422629 16810633624901348173204243)
          ·
            refine ⟨25215950437352022259806365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16810633624901348173204243 25215950437352022259806365)
            ·
              refine ⟨9455981414007008347427387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25215950437352022259806365 9455981414007008347427387)
              ·
                refine ⟨14183972121010512521141081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9455981414007008347427387 14183972121010512521141081)
                ·
                  refine ⟨10637979090757884390855811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14183972121010512521141081 10637979090757884390855811)
                  ·
                    refine ⟨15956968636136826586283717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10637979090757884390855811 15956968636136826586283717)
                    ·
                      refine ⟨2991931619275654984928197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15956968636136826586283717 2991931619275654984928197)
                      ·
                        rfl

theorem cell23_5826766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_5826766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826766 prefixEnd_5826766 := by exact prefixLift 5826766
  have htrace : WordTrace (prefixWord ++ tailWord_5826766) baseStart_5826766 baseEnd_5826766 := by
    simpa [prefixWord, tailWord_5826766, baseEnd_5826766] using wordTrace_append hprefix tailTrace_5826766
  have hstable : (prefixWord ++ tailWord_5826766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826766).length < 2 ^ (prefixWord ++ tailWord_5826766).sum := by decide
  have hdescent : baseEnd_5826766 < baseStart_5826766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826789 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 8]
def baseStart_5826789 : Nat := 118140960795 + 5826789 * 2 ^ 59
def prefixEnd_5826789 : Nat := 4983230072969 + 3 ^ 40 * 5826789 * 2
def baseEnd_5826789 : Nat := 332438158814523154993399

theorem tailTrace_5826789 : CollatzResearch.WordTrace tailWord_5826789 prefixEnd_5826789 332438158814523154993399 := by
  unfold tailWord_5826789
  simp only [CollatzResearch.WordTrace]
  refine ⟨212520454087546064179459421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141680302725030709452972947 212520454087546064179459421)
  ·
    refine ⟨79695170282829774067297283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212520454087546064179459421 79695170282829774067297283)
    ·
      refine ⟨119542755424244661100945925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79695170282829774067297283 119542755424244661100945925)
      ·
        refine ⟨22414266642045873956427361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119542755424244661100945925 22414266642045873956427361)
        ·
          refine ⟨16810699981534405467320521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22414266642045873956427361 16810699981534405467320521)
          ·
            refine ⟨12608024986150804100490391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16810699981534405467320521 12608024986150804100490391)
            ·
              refine ⟨18912037479226206150735587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12608024986150804100490391 18912037479226206150735587)
              ·
                refine ⟨28368056218839309226103381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18912037479226206150735587 28368056218839309226103381)
                ·
                  refine ⟨332438158814523154993399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28368056218839309226103381 332438158814523154993399)
                  ·
                    rfl

theorem cell23_5826789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_5826789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826789 prefixEnd_5826789 := by exact prefixLift 5826789
  have htrace : WordTrace (prefixWord ++ tailWord_5826789) baseStart_5826789 baseEnd_5826789 := by
    simpa [prefixWord, tailWord_5826789, baseEnd_5826789] using wordTrace_append hprefix tailTrace_5826789
  have hstable : (prefixWord ++ tailWord_5826789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826789).length < 2 ^ (prefixWord ++ tailWord_5826789).sum := by decide
  have hdescent : baseEnd_5826789 < baseStart_5826789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826816 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3]
def baseStart_5826816 : Nat := 118140960795 + 5826816 * 2 ^ 59
def prefixEnd_5826816 : Nat := 4983230072969 + 3 ^ 40 * 5826816 * 2
def baseEnd_5826816 : Nat := 2991957293308379789302967

theorem tailTrace_5826816 : CollatzResearch.WordTrace tailWord_5826816 prefixEnd_5826816 2991957293308379789302967 := by
  unfold tailWord_5826816
  simp only [CollatzResearch.WordTrace]
  refine ⟨106260719429224123895346151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141680959238965498527128201 106260719429224123895346151)
  ·
    refine ⟨159391079143836185843019227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106260719429224123895346151 159391079143836185843019227)
    ·
      refine ⟨239086618715754278764528841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159391079143836185843019227 239086618715754278764528841)
      ·
        refine ⟨179314964036815709073396631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239086618715754278764528841 179314964036815709073396631)
        ·
          refine ⟨268972446055223563610094947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179314964036815709073396631 268972446055223563610094947)
          ·
            refine ⟨403458669082835345415142421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268972446055223563610094947 403458669082835345415142421)
            ·
              refine ⟨18912125113257906816334801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403458669082835345415142421 18912125113257906816334801)
              ·
                refine ⟨14184093834943430112251101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18912125113257906816334801 14184093834943430112251101)
                ·
                  refine ⟨5319035188103786292094163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14184093834943430112251101 5319035188103786292094163)
                  ·
                    refine ⟨7978552782155679438141245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319035188103786292094163 7978552782155679438141245)
                    ·
                      refine ⟨2991957293308379789302967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978552782155679438141245 2991957293308379789302967)
                      ·
                        rfl

theorem cell23_5826816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_5826816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826816 prefixEnd_5826816 := by exact prefixLift 5826816
  have htrace : WordTrace (prefixWord ++ tailWord_5826816) baseStart_5826816 baseEnd_5826816 := by
    simpa [prefixWord, tailWord_5826816, baseEnd_5826816] using wordTrace_append hprefix tailTrace_5826816
  have hstable : (prefixWord ++ tailWord_5826816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826816).length < 2 ^ (prefixWord ++ tailWord_5826816).sum := by decide
  have hdescent : baseEnd_5826816 < baseStart_5826816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826826 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_5826826 : Nat := 118140960795 + 5826826 * 2 ^ 59
def prefixEnd_5826826 : Nat := 4983230072969 + 3 ^ 40 * 5826826 * 2
def baseEnd_5826826 : Nat := 2991962428114924750177921

theorem tailTrace_5826826 : CollatzResearch.WordTrace tailWord_5826826 prefixEnd_5826826 2991962428114924750177921 := by
  unfold tailWord_5826826
  simp only [CollatzResearch.WordTrace]
  refine ⟨53130450897103004874639083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141681202392274679665704221 53130450897103004874639083)
  ·
    refine ⟨79695676345654507311958625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53130450897103004874639083 79695676345654507311958625)
    ·
      refine ⟨59771757259240880483968969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79695676345654507311958625 59771757259240880483968969)
      ·
        refine ⟨44828817944430660362976727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59771757259240880483968969 44828817944430660362976727)
        ·
          refine ⟨67243226916645990544465091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44828817944430660362976727 67243226916645990544465091)
          ·
            refine ⟨100864840374968985816697637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67243226916645990544465091 100864840374968985816697637)
            ·
              refine ⟨18912157570306684840630807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100864840374968985816697637 18912157570306684840630807)
              ·
                refine ⟨28368236355460027260946211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18912157570306684840630807 28368236355460027260946211)
                ·
                  refine ⟨42552354533190040891419317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28368236355460027260946211 42552354533190040891419317)
                  ·
                    refine ⟨3989283237486566333570561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42552354533190040891419317 3989283237486566333570561)
                    ·
                      refine ⟨2991962428114924750177921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989283237486566333570561 2991962428114924750177921)
                      ·
                        rfl

theorem cell23_5826826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_5826826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826826 prefixEnd_5826826 := by exact prefixLift 5826826
  have htrace : WordTrace (prefixWord ++ tailWord_5826826) baseStart_5826826 baseEnd_5826826 := by
    simpa [prefixWord, tailWord_5826826, baseEnd_5826826] using wordTrace_append hprefix tailTrace_5826826
  have hstable : (prefixWord ++ tailWord_5826826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826826).length < 2 ^ (prefixWord ++ tailWord_5826826).sum := by decide
  have hdescent : baseEnd_5826826 < baseStart_5826826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826850 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_5826850 : Nat := 118140960795 + 5826850 * 2 ^ 59
def prefixEnd_5826850 : Nat := 4983230072969 + 3 ^ 40 * 5826850 * 2
def baseEnd_5826850 : Nat := 2991974751650632656277811

theorem tailTrace_5826850 : CollatzResearch.WordTrace tailWord_5826850 prefixEnd_5826850 2991974751650632656277811 := by
  unfold tailWord_5826850
  simp only [CollatzResearch.WordTrace]
  refine ⟨53130669735081267899357501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141681785960216714398286669 53130669735081267899357501)
  ·
    refine ⟨19924001150655475462259063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53130669735081267899357501 19924001150655475462259063)
    ·
      refine ⟨29886001725983213193388595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19924001150655475462259063 29886001725983213193388595)
      ·
        refine ⟨44829002588974819790082893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29886001725983213193388595 44829002588974819790082893)
        ·
          refine ⟨16810875970865557421281085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44829002588974819790082893 16810875970865557421281085)
          ·
            refine ⟨6304078489074584032980407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16810875970865557421281085 6304078489074584032980407)
            ·
              refine ⟨9456117733611876049470611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304078489074584032980407 9456117733611876049470611)
              ·
                refine ⟨14184176600417814074205917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456117733611876049470611 14184176600417814074205917)
                ·
                  refine ⟨5319066225156680277827219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14184176600417814074205917 5319066225156680277827219)
                  ·
                    refine ⟨7978599337735020416740829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319066225156680277827219 7978599337735020416740829)
                    ·
                      refine ⟨2991974751650632656277811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978599337735020416740829 2991974751650632656277811)
                      ·
                        rfl

theorem cell23_5826850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_5826850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826850 prefixEnd_5826850 := by exact prefixLift 5826850
  have htrace : WordTrace (prefixWord ++ tailWord_5826850) baseStart_5826850 baseEnd_5826850 := by
    simpa [prefixWord, tailWord_5826850, baseEnd_5826850] using wordTrace_append hprefix tailTrace_5826850
  have hstable : (prefixWord ++ tailWord_5826850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826850).length < 2 ^ (prefixWord ++ tailWord_5826850).sum := by decide
  have hdescent : baseEnd_5826850 < baseStart_5826850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826869 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_5826869 : Nat := 118140960795 + 5826869 * 2 ^ 59
def prefixEnd_5826869 : Nat := 4983230072969 + 3 ^ 40 * 5826869 * 2
def baseEnd_5826869 : Nat := 2991984507783068081940223

theorem tailTrace_5826869 : CollatzResearch.WordTrace tailWord_5826869 prefixEnd_5826869 2991984507783068081940223 := by
  unfold tailWord_5826869
  simp only [CollatzResearch.WordTrace]
  refine ⟨212523371927256237842371661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141682247951504158561581107 212523371927256237842371661)
  ·
    refine ⟨79696264472721089190889373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212523371927256237842371661 79696264472721089190889373)
    ·
      refine ⟨29886099177270408446583515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79696264472721089190889373 29886099177270408446583515)
      ·
        refine ⟨44829148765905612669875273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29886099177270408446583515 44829148765905612669875273)
        ·
          refine ⟨33621861574429209502406455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44829148765905612669875273 33621861574429209502406455)
          ·
            refine ⟨50432792361643814253609683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33621861574429209502406455 50432792361643814253609683)
            ·
              refine ⟨75649188542465721380414525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50432792361643814253609683 75649188542465721380414525)
              ·
                refine ⟨28368445703424645517655447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75649188542465721380414525 28368445703424645517655447)
                ·
                  refine ⟨42552668555136968276483171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28368445703424645517655447 42552668555136968276483171)
                  ·
                    refine ⟨63829002832705452414724757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42552668555136968276483171 63829002832705452414724757)
                    ·
                      refine ⟨2991984507783068081940223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63829002832705452414724757 2991984507783068081940223)
                      ·
                        rfl

theorem cell23_5826869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_5826869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826869 prefixEnd_5826869 := by exact prefixLift 5826869
  have htrace : WordTrace (prefixWord ++ tailWord_5826869) baseStart_5826869 baseEnd_5826869 := by
    simpa [prefixWord, tailWord_5826869, baseEnd_5826869] using wordTrace_append hprefix tailTrace_5826869
  have hstable : (prefixWord ++ tailWord_5826869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826869).length < 2 ^ (prefixWord ++ tailWord_5826869).sum := by decide
  have hdescent : baseEnd_5826869 < baseStart_5826869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826873 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5826873 : Nat := 118140960795 + 5826873 * 2 ^ 59
def prefixEnd_5826873 : Nat := 4983230072969 + 3 ^ 40 * 5826873 * 2
def baseEnd_5826873 : Nat := 2991986561705686066290205

theorem tailTrace_5826873 : CollatzResearch.WordTrace tailWord_5826873 prefixEnd_5826873 2991986561705686066290205 := by
  unfold tailWord_5826873
  simp only [CollatzResearch.WordTrace]
  refine ⟨212523517819241746525517273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141682345212827831017011515 212523517819241746525517273)
  ·
    refine ⟨159392638364431309894137955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212523517819241746525517273 159392638364431309894137955)
    ·
      refine ⟨239088957546646964841206933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159392638364431309894137955 239088957546646964841206933)
      ·
        refine ⟨11207294884999076476931575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 239088957546646964841206933 11207294884999076476931575)
        ·
          refine ⟨16810942327498614715397363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11207294884999076476931575 16810942327498614715397363)
          ·
            refine ⟨25216413491247922073096045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16810942327498614715397363 25216413491247922073096045)
            ·
              refine ⟨9456155059217970777411017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25216413491247922073096045 9456155059217970777411017)
              ·
                refine ⟨7092116294413478083058263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9456155059217970777411017 7092116294413478083058263)
                ·
                  refine ⟨10638174441620217124587395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092116294413478083058263 10638174441620217124587395)
                  ·
                    refine ⟨15957261662430325686881093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10638174441620217124587395 15957261662430325686881093)
                    ·
                      refine ⟨2991986561705686066290205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15957261662430325686881093 2991986561705686066290205)
                      ·
                        rfl

theorem cell23_5826873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5826873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826873 prefixEnd_5826873 := by exact prefixLift 5826873
  have htrace : WordTrace (prefixWord ++ tailWord_5826873) baseStart_5826873 baseEnd_5826873 := by
    simpa [prefixWord, tailWord_5826873, baseEnd_5826873] using wordTrace_append hprefix tailTrace_5826873
  have hstable : (prefixWord ++ tailWord_5826873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826873).length < 2 ^ (prefixWord ++ tailWord_5826873).sum := by decide
  have hdescent : baseEnd_5826873 < baseStart_5826873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826876 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_5826876 : Nat := 118140960795 + 5826876 * 2 ^ 59
def prefixEnd_5826876 : Nat := 4983230072969 + 3 ^ 40 * 5826876 * 2
def baseEnd_5826876 : Nat := 2991988102147649554552691

theorem tailTrace_5826876 : CollatzResearch.WordTrace tailWord_5826876 prefixEnd_5826876 2991988102147649554552691 := by
  unfold tailWord_5826876
  simp only [CollatzResearch.WordTrace]
  refine ⟨106261813619115439018938241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141682418158820585358584321 106261813619115439018938241)
  ·
    refine ⟨79696360214336579264203681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106261813619115439018938241 79696360214336579264203681)
    ·
      refine ⟨59772270160752434448152761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79696360214336579264203681 59772270160752434448152761)
      ·
        refine ⟨44829202620564325836114571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59772270160752434448152761 44829202620564325836114571)
        ·
          refine ⟨67243803930846488754171857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44829202620564325836114571 67243803930846488754171857)
          ·
            refine ⟨50432852948134866565628893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67243803930846488754171857 50432852948134866565628893)
            ·
              refine ⟨18912319855550574962110835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50432852948134866565628893 18912319855550574962110835)
              ·
                refine ⟨28368479783325862443166253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18912319855550574962110835 28368479783325862443166253)
                ·
                  refine ⟨10638179918747198416187345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28368479783325862443166253 10638179918747198416187345)
                  ·
                    refine ⟨7978634939060398812140509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10638179918747198416187345 7978634939060398812140509)
                    ·
                      refine ⟨2991988102147649554552691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978634939060398812140509 2991988102147649554552691)
                      ·
                        rfl

theorem cell23_5826876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_5826876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826876 prefixEnd_5826876 := by exact prefixLift 5826876
  have htrace : WordTrace (prefixWord ++ tailWord_5826876) baseStart_5826876 baseEnd_5826876 := by
    simpa [prefixWord, tailWord_5826876, baseEnd_5826876] using wordTrace_append hprefix tailTrace_5826876
  have hstable : (prefixWord ++ tailWord_5826876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826876).length < 2 ^ (prefixWord ++ tailWord_5826876).sum := by decide
  have hdescent : baseEnd_5826876 < baseStart_5826876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826929 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_5826929 : Nat := 118140960795 + 5826929 * 2 ^ 59
def prefixEnd_5826929 : Nat := 4983230072969 + 3 ^ 40 * 5826929 * 2
def baseEnd_5826929 : Nat := 2992015316622337847189947

theorem tailTrace_5826929 : CollatzResearch.WordTrace tailWord_5826929 prefixEnd_5826929 2992015316622337847189947 := by
  unfold tailWord_5826929
  simp only [CollatzResearch.WordTrace]
  refine ⟨212525560307038868089555841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141683706871359245393037227 212525560307038868089555841)
  ·
    refine ⟨159394170230279151067166881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212525560307038868089555841 159394170230279151067166881)
    ·
      refine ⟨119545627672709363300375161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159394170230279151067166881 119545627672709363300375161)
      ·
        refine ⟨89659220754532022475281371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119545627672709363300375161 89659220754532022475281371)
        ·
          refine ⟨134488831131798033712922057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89659220754532022475281371 134488831131798033712922057)
          ·
            refine ⟨100866623348848525284691543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134488831131798033712922057 100866623348848525284691543)
            ·
              refine ⟨151299935023272787927037315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100866623348848525284691543 151299935023272787927037315)
              ·
                refine ⟨226949902534909181890555973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151299935023272787927037315 226949902534909181890555973)
                ·
                  refine ⟨42553106725295471604479245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226949902534909181890555973 42553106725295471604479245)
                  ·
                    refine ⟨15957415021985801851679717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42553106725295471604479245 15957415021985801851679717)
                    ·
                      refine ⟨2992015316622337847189947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15957415021985801851679717 2992015316622337847189947)
                      ·
                        rfl

theorem cell23_5826929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_5826929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826929 prefixEnd_5826929 := by exact prefixLift 5826929
  have htrace : WordTrace (prefixWord ++ tailWord_5826929) baseStart_5826929 baseEnd_5826929 := by
    simpa [prefixWord, tailWord_5826929, baseEnd_5826929] using wordTrace_append hprefix tailTrace_5826929
  have hstable : (prefixWord ++ tailWord_5826929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826929).length < 2 ^ (prefixWord ++ tailWord_5826929).sum := by decide
  have hdescent : baseEnd_5826929 < baseStart_5826929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826949 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_5826949 : Nat := 118140960795 + 5826949 * 2 ^ 59
def prefixEnd_5826949 : Nat := 4983230072969 + 3 ^ 40 * 5826949 * 2
def baseEnd_5826949 : Nat := 2992025586235427768939855

theorem tailTrace_5826949 : CollatzResearch.WordTrace tailWord_5826949 prefixEnd_5826949 2992025586235427768939855 := by
  unfold tailWord_5826949
  simp only [CollatzResearch.WordTrace]
  refine ⟨212526289766966411505283901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141684193177977607670189267 212526289766966411505283901)
  ·
    refine ⟨79697358662612404314481463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212526289766966411505283901 79697358662612404314481463)
    ·
      refine ⟨119546037993918606471722195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79697358662612404314481463 119546037993918606471722195)
      ·
        refine ⟨179319056990877909707583293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119546037993918606471722195 179319056990877909707583293)
        ·
          refine ⟨67244646371579216140343735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179319056990877909707583293 67244646371579216140343735)
          ·
            refine ⟨100866969557368824210515603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67244646371579216140343735 100866969557368824210515603)
            ·
              refine ⟨151300454336053236315773405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100866969557368824210515603 151300454336053236315773405)
              ·
                refine ⟨56737670376019963618415027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151300454336053236315773405 56737670376019963618415027)
                ·
                  refine ⟨85106505564029945427622541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56737670376019963618415027 85106505564029945427622541)
                  ·
                    refine ⟨31914939586511229535358453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85106505564029945427622541 31914939586511229535358453)
                    ·
                      refine ⟨2992025586235427768939855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31914939586511229535358453 2992025586235427768939855)
                      ·
                        rfl

theorem cell23_5826949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_5826949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826949 prefixEnd_5826949 := by exact prefixLift 5826949
  have htrace : WordTrace (prefixWord ++ tailWord_5826949) baseStart_5826949 baseEnd_5826949 := by
    simpa [prefixWord, tailWord_5826949, baseEnd_5826949] using wordTrace_append hprefix tailTrace_5826949
  have hstable : (prefixWord ++ tailWord_5826949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826949).length < 2 ^ (prefixWord ++ tailWord_5826949).sum := by decide
  have hdescent : baseEnd_5826949 < baseStart_5826949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826974 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5826974 : Nat := 118140960795 + 5826974 * 2 ^ 59
def prefixEnd_5826974 : Nat := 4983230072969 + 3 ^ 40 * 5826974 * 2
def baseEnd_5826974 : Nat := 2992038423251790171127241

theorem tailTrace_5826974 : CollatzResearch.WordTrace tailWord_5826974 prefixEnd_5826974 2992038423251790171127241 := by
  unfold tailWord_5826974
  simp only [CollatzResearch.WordTrace]
  refine ⟨26565900198984480096867997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141684801061250560516629317 26565900198984480096867997)
  ·
    refine ⟨9962212574619180036325499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26565900198984480096867997 9962212574619180036325499)
    ·
      refine ⟨14943318861928770054488249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9962212574619180036325499 14943318861928770054488249)
      ·
        refine ⟨11207489146446577540866187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14943318861928770054488249 11207489146446577540866187)
        ·
          refine ⟨16811233719669866311299281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11207489146446577540866187 16811233719669866311299281)
          ·
            refine ⟨12608425289752399733474461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16811233719669866311299281 12608425289752399733474461)
            ·
              refine ⟨4728159483657149900052923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12608425289752399733474461 4728159483657149900052923)
              ·
                refine ⟨7092239225485724850079385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728159483657149900052923 7092239225485724850079385)
                ·
                  refine ⟨5319179419114293637559539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7092239225485724850079385 5319179419114293637559539)
                  ·
                    refine ⟨7978769128671440456339309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319179419114293637559539 7978769128671440456339309)
                    ·
                      refine ⟨2992038423251790171127241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978769128671440456339309 2992038423251790171127241)
                      ·
                        rfl

theorem cell23_5826974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5826974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826974 prefixEnd_5826974 := by exact prefixLift 5826974
  have htrace : WordTrace (prefixWord ++ tailWord_5826974) baseStart_5826974 baseEnd_5826974 := by
    simpa [prefixWord, tailWord_5826974, baseEnd_5826974] using wordTrace_append hprefix tailTrace_5826974
  have hstable : (prefixWord ++ tailWord_5826974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826974).length < 2 ^ (prefixWord ++ tailWord_5826974).sum := by decide
  have hdescent : baseEnd_5826974 < baseStart_5826974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826976 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_5826976 : Nat := 118140960795 + 5826976 * 2 ^ 59
def prefixEnd_5826976 : Nat := 4983230072969 + 3 ^ 40 * 5826976 * 2
def baseEnd_5826976 : Nat := 2992039450213099163302231

theorem tailTrace_5826976 : CollatzResearch.WordTrace tailWord_5826976 prefixEnd_5826976 2992039450213099163302231 := by
  unfold tailWord_5826976
  simp only [CollatzResearch.WordTrace]
  refine ⟨106263637268934297558258391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141684849691912396744344521 106263637268934297558258391)
  ·
    refine ⟨159395455903401446337387587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106263637268934297558258391 159395455903401446337387587)
    ·
      refine ⟨239093183855102169506081381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159395455903401446337387587 239093183855102169506081381)
      ·
        refine ⟨44829971972831656782390259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239093183855102169506081381 44829971972831656782390259)
        ·
          refine ⟨67244957959247485173585389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44829971972831656782390259 67244957959247485173585389)
          ·
            refine ⟨25216859234717806940094521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67244957959247485173585389 25216859234717806940094521)
            ·
              refine ⟨18912644426038355205070891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25216859234717806940094521 18912644426038355205070891)
              ·
                refine ⟨28368966639057532807606337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18912644426038355205070891 28368966639057532807606337)
                ·
                  refine ⟨21276724979293149605704753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28368966639057532807606337 21276724979293149605704753)
                  ·
                    refine ⟨15957543734469862204278565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21276724979293149605704753 15957543734469862204278565)
                    ·
                      refine ⟨2992039450213099163302231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15957543734469862204278565 2992039450213099163302231)
                      ·
                        rfl

theorem cell23_5826976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_5826976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826976 prefixEnd_5826976 := by exact prefixLift 5826976
  have htrace : WordTrace (prefixWord ++ tailWord_5826976) baseStart_5826976 baseEnd_5826976 := by
    simpa [prefixWord, tailWord_5826976, baseEnd_5826976] using wordTrace_append hprefix tailTrace_5826976
  have hstable : (prefixWord ++ tailWord_5826976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826976).length < 2 ^ (prefixWord ++ tailWord_5826976).sum := by decide
  have hdescent : baseEnd_5826976 < baseStart_5826976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5826980 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_5826980 : Nat := 118140960795 + 5826980 * 2 ^ 59
def prefixEnd_5826980 : Nat := 4983230072969 + 3 ^ 40 * 5826980 * 2
def baseEnd_5826980 : Nat := 2992041504135717147652213

theorem tailTrace_5826980 : CollatzResearch.WordTrace tailWord_5826980 prefixEnd_5826980 2992041504135717147652213 := by
  unfold tailWord_5826980
  simp only [CollatzResearch.WordTrace]
  refine ⟨106263710214927051899831197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141684946953236069199774929 106263710214927051899831197)
  ·
    refine ⟨39848891330597644462436699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106263710214927051899831197 39848891330597644462436699)
    ·
      refine ⟨59773336995896466693655049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39848891330597644462436699 59773336995896466693655049)
      ·
        refine ⟨44830002746922350020241287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59773336995896466693655049 44830002746922350020241287)
        ·
          refine ⟨67245004120383525030361931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44830002746922350020241287 67245004120383525030361931)
          ·
            refine ⟨100867506180575287545542897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67245004120383525030361931 100867506180575287545542897)
            ·
              refine ⟨75650629635431465659157173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100867506180575287545542897 75650629635431465659157173)
              ·
                refine ⟨7092246528321699905545985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75650629635431465659157173 7092246528321699905545985)
                ·
                  refine ⟨5319184896241274929159489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7092246528321699905545985 5319184896241274929159489)
                  ·
                    refine ⟨3989388672180956196869617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5319184896241274929159489 3989388672180956196869617)
                    ·
                      refine ⟨2992041504135717147652213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989388672180956196869617 2992041504135717147652213)
                      ·
                        rfl

theorem cell23_5826980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_5826980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5826980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5826980 prefixEnd_5826980 := by exact prefixLift 5826980
  have htrace : WordTrace (prefixWord ++ tailWord_5826980) baseStart_5826980 baseEnd_5826980 := by
    simpa [prefixWord, tailWord_5826980, baseEnd_5826980] using wordTrace_append hprefix tailTrace_5826980
  have hstable : (prefixWord ++ tailWord_5826980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5826980).length < 2 ^ (prefixWord ++ tailWord_5826980).sum := by decide
  have hdescent : baseEnd_5826980 < baseStart_5826980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5826980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827016 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_5827016 : Nat := 118140960795 + 5827016 * 2 ^ 59
def prefixEnd_5827016 : Nat := 4983230072969 + 3 ^ 40 * 5827016 * 2
def baseEnd_5827016 : Nat := 997353329813093002267349

theorem tailTrace_5827016 : CollatzResearch.WordTrace tailWord_5827016 prefixEnd_5827016 997353329813093002267349 := by
  unfold tailWord_5827016
  simp only [CollatzResearch.WordTrace]
  refine ⟨106264366728861840973986451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141685822305149121298648601 106264366728861840973986451)
  ·
    refine ⟨159396550093292761460979677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106264366728861840973986451 159396550093292761460979677)
    ·
      refine ⟨59773706284984785547867379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159396550093292761460979677 59773706284984785547867379)
      ·
        refine ⟨89660559427477178321801069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59773706284984785547867379 89660559427477178321801069)
        ·
          refine ⟨33622709785303941870675401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89660559427477178321801069 33622709785303941870675401)
          ·
            refine ⟨25217032338977956403006551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33622709785303941870675401 25217032338977956403006551)
            ·
              refine ⟨37825548508466934604509827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25217032338977956403006551 37825548508466934604509827)
              ·
                refine ⟨56738322762700401906764741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37825548508466934604509827 56738322762700401906764741)
                ·
                  refine ⟨10638435518006325357518389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56738322762700401906764741 10638435518006325357518389)
                  ·
                    refine ⟨997353329813093002267349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10638435518006325357518389 997353329813093002267349)
                    ·
                      rfl

theorem cell23_5827016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_5827016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827016 prefixEnd_5827016 := by exact prefixLift 5827016
  have htrace : WordTrace (prefixWord ++ tailWord_5827016) baseStart_5827016 baseEnd_5827016 := by
    simpa [prefixWord, tailWord_5827016, baseEnd_5827016] using wordTrace_append hprefix tailTrace_5827016
  have hstable : (prefixWord ++ tailWord_5827016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827016).length < 2 ^ (prefixWord ++ tailWord_5827016).sum := by decide
  have hdescent : baseEnd_5827016 < baseStart_5827016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827020 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 7]
def baseStart_5827020 : Nat := 118140960795 + 5827020 * 2 ^ 59
def prefixEnd_5827020 : Nat := 4983230072969 + 3 ^ 40 * 5827020 * 2
def baseEnd_5827020 : Nat := 332451338151321887905781

theorem tailTrace_5827020 : CollatzResearch.WordTrace tailWord_5827020 prefixEnd_5827020 332451338151321887905781 := by
  unfold tailWord_5827020
  simp only [CollatzResearch.WordTrace]
  refine ⟨106264439674854595315559257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141685919566472793754079009 106264439674854595315559257)
  ·
    refine ⟨79698329756140946486669443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106264439674854595315559257 79698329756140946486669443)
    ·
      refine ⟨119547494634211419730004165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79698329756140946486669443 119547494634211419730004165)
      ·
        refine ⟨22415155243914641199375781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119547494634211419730004165 22415155243914641199375781)
        ·
          refine ⟨4202841608233995224882959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22415155243914641199375781 4202841608233995224882959)
          ·
            refine ⟨6304262412350992837324439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202841608233995224882959 6304262412350992837324439)
            ·
              refine ⟨9456393618526489255986659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304262412350992837324439 9456393618526489255986659)
              ·
                refine ⟨14184590427789733883979989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456393618526489255986659 14184590427789733883979989)
                ·
                  refine ⟨332451338151321887905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14184590427789733883979989 332451338151321887905781)
                  ·
                    rfl

theorem cell23_5827020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_5827020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827020 prefixEnd_5827020 := by exact prefixLift 5827020
  have htrace : WordTrace (prefixWord ++ tailWord_5827020) baseStart_5827020 baseEnd_5827020 := by
    simpa [prefixWord, tailWord_5827020, baseEnd_5827020] using wordTrace_append hprefix tailTrace_5827020
  have hstable : (prefixWord ++ tailWord_5827020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827020).length < 2 ^ (prefixWord ++ tailWord_5827020).sum := by decide
  have hdescent : baseEnd_5827020 < baseStart_5827020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827123 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 1, 5]
def baseStart_5827123 : Nat := 118140960795 + 5827123 * 2 ^ 59
def prefixEnd_5827123 : Nat := 4983230072969 + 3 ^ 40 * 5827123 * 2
def baseEnd_5827123 : Nat := 997371643956436696054685

theorem tailTrace_5827123 : CollatzResearch.WordTrace tailWord_5827123 prefixEnd_5827123 997371643956436696054685 := by
  unfold tailWord_5827123
  simp only [CollatzResearch.WordTrace]
  refine ⟨212532636068336039222118023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141688424045557359481412015 212532636068336039222118023)
  ·
    refine ⟨318798954102504058833177035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212532636068336039222118023 318798954102504058833177035)
    ·
      refine ⟨478198431153756088249765553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318798954102504058833177035 478198431153756088249765553)
      ·
        refine ⟨358648823365317066187324165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478198431153756088249765553 358648823365317066187324165)
        ·
          refine ⟨67246654380996949910123281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358648823365317066187324165 67246654380996949910123281)
          ·
            refine ⟨50434990785747712432592461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67246654380996949910123281 50434990785747712432592461)
            ·
              refine ⟨18913121544655392162222173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50434990785747712432592461 18913121544655392162222173)
              ·
                refine ⟨7092420579245772060833315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18913121544655392162222173 7092420579245772060833315)
                ·
                  refine ⟨10638630868868658091249973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092420579245772060833315 10638630868868658091249973)
                  ·
                    refine ⟨997371643956436696054685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10638630868868658091249973 997371643956436696054685)
                    ·
                      rfl

theorem cell23_5827123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 5].length) (baseStart_5827123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827123 prefixEnd_5827123 := by exact prefixLift 5827123
  have htrace : WordTrace (prefixWord ++ tailWord_5827123) baseStart_5827123 baseEnd_5827123 := by
    simpa [prefixWord, tailWord_5827123, baseEnd_5827123] using wordTrace_append hprefix tailTrace_5827123
  have hstable : (prefixWord ++ tailWord_5827123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827123).length < 2 ^ (prefixWord ++ tailWord_5827123).sum := by decide
  have hdescent : baseEnd_5827123 < baseStart_5827123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827136 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_5827136 : Nat := 118140960795 + 5827136 * 2 ^ 59
def prefixEnd_5827136 : Nat := 4983230072969 + 3 ^ 40 * 5827136 * 2
def baseEnd_5827136 : Nat := 997373869039272845767165

theorem tailTrace_5827136 : CollatzResearch.WordTrace tailWord_5827136 prefixEnd_5827136 997373869039272845767165 := by
  unfold tailWord_5827136
  simp only [CollatzResearch.WordTrace]
  refine ⟨106266555108644471221170631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141688740144859294961560841 106266555108644471221170631)
  ·
    refine ⟨159399832662966706831755947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106266555108644471221170631 159399832662966706831755947)
    ·
      refine ⟨239099748994450060247633921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159399832662966706831755947 239099748994450060247633921)
      ·
        refine ⟨179324811745837545185725441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239099748994450060247633921 179324811745837545185725441)
        ·
          refine ⟨134493608809378158889294081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179324811745837545185725441 134493608809378158889294081)
          ·
            refine ⟨100870206607033619166970561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134493608809378158889294081 100870206607033619166970561)
            ·
              refine ⟨75652654955275214375227921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100870206607033619166970561 75652654955275214375227921)
              ·
                refine ⟨56739491216456410781420941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75652654955275214375227921 56739491216456410781420941)
                ·
                  refine ⟨21277309206171154043032853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56739491216456410781420941 21277309206171154043032853)
                  ·
                    refine ⟨997373869039272845767165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21277309206171154043032853 997373869039272845767165)
                    ·
                      rfl

theorem cell23_5827136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_5827136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827136 prefixEnd_5827136 := by exact prefixLift 5827136
  have htrace : WordTrace (prefixWord ++ tailWord_5827136) baseStart_5827136 baseEnd_5827136 := by
    simpa [prefixWord, tailWord_5827136, baseEnd_5827136] using wordTrace_append hprefix tailTrace_5827136
  have hstable : (prefixWord ++ tailWord_5827136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827136).length < 2 ^ (prefixWord ++ tailWord_5827136).sum := by decide
  have hdescent : baseEnd_5827136 < baseStart_5827136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827137 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5827137 : Nat := 118140960795 + 5827137 * 2 ^ 59
def prefixEnd_5827137 : Nat := 4983230072969 + 3 ^ 40 * 5827137 * 2
def baseEnd_5827137 : Nat := 2992122120598473033388991

theorem tailTrace_5827137 : CollatzResearch.WordTrace tailWord_5827137 prefixEnd_5827137 2992122120598473033388991 := by
  unfold tailWord_5827137
  simp only [CollatzResearch.WordTrace]
  refine ⟨212533146690285319613127665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141688764460190213075418443 212533146690285319613127665)
  ·
    refine ⟨159399860017713989709845749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212533146690285319613127665 159399860017713989709845749)
    ·
      refine ⟨14943736876660686535298039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159399860017713989709845749 14943736876660686535298039)
      ·
        refine ⟨22415605314991029802947059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14943736876660686535298039 22415605314991029802947059)
        ·
          refine ⟨33623407972486544704420589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22415605314991029802947059 33623407972486544704420589)
          ·
            refine ⟨12608777989682454264157721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33623407972486544704420589 12608777989682454264157721)
            ·
              refine ⟨9456583492261840698118291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12608777989682454264157721 9456583492261840698118291)
              ·
                refine ⟨14184875238392761047177437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456583492261840698118291 14184875238392761047177437)
                ·
                  refine ⟨5319328214397285392691539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14184875238392761047177437 5319328214397285392691539)
                  ·
                    refine ⟨7978992321595928089037309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319328214397285392691539 7978992321595928089037309)
                    ·
                      refine ⟨2992122120598473033388991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7978992321595928089037309 2992122120598473033388991)
                      ·
                        rfl

theorem cell23_5827137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5827137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827137 prefixEnd_5827137 := by exact prefixLift 5827137
  have htrace : WordTrace (prefixWord ++ tailWord_5827137) baseStart_5827137 baseEnd_5827137 := by
    simpa [prefixWord, tailWord_5827137, baseEnd_5827137] using wordTrace_append hprefix tailTrace_5827137
  have hstable : (prefixWord ++ tailWord_5827137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827137).length < 2 ^ (prefixWord ++ tailWord_5827137).sum := by decide
  have hdescent : baseEnd_5827137 < baseStart_5827137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827153 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_5827153 : Nat := 118140960795 + 5827153 * 2 ^ 59
def prefixEnd_5827153 : Nat := 4983230072969 + 3 ^ 40 * 5827153 * 2
def baseEnd_5827153 : Nat := 997376778762981656929639

theorem tailTrace_5827153 : CollatzResearch.WordTrace tailWord_5827153 prefixEnd_5827153 997376778762981656929639 := by
  unfold tailWord_5827153
  simp only [CollatzResearch.WordTrace]
  refine ⟨212533730258227354345710113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141689153505484902897140075 212533730258227354345710113)
  ·
    refine ⟨159400297693670515759282585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212533730258227354345710113 159400297693670515759282585)
    ·
      refine ⟨119550223270252886819461939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159400297693670515759282585 119550223270252886819461939)
      ·
        refine ⟨179325334905379330229192909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119550223270252886819461939 179325334905379330229192909)
        ·
          refine ⟨67247000589517248835947341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179325334905379330229192909 67247000589517248835947341)
          ·
            refine ⟨25217625221068968313480253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67247000589517248835947341 25217625221068968313480253)
            ·
              refine ⟨9456609457900863117555095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25217625221068968313480253 9456609457900863117555095)
              ·
                refine ⟨14184914186851294676332643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456609457900863117555095 14184914186851294676332643)
                ·
                  refine ⟨21277371280276942014498965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14184914186851294676332643 21277371280276942014498965)
                  ·
                    refine ⟨997376778762981656929639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21277371280276942014498965 997376778762981656929639)
                    ·
                      rfl

theorem cell23_5827153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_5827153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827153 prefixEnd_5827153 := by exact prefixLift 5827153
  have htrace : WordTrace (prefixWord ++ tailWord_5827153) baseStart_5827153 baseEnd_5827153 := by
    simpa [prefixWord, tailWord_5827153, baseEnd_5827153] using wordTrace_append hprefix tailTrace_5827153
  have hstable : (prefixWord ++ tailWord_5827153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827153).length < 2 ^ (prefixWord ++ tailWord_5827153).sum := by decide
  have hdescent : baseEnd_5827153 < baseStart_5827153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827180 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_5827180 : Nat := 118140960795 + 5827180 * 2 ^ 59
def prefixEnd_5827180 : Nat := 4983230072969 + 3 ^ 40 * 5827180 * 2
def baseEnd_5827180 : Nat := 2992144200266616365151293

theorem tailTrace_5827180 : CollatzResearch.WordTrace tailWord_5827180 prefixEnd_5827180 2992144200266616365151293 := by
  unfold tailWord_5827180
  simp only [CollatzResearch.WordTrace]
  refine ⟨106267357514564768978471497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141689810019419691971295329 106267357514564768978471497)
  ·
    refine ⟨79700518135923576733853623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106267357514564768978471497 79700518135923576733853623)
    ·
      refine ⟨119550777203885365100780435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79700518135923576733853623 119550777203885365100780435)
      ·
        refine ⟨179326165805828047651170653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119550777203885365100780435 179326165805828047651170653)
        ·
          refine ⟨67247312177185517869188995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179326165805828047651170653 67247312177185517869188995)
          ·
            refine ⟨100870968265778276803783493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67247312177185517869188995 100870968265778276803783493)
            ·
              refine ⟨18913306549833426900709405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100870968265778276803783493 18913306549833426900709405)
              ·
                refine ⟨7092489956187535087766027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18913306549833426900709405 7092489956187535087766027)
                ·
                  refine ⟨10638734934281302631649041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092489956187535087766027 10638734934281302631649041)
                  ·
                    refine ⟨7979051200710976973736781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10638734934281302631649041 7979051200710976973736781)
                    ·
                      refine ⟨2992144200266616365151293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979051200710976973736781 2992144200266616365151293)
                      ·
                        rfl

theorem cell23_5827180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_5827180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827180 prefixEnd_5827180 := by exact prefixLift 5827180
  have htrace : WordTrace (prefixWord ++ tailWord_5827180) baseStart_5827180 baseEnd_5827180 := by
    simpa [prefixWord, tailWord_5827180, baseEnd_5827180] using wordTrace_append hprefix tailTrace_5827180
  have hstable : (prefixWord ++ tailWord_5827180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827180).length < 2 ^ (prefixWord ++ tailWord_5827180).sum := by decide
  have hdescent : baseEnd_5827180 < baseStart_5827180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827204 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_5827204 : Nat := 118140960795 + 5827204 * 2 ^ 59
def prefixEnd_5827204 : Nat := 4983230072969 + 3 ^ 40 * 5827204 * 2
def baseEnd_5827204 : Nat := 997385507934108090417061

theorem tailTrace_5827204 : CollatzResearch.WordTrace tailWord_5827204 prefixEnd_5827204 997385507934108090417061 := by
  unfold tailWord_5827204
  simp only [CollatzResearch.WordTrace]
  refine ⟨106267795190521295027908333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141690393587361726703877777 106267795190521295027908333)
  ·
    refine ⟨39850423196445485635465625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106267795190521295027908333 39850423196445485635465625)
    ·
      refine ⟨29887817397334114226599219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39850423196445485635465625 29887817397334114226599219)
      ·
        refine ⟨44831726096001171339898829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29887817397334114226599219 44831726096001171339898829)
        ·
          refine ⟨16811897286000439252462061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44831726096001171339898829 16811897286000439252462061)
          ·
            refine ⟨6304461482250164719673273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16811897286000439252462061 6304461482250164719673273)
            ·
              refine ⟨4728346111687623539754955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6304461482250164719673273 4728346111687623539754955)
              ·
                refine ⟨7092519167531435309632433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728346111687623539754955 7092519167531435309632433)
                ·
                  refine ⟨5319389375648576482224325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7092519167531435309632433 5319389375648576482224325)
                  ·
                    refine ⟨997385507934108090417061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5319389375648576482224325 997385507934108090417061)
                    ·
                      rfl

theorem cell23_5827204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_5827204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827204 prefixEnd_5827204 := by exact prefixLift 5827204
  have htrace : WordTrace (prefixWord ++ tailWord_5827204) baseStart_5827204 baseEnd_5827204 := by
    simpa [prefixWord, tailWord_5827204, baseEnd_5827204] using wordTrace_append hprefix tailTrace_5827204
  have hstable : (prefixWord ++ tailWord_5827204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827204).length < 2 ^ (prefixWord ++ tailWord_5827204).sum := by decide
  have hdescent : baseEnd_5827204 < baseStart_5827204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827216 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_5827216 : Nat := 118140960795 + 5827216 * 2 ^ 59
def prefixEnd_5827216 : Nat := 4983230072969 + 3 ^ 40 * 5827216 * 2
def baseEnd_5827216 : Nat := 2992162685570178224301127

theorem tailTrace_5827216 : CollatzResearch.WordTrace tailWord_5827216 prefixEnd_5827216 2992162685570178224301127 := by
  unfold tailWord_5827216
  simp only [CollatzResearch.WordTrace]
  refine ⟨106268014028499558052626751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141690685371332744070169001 106268014028499558052626751)
  ·
    refine ⟨159402021042749337078940127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106268014028499558052626751 159402021042749337078940127)
    ·
      refine ⟨239103031564124005618410191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159402021042749337078940127 239103031564124005618410191)
      ·
        refine ⟨358654547346186008427615287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239103031564124005618410191 358654547346186008427615287)
        ·
          refine ⟨537981821019279012641422931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358654547346186008427615287 537981821019279012641422931)
          ·
            refine ⟨806972731528918518962134397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537981821019279012641422931 806972731528918518962134397)
            ·
              refine ⟨302614774323344444610800399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 806972731528918518962134397 302614774323344444610800399)
              ·
                refine ⟨453922161485016666916200599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302614774323344444610800399 453922161485016666916200599)
                ·
                  refine ⟨680883242227525000374300899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453922161485016666916200599 680883242227525000374300899)
                  ·
                    refine ⟨1021324863341287500561451349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680883242227525000374300899 1021324863341287500561451349)
                    ·
                      refine ⟨2992162685570178224301127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1021324863341287500561451349 2992162685570178224301127)
                      ·
                        rfl

theorem cell23_5827216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_5827216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827216 prefixEnd_5827216 := by exact prefixLift 5827216
  have htrace : WordTrace (prefixWord ++ tailWord_5827216) baseStart_5827216 baseEnd_5827216 := by
    simpa [prefixWord, tailWord_5827216, baseEnd_5827216] using wordTrace_append hprefix tailTrace_5827216
  have hstable : (prefixWord ++ tailWord_5827216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827216).length < 2 ^ (prefixWord ++ tailWord_5827216).sum := by decide
  have hdescent : baseEnd_5827216 < baseStart_5827216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_5827250 : Nat := 118140960795 + 5827250 * 2 ^ 59
def prefixEnd_5827250 : Nat := 4983230072969 + 3 ^ 40 * 5827250 * 2
def baseEnd_5827250 : Nat := 2992180143912431091275971

theorem tailTrace_5827250 : CollatzResearch.WordTrace tailWord_5827250 prefixEnd_5827250 2992180143912431091275971 := by
  unfold tailWord_5827250
  simp only [CollatzResearch.WordTrace]
  refine ⟨53134317034718984977997801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141691512092583959941327469 53134317034718984977997801)
  ·
    refine ⟨39850737776039238733498351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53134317034718984977997801 39850737776039238733498351)
    ·
      refine ⟨59776106664058858100247527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39850737776039238733498351 59776106664058858100247527)
      ·
        refine ⟨89664159996088287150371291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59776106664058858100247527 89664159996088287150371291)
        ·
          refine ⟨134496239994132430725556937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89664159996088287150371291 134496239994132430725556937)
          ·
            refine ⟨100872179995599323044167703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134496239994132430725556937 100872179995599323044167703)
            ·
              refine ⟨151308269993398984566251555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100872179995599323044167703 151308269993398984566251555)
              ·
                refine ⟨226962404990098476849377333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151308269993398984566251555 226962404990098476849377333)
                ·
                  refine ⟨21277725467821732204629125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226962404990098476849377333 21277725467821732204629125)
                  ·
                    refine ⟨3989573525216574788367961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21277725467821732204629125 3989573525216574788367961)
                    ·
                      refine ⟨2992180143912431091275971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989573525216574788367961 2992180143912431091275971)
                      ·
                        rfl

theorem cell23_5827250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_5827250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827250 prefixEnd_5827250 := by exact prefixLift 5827250
  have htrace : WordTrace (prefixWord ++ tailWord_5827250) baseStart_5827250 baseEnd_5827250 := by
    simpa [prefixWord, tailWord_5827250, baseEnd_5827250] using wordTrace_append hprefix tailTrace_5827250
  have hstable : (prefixWord ++ tailWord_5827250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827250).length < 2 ^ (prefixWord ++ tailWord_5827250).sum := by decide
  have hdescent : baseEnd_5827250 < baseStart_5827250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827263 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_5827263 : Nat := 118140960795 + 5827263 * 2 ^ 59
def prefixEnd_5827263 : Nat := 4983230072969 + 3 ^ 40 * 5827263 * 2
def baseEnd_5827263 : Nat := 2992186819160939540413411

theorem tailTrace_5827263 : CollatzResearch.WordTrace tailWord_5827263 prefixEnd_5827263 2992186819160939540413411 := by
  unfold tailWord_5827263
  simp only [CollatzResearch.WordTrace]
  refine ⟨212537742287828843132214443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141691828191885895421476295 212537742287828843132214443)
  ·
    refine ⟨318806613431743264698321665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212537742287828843132214443 318806613431743264698321665)
    ·
      refine ⟨239104960073807448523741249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318806613431743264698321665 239104960073807448523741249)
      ·
        refine ⟨179328720055355586392805937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239104960073807448523741249 179328720055355586392805937)
        ·
          refine ⟨134496540041516689794604453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179328720055355586392805937 134496540041516689794604453)
          ·
            refine ⟨25218101257784379336488335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134496540041516689794604453 25218101257784379336488335)
            ·
              refine ⟨37827151886676569004732503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25218101257784379336488335 37827151886676569004732503)
              ·
                refine ⟨56740727830014853507098755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37827151886676569004732503 56740727830014853507098755)
                ·
                  refine ⟨85111091745022280260648133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56740727830014853507098755 85111091745022280260648133)
                  ·
                    refine ⟨15958329702191677548871525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85111091745022280260648133 15958329702191677548871525)
                    ·
                      refine ⟨2992186819160939540413411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15958329702191677548871525 2992186819160939540413411)
                      ·
                        rfl

theorem cell23_5827263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_5827263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827263 prefixEnd_5827263 := by exact prefixLift 5827263
  have htrace : WordTrace (prefixWord ++ tailWord_5827263) baseStart_5827263 baseEnd_5827263 := by
    simpa [prefixWord, tailWord_5827263, baseEnd_5827263] using wordTrace_append hprefix tailTrace_5827263
  have hstable : (prefixWord ++ tailWord_5827263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827263).length < 2 ^ (prefixWord ++ tailWord_5827263).sum := by decide
  have hdescent : baseEnd_5827263 < baseStart_5827263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827300 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_5827300 : Nat := 118140960795 + 5827300 * 2 ^ 59
def prefixEnd_5827300 : Nat := 4983230072969 + 3 ^ 40 * 5827300 * 2
def baseEnd_5827300 : Nat := 2992205817945155895650741

theorem tailTrace_5827300 : CollatzResearch.WordTrace tailWord_5827300 prefixEnd_5827300 2992205817945155895650741 := by
  unfold tailWord_5827300
  simp only [CollatzResearch.WordTrace]
  refine ⟨106269545894347399225655677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141692727859129865634207569 106269545894347399225655677)
  ·
    refine ⟨39851079710380274709620879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106269545894347399225655677 39851079710380274709620879)
    ·
      refine ⟨59776619565570412064431319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39851079710380274709620879 59776619565570412064431319)
      ·
        refine ⟨89664929348355618096646979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59776619565570412064431319 89664929348355618096646979)
        ·
          refine ⟨134497394022533427144970469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89664929348355618096646979 134497394022533427144970469)
          ·
            refine ⟨25218261379225017589681963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134497394022533427144970469 25218261379225017589681963)
            ·
              refine ⟨37827392068837526384522945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25218261379225017589681963 37827392068837526384522945)
              ·
                refine ⟨28370544051628144788392209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37827392068837526384522945 28370544051628144788392209)
                ·
                  refine ⟨21277908038721108591294157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28370544051628144788392209 21277908038721108591294157)
                  ·
                    refine ⟨7979215514520415721735309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21277908038721108591294157 7979215514520415721735309)
                    ·
                      refine ⟨2992205817945155895650741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979215514520415721735309 2992205817945155895650741)
                      ·
                        rfl

theorem cell23_5827300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_5827300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827300 prefixEnd_5827300 := by exact prefixLift 5827300
  have htrace : WordTrace (prefixWord ++ tailWord_5827300) baseStart_5827300 baseEnd_5827300 := by
    simpa [prefixWord, tailWord_5827300, baseEnd_5827300] using wordTrace_append hprefix tailTrace_5827300
  have hstable : (prefixWord ++ tailWord_5827300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827300).length < 2 ^ (prefixWord ++ tailWord_5827300).sum := by decide
  have hdescent : baseEnd_5827300 < baseStart_5827300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827301 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5827301 : Nat := 118140960795 + 5827301 * 2 ^ 59
def prefixEnd_5827301 : Nat := 4983230072969 + 3 ^ 40 * 5827301 * 2
def baseEnd_5827301 : Nat := 2992206331425810391738237

theorem tailTrace_5827301 : CollatzResearch.WordTrace tailWord_5827301 prefixEnd_5827301 2992206331425810391738237 := by
  unfold tailWord_5827301
  simp only [CollatzResearch.WordTrace]
  refine ⟨212539128261691175622097757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141692752174460783748065171 212539128261691175622097757)
  ·
    refine ⟨79702173098134190858286659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212539128261691175622097757 79702173098134190858286659)
    ·
      refine ⟨119553259647201286287429989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79702173098134190858286659 119553259647201286287429989)
      ·
        refine ⟨22416236183850241178893123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119553259647201286287429989 22416236183850241178893123)
        ·
          refine ⟨33624354275775361768339685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22416236183850241178893123 33624354275775361768339685)
          ·
            refine ⟨6304566426707880331563691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33624354275775361768339685 6304566426707880331563691)
            ·
              refine ⟨9456849640061820497345537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304566426707880331563691 9456849640061820497345537)
              ·
                refine ⟨7092637230046365373009153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9456849640061820497345537 7092637230046365373009153)
                ·
                  refine ⟨5319477922534774029756865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7092637230046365373009153 5319477922534774029756865)
                  ·
                    refine ⟨3989608441901080522317649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5319477922534774029756865 3989608441901080522317649)
                    ·
                      refine ⟨2992206331425810391738237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989608441901080522317649 2992206331425810391738237)
                      ·
                        rfl

theorem cell23_5827301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5827301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827301 prefixEnd_5827301 := by exact prefixLift 5827301
  have htrace : WordTrace (prefixWord ++ tailWord_5827301) baseStart_5827301 baseEnd_5827301 := by
    simpa [prefixWord, tailWord_5827301, baseEnd_5827301] using wordTrace_append hprefix tailTrace_5827301
  have hstable : (prefixWord ++ tailWord_5827301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827301).length < 2 ^ (prefixWord ++ tailWord_5827301).sum := by decide
  have hdescent : baseEnd_5827301 < baseStart_5827301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827313 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_5827313 : Nat := 118140960795 + 5827313 * 2 ^ 59
def prefixEnd_5827313 : Nat := 4983230072969 + 3 ^ 40 * 5827313 * 2
def baseEnd_5827313 : Nat := 2992212493193664344788181

theorem tailTrace_5827313 : CollatzResearch.WordTrace tailWord_5827313 prefixEnd_5827313 2992212493193664344788181 := by
  unfold tailWord_5827313
  simp only [CollatzResearch.WordTrace]
  refine ⟨212539565937647701671534593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141693043958431801114356395 212539565937647701671534593)
  ·
    refine ⟨159404674453235776253650945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212539565937647701671534593 159404674453235776253650945)
    ·
      refine ⟨119553505839926832190238209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159404674453235776253650945 119553505839926832190238209)
      ·
        refine ⟨89665129379945124142678657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119553505839926832190238209 89665129379945124142678657)
        ·
          refine ⟨67248847034958843107008993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89665129379945124142678657 67248847034958843107008993)
          ·
            refine ⟨50436635276219132330256745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67248847034958843107008993 50436635276219132330256745)
            ·
              refine ⟨37827476457164349247692559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50436635276219132330256745 37827476457164349247692559)
              ·
                refine ⟨56741214685746523871538839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37827476457164349247692559 56741214685746523871538839)
                ·
                  refine ⟨85111822028619785807308259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56741214685746523871538839 85111822028619785807308259)
                  ·
                    refine ⟨127667733042929678710962389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85111822028619785807308259 127667733042929678710962389)
                    ·
                      refine ⟨2992212493193664344788181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127667733042929678710962389 2992212493193664344788181)
                      ·
                        rfl

theorem cell23_5827313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_5827313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827313 prefixEnd_5827313 := by exact prefixLift 5827313
  have htrace : WordTrace (prefixWord ++ tailWord_5827313) baseStart_5827313 baseEnd_5827313 := by
    simpa [prefixWord, tailWord_5827313, baseEnd_5827313] using wordTrace_append hprefix tailTrace_5827313
  have hstable : (prefixWord ++ tailWord_5827313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827313).length < 2 ^ (prefixWord ++ tailWord_5827313).sum := by decide
  have hdescent : baseEnd_5827313 < baseStart_5827313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827340 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5827340 : Nat := 118140960795 + 5827340 * 2 ^ 59
def prefixEnd_5827340 : Nat := 4983230072969 + 3 ^ 40 * 5827340 * 2
def baseEnd_5827340 : Nat := 2992226357171335739150557

theorem tailTrace_5827340 : CollatzResearch.WordTrace tailWord_5827340 prefixEnd_5827340 2992226357171335739150557 := by
  unfold tailWord_5827340
  simp only [CollatzResearch.WordTrace]
  refine ⟨106270275354274942641383737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141693700472366590188511649 106270275354274942641383737)
  ·
    refine ⟨79702706515706206981037803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106270275354274942641383737 79702706515706206981037803)
    ·
      refine ⟨119554059773559310471556705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79702706515706206981037803 119554059773559310471556705)
      ·
        refine ⟨89665544830169482853667529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119554059773559310471556705 89665544830169482853667529)
        ·
          refine ⟨67249158622627112140250647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89665544830169482853667529 67249158622627112140250647)
          ·
            refine ⟨100873737933940668210375971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67249158622627112140250647 100873737933940668210375971)
            ·
              refine ⟨151310606900911002315563957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100873737933940668210375971 151310606900911002315563957)
              ·
                refine ⟨14185369396960406467084121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151310606900911002315563957 14185369396960406467084121)
                ·
                  refine ⟨10639027047720304850313091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14185369396960406467084121 10639027047720304850313091)
                  ·
                    refine ⟨15958540571580457275469637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10639027047720304850313091 15958540571580457275469637)
                    ·
                      refine ⟨2992226357171335739150557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15958540571580457275469637 2992226357171335739150557)
                      ·
                        rfl

theorem cell23_5827340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5827340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827340 prefixEnd_5827340 := by exact prefixLift 5827340
  have htrace : WordTrace (prefixWord ++ tailWord_5827340) baseStart_5827340 baseEnd_5827340 := by
    simpa [prefixWord, tailWord_5827340, baseEnd_5827340] using wordTrace_append hprefix tailTrace_5827340
  have hstable : (prefixWord ++ tailWord_5827340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827340).length < 2 ^ (prefixWord ++ tailWord_5827340).sum := by decide
  have hdescent : baseEnd_5827340 < baseStart_5827340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827353 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5827353 : Nat := 118140960795 + 5827353 * 2 ^ 59
def prefixEnd_5827353 : Nat := 4983230072969 + 3 ^ 40 * 5827353 * 2
def baseEnd_5827353 : Nat := 2992233032419844188287997

theorem tailTrace_5827353 : CollatzResearch.WordTrace tailWord_5827353 prefixEnd_5827353 2992233032419844188287997 := by
  unfold tailWord_5827353
  simp only [CollatzResearch.WordTrace]
  refine ⟨212541024857502788502990713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141694016571668525668660475 212541024857502788502990713)
  ·
    refine ⟨159405768643127091377243035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212541024857502788502990713 159405768643127091377243035)
    ·
      refine ⟨239108652964690637065864553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159405768643127091377243035 239108652964690637065864553)
      ·
        refine ⟨179331489723517977799398415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239108652964690637065864553 179331489723517977799398415)
        ·
          refine ⟨268997234585276966699097623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179331489723517977799398415 268997234585276966699097623)
          ·
            refine ⟨403495851877915450048646435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268997234585276966699097623 403495851877915450048646435)
            ·
              refine ⟨605243777816873175072969653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403495851877915450048646435 605243777816873175072969653)
              ·
                refine ⟨56741604170331860163090905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 605243777816873175072969653 56741604170331860163090905)
                ·
                  refine ⟨42556203127748895122318179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56741604170331860163090905 42556203127748895122318179)
                  ·
                    refine ⟨63834304691623342683477269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42556203127748895122318179 63834304691623342683477269)
                    ·
                      refine ⟨2992233032419844188287997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63834304691623342683477269 2992233032419844188287997)
                      ·
                        rfl

theorem cell23_5827353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5827353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827353 prefixEnd_5827353 := by exact prefixLift 5827353
  have htrace : WordTrace (prefixWord ++ tailWord_5827353) baseStart_5827353 baseEnd_5827353 := by
    simpa [prefixWord, tailWord_5827353, baseEnd_5827353] using wordTrace_append hprefix tailTrace_5827353
  have hstable : (prefixWord ++ tailWord_5827353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827353).length < 2 ^ (prefixWord ++ tailWord_5827353).sum := by decide
  have hdescent : baseEnd_5827353 < baseStart_5827353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827403 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_5827403 : Nat := 118140960795 + 5827403 * 2 ^ 59
def prefixEnd_5827403 : Nat := 4983230072969 + 3 ^ 40 * 5827403 * 2
def baseEnd_5827403 : Nat := 2992258706452568992662767

theorem tailTrace_5827403 : CollatzResearch.WordTrace tailWord_5827403 prefixEnd_5827403 2992258706452568992662767 := by
  unfold tailWord_5827403
  simp only [CollatzResearch.WordTrace]
  refine ⟨212542848507321647042310863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141695232338214431361540575 212542848507321647042310863)
  ·
    refine ⟨318814272760982470563466295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212542848507321647042310863 318814272760982470563466295)
    ·
      refine ⟨478221409141473705845199443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318814272760982470563466295 478221409141473705845199443)
      ·
        refine ⟨717332113712210558767799165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478221409141473705845199443 717332113712210558767799165)
        ·
          refine ⟨268999542642078959537924687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 717332113712210558767799165 268999542642078959537924687)
          ·
            refine ⟨403499313963118439306887031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268999542642078959537924687 403499313963118439306887031)
            ·
              refine ⟨605248970944677658960330547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403499313963118439306887031 605248970944677658960330547)
              ·
                refine ⟨907873456417016488440495821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605248970944677658960330547 907873456417016488440495821)
                ·
                  refine ⟨340452546156381183165185933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907873456417016488440495821 340452546156381183165185933)
                  ·
                    refine ⟨127669704808642943686944725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340452546156381183165185933 127669704808642943686944725)
                    ·
                      refine ⟨2992258706452568992662767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127669704808642943686944725 2992258706452568992662767)
                      ·
                        rfl

theorem cell23_5827403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_5827403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827403 prefixEnd_5827403 := by exact prefixLift 5827403
  have htrace : WordTrace (prefixWord ++ tailWord_5827403) baseStart_5827403 baseEnd_5827403 := by
    simpa [prefixWord, tailWord_5827403, baseEnd_5827403] using wordTrace_append hprefix tailTrace_5827403
  have hstable : (prefixWord ++ tailWord_5827403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827403).length < 2 ^ (prefixWord ++ tailWord_5827403).sum := by decide
  have hdescent : baseEnd_5827403 < baseStart_5827403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827440 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_5827440 : Nat := 118140960795 + 5827440 * 2 ^ 59
def prefixEnd_5827440 : Nat := 4983230072969 + 3 ^ 40 * 5827440 * 2
def baseEnd_5827440 : Nat := 997425901745595115966699

theorem tailTrace_5827440 : CollatzResearch.WordTrace tailWord_5827440 prefixEnd_5827440 997425901745595115966699 := by
  unfold tailWord_5827440
  simp only [CollatzResearch.WordTrace]
  refine ⟨106272099004093801180703887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141696132005458401574271849 106272099004093801180703887)
  ·
    refine ⟨159408148506140701771055831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106272099004093801180703887 159408148506140701771055831)
    ·
      refine ⟨239112222759211052656583747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159408148506140701771055831 239112222759211052656583747)
      ·
        refine ⟨358668334138816578984875621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239112222759211052656583747 358668334138816578984875621)
        ·
          refine ⟨67250312651028108559664179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358668334138816578984875621 67250312651028108559664179)
          ·
            refine ⟨100875468976542162839496269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67250312651028108559664179 100875468976542162839496269)
            ·
              refine ⟨37828300866203311064811101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100875468976542162839496269 37828300866203311064811101)
              ·
                refine ⟨14185612824826241649304163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37828300866203311064811101 14185612824826241649304163)
                ·
                  refine ⟨21278419237239362473956245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14185612824826241649304163 21278419237239362473956245)
                  ·
                    refine ⟨997425901745595115966699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21278419237239362473956245 997425901745595115966699)
                    ·
                      rfl

theorem cell23_5827440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_5827440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827440 prefixEnd_5827440 := by exact prefixLift 5827440
  have htrace : WordTrace (prefixWord ++ tailWord_5827440) baseStart_5827440 baseEnd_5827440 := by
    simpa [prefixWord, tailWord_5827440, baseEnd_5827440] using wordTrace_append hprefix tailTrace_5827440
  have hstable : (prefixWord ++ tailWord_5827440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827440).length < 2 ^ (prefixWord ++ tailWord_5827440).sum := by decide
  have hdescent : baseEnd_5827440 < baseStart_5827440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827460 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5827460 : Nat := 118140960795 + 5827460 * 2 ^ 59
def prefixEnd_5827460 : Nat := 4983230072969 + 3 ^ 40 * 5827460 * 2
def baseEnd_5827460 : Nat := 2992287974849875269650005

theorem tailTrace_5827460 : CollatzResearch.WordTrace tailWord_5827460 prefixEnd_5827460 2992287974849875269650005 := by
  unfold tailWord_5827460
  simp only [CollatzResearch.WordTrace]
  refine ⟨106272463734057572888567917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141696618312076763851423889 106272463734057572888567917)
  ·
    refine ⟨39852173900271589833212969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106272463734057572888567917 39852173900271589833212969)
    ·
      refine ⟨29889130425203692374909727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39852173900271589833212969 29889130425203692374909727)
      ·
        refine ⟨44833695637805538562364591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29889130425203692374909727 44833695637805538562364591)
        ·
          refine ⟨67250543456708307843546887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44833695637805538562364591 67250543456708307843546887)
          ·
            refine ⟨100875815185062461765320331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67250543456708307843546887 100875815185062461765320331)
            ·
              refine ⟨151313722777593692647980497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100875815185062461765320331 151313722777593692647980497)
              ·
                refine ⟨113485292083195269485985373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151313722777593692647980497 113485292083195269485985373)
                ·
                  refine ⟨42556984531198226057244515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113485292083195269485985373 42556984531198226057244515)
                  ·
                    refine ⟨63835476796797339085866773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42556984531198226057244515 63835476796797339085866773)
                    ·
                      refine ⟨2992287974849875269650005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63835476796797339085866773 2992287974849875269650005)
                      ·
                        rfl

theorem cell23_5827460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5827460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827460 prefixEnd_5827460 := by exact prefixLift 5827460
  have htrace : WordTrace (prefixWord ++ tailWord_5827460) baseStart_5827460 baseEnd_5827460 := by
    simpa [prefixWord, tailWord_5827460, baseEnd_5827460] using wordTrace_append hprefix tailTrace_5827460
  have hstable : (prefixWord ++ tailWord_5827460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827460).length < 2 ^ (prefixWord ++ tailWord_5827460).sum := by decide
  have hdescent : baseEnd_5827460 < baseStart_5827460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827464 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5827464 : Nat := 118140960795 + 5827464 * 2 ^ 59
def prefixEnd_5827464 : Nat := 4983230072969 + 3 ^ 40 * 5827464 * 2
def baseEnd_5827464 : Nat := 2992290028772493253999987

theorem tailTrace_5827464 : CollatzResearch.WordTrace tailWord_5827464 prefixEnd_5827464 2992290028772493253999987 := by
  unfold tailWord_5827464
  simp only [CollatzResearch.WordTrace]
  refine ⟨106272536680050327230140723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141696715573400436306854297 106272536680050327230140723)
  ·
    refine ⟨159408805020075490845211085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106272536680050327230140723 159408805020075490845211085)
    ·
      refine ⟨59778301882528309066954157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159408805020075490845211085 59778301882528309066954157)
      ·
        refine ⟨22416863205948115900107809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59778301882528309066954157 22416863205948115900107809)
        ·
          refine ⟨16812647404461086925080857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22416863205948115900107809 16812647404461086925080857)
          ·
            refine ⟨12609485553345815193810643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16812647404461086925080857 12609485553345815193810643)
            ·
              refine ⟨18914228330018722790715965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12609485553345815193810643 18914228330018722790715965)
              ·
                refine ⟨7092835623757021046518487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18914228330018722790715965 7092835623757021046518487)
                ·
                  refine ⟨10639253435635531569777731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7092835623757021046518487 10639253435635531569777731)
                  ·
                    refine ⟨15958880153453297354666597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10639253435635531569777731 15958880153453297354666597)
                    ·
                      refine ⟨2992290028772493253999987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15958880153453297354666597 2992290028772493253999987)
                      ·
                        rfl

theorem cell23_5827464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5827464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827464 prefixEnd_5827464 := by exact prefixLift 5827464
  have htrace : WordTrace (prefixWord ++ tailWord_5827464) baseStart_5827464 baseEnd_5827464 := by
    simpa [prefixWord, tailWord_5827464, baseEnd_5827464] using wordTrace_append hprefix tailTrace_5827464
  have hstable : (prefixWord ++ tailWord_5827464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827464).length < 2 ^ (prefixWord ++ tailWord_5827464).sum := by decide
  have hdescent : baseEnd_5827464 < baseStart_5827464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827484 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5827484 : Nat := 118140960795 + 5827484 * 2 ^ 59
def prefixEnd_5827484 : Nat := 4983230072969 + 3 ^ 40 * 5827484 * 2
def baseEnd_5827484 : Nat := 2992300298385583175749895

theorem tailTrace_5827484 : CollatzResearch.WordTrace tailWord_5827484 prefixEnd_5827484 2992300298385583175749895 := by
  unfold tailWord_5827484
  simp only [CollatzResearch.WordTrace]
  refine ⟨106272901410014098938004753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141697201880018798584006337 106272901410014098938004753)
  ·
    refine ⟨79704676057510574203503565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106272901410014098938004753 79704676057510574203503565)
    ·
      refine ⟨29889253521566465326313837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79704676057510574203503565 29889253521566465326313837)
      ·
        refine ⟨11208470070587424497367689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29889253521566465326313837 11208470070587424497367689)
        ·
          refine ⟨8406352552940568373025767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11208470070587424497367689 8406352552940568373025767)
          ·
            refine ⟨12609528829410852559538651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8406352552940568373025767 12609528829410852559538651)
            ·
              refine ⟨18914293244116278839307977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12609528829410852559538651 18914293244116278839307977)
              ·
                refine ⟨14185719933087209129480983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18914293244116278839307977 14185719933087209129480983)
                ·
                  refine ⟨21278579899630813694221475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14185719933087209129480983 21278579899630813694221475)
                  ·
                    refine ⟨31917869849446220541332213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21278579899630813694221475 31917869849446220541332213)
                    ·
                      refine ⟨2992300298385583175749895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31917869849446220541332213 2992300298385583175749895)
                      ·
                        rfl

theorem cell23_5827484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5827484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827484 prefixEnd_5827484 := by exact prefixLift 5827484
  have htrace : WordTrace (prefixWord ++ tailWord_5827484) baseStart_5827484 baseEnd_5827484 := by
    simpa [prefixWord, tailWord_5827484, baseEnd_5827484] using wordTrace_append hprefix tailTrace_5827484
  have hstable : (prefixWord ++ tailWord_5827484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827484).length < 2 ^ (prefixWord ++ tailWord_5827484).sum := by decide
  have hdescent : baseEnd_5827484 < baseStart_5827484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827526 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5827526 : Nat := 118140960795 + 5827526 * 2 ^ 59
def prefixEnd_5827526 : Nat := 4983230072969 + 3 ^ 40 * 5827526 * 2
def baseEnd_5827526 : Nat := 2992321864573072011424703

theorem tailTrace_5827526 : CollatzResearch.WordTrace tailWord_5827526 prefixEnd_5827526 2992321864573072011424703 := by
  unfold tailWord_5827526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642104208933626220282451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141698223123917359366025621 6642104208933626220282451)
  ·
    refine ⟨9963156313400439330423677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6642104208933626220282451 9963156313400439330423677)
    ·
      refine ⟨3736183617525164748908879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9963156313400439330423677 3736183617525164748908879)
      ·
        refine ⟨5604275426287747123363319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736183617525164748908879 5604275426287747123363319)
        ·
          refine ⟨8406413139431620685044979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604275426287747123363319 8406413139431620685044979)
          ·
            refine ⟨12609619709147431027567469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8406413139431620685044979 12609619709147431027567469)
            ·
              refine ⟨4728607390930286635337801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12609619709147431027567469 4728607390930286635337801)
              ·
                refine ⟨3546455543197714976503351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728607390930286635337801 3546455543197714976503351)
                ·
                  refine ⟨5319683314796572464755027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546455543197714976503351 5319683314796572464755027)
                  ·
                    refine ⟨7979524972194858697132541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319683314796572464755027 7979524972194858697132541)
                    ·
                      refine ⟨2992321864573072011424703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979524972194858697132541 2992321864573072011424703)
                      ·
                        rfl

theorem cell23_5827526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5827526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827526 prefixEnd_5827526 := by exact prefixLift 5827526
  have htrace : WordTrace (prefixWord ++ tailWord_5827526) baseStart_5827526 baseEnd_5827526 := by
    simpa [prefixWord, tailWord_5827526, baseEnd_5827526] using wordTrace_append hprefix tailTrace_5827526
  have hstable : (prefixWord ++ tailWord_5827526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827526).length < 2 ^ (prefixWord ++ tailWord_5827526).sum := by decide
  have hdescent : baseEnd_5827526 < baseStart_5827526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827574 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5827574 : Nat := 118140960795 + 5827574 * 2 ^ 59
def prefixEnd_5827574 : Nat := 4983230072969 + 3 ^ 40 * 5827574 * 2
def baseEnd_5827574 : Nat := 2992346511644487823624481

theorem tailTrace_5827574 : CollatzResearch.WordTrace tailWord_5827574 prefixEnd_5827574 2992346511644487823624481 := by
  unfold tailWord_5827574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284317836856383952924111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141699390259801428831190517 13284317836856383952924111)
  ·
    refine ⟨19926476755284575929386167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13284317836856383952924111 19926476755284575929386167)
    ·
      refine ⟨29889715132926863894079251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19926476755284575929386167 29889715132926863894079251)
      ·
        refine ⟨44834572699390295841118877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29889715132926863894079251 44834572699390295841118877)
        ·
          refine ⟨16812964762271360940419579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44834572699390295841118877 16812964762271360940419579)
          ·
            refine ⟨25219447143407041410629369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16812964762271360940419579 25219447143407041410629369)
            ·
              refine ⟨18914585357555281057972027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25219447143407041410629369 18914585357555281057972027)
              ·
                refine ⟨28371878036332921586958041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18914585357555281057972027 28371878036332921586958041)
                ·
                  refine ⟨21278908527249691190218531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28371878036332921586958041 21278908527249691190218531)
                  ·
                    refine ⟨31918362790874536785327797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21278908527249691190218531 31918362790874536785327797)
                    ·
                      refine ⟨2992346511644487823624481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31918362790874536785327797 2992346511644487823624481)
                      ·
                        rfl

theorem cell23_5827574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5827574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827574 prefixEnd_5827574 := by exact prefixLift 5827574
  have htrace : WordTrace (prefixWord ++ tailWord_5827574) baseStart_5827574 baseEnd_5827574 := by
    simpa [prefixWord, tailWord_5827574, baseEnd_5827574] using wordTrace_append hprefix tailTrace_5827574
  have hstable : (prefixWord ++ tailWord_5827574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827574).length < 2 ^ (prefixWord ++ tailWord_5827574).sum := by decide
  have hdescent : baseEnd_5827574 < baseStart_5827574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827627 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_5827627 : Nat := 118140960795 + 5827627 * 2 ^ 59
def prefixEnd_5827627 : Nat := 4983230072969 + 3 ^ 40 * 5827627 * 2
def baseEnd_5827627 : Nat := 2992373726119176116261737

theorem tailTrace_5827627 : CollatzResearch.WordTrace tailWord_5827627 prefixEnd_5827627 2992373726119176116261737 := by
  unfold tailWord_5827627
  simp only [CollatzResearch.WordTrace]
  refine ⟨212551018458510133298465135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141700678972340088865643423 212551018458510133298465135)
  ·
    refine ⟨318826527687765199947697703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212551018458510133298465135 318826527687765199947697703)
    ·
      refine ⟨478239791531647799921546555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318826527687765199947697703 478239791531647799921546555)
      ·
        refine ⟨717359687297471699882319833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478239791531647799921546555 717359687297471699882319833)
        ·
          refine ⟨538019765473103774911739875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717359687297471699882319833 538019765473103774911739875)
          ·
            refine ⟨807029648209655662367609813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538019765473103774911739875 807029648209655662367609813)
            ·
              refine ⟨18914757379913804586740855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 807029648209655662367609813 18914757379913804586740855)
              ·
                refine ⟨28372136069870706880111283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18914757379913804586740855 28372136069870706880111283)
                ·
                  refine ⟨42558204104806060320166925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28372136069870706880111283 42558204104806060320166925)
                  ·
                    refine ⟨15959326539302272620062597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42558204104806060320166925 15959326539302272620062597)
                    ·
                      refine ⟨2992373726119176116261737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15959326539302272620062597 2992373726119176116261737)
                      ·
                        rfl

theorem cell23_5827627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_5827627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827627 prefixEnd_5827627 := by exact prefixLift 5827627
  have htrace : WordTrace (prefixWord ++ tailWord_5827627) baseStart_5827627 baseEnd_5827627 := by
    simpa [prefixWord, tailWord_5827627, baseEnd_5827627] using wordTrace_append hprefix tailTrace_5827627
  have hstable : (prefixWord ++ tailWord_5827627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827627).length < 2 ^ (prefixWord ++ tailWord_5827627).sum := by decide
  have hdescent : baseEnd_5827627 < baseStart_5827627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827678 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5827678 : Nat := 118140960795 + 5827678 * 2 ^ 59
def prefixEnd_5827678 : Nat := 4983230072969 + 3 ^ 40 * 5827678 * 2
def baseEnd_5827678 : Nat := 2992399913632555416724003

theorem tailTrace_5827678 : CollatzResearch.WordTrace tailWord_5827678 prefixEnd_5827678 2992399913632555416724003 := by
  unfold tailWord_5827678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26569109822665671126071461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141701919054216912672381125 26569109822665671126071461)
  ·
    refine ⟨4981708091749813336138399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26569109822665671126071461 4981708091749813336138399)
    ·
      refine ⟨7472562137624720004207599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981708091749813336138399 7472562137624720004207599)
      ·
        refine ⟨11208843206437080006311399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7472562137624720004207599 11208843206437080006311399)
        ·
          refine ⟨16813264809655620009467099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11208843206437080006311399 16813264809655620009467099)
          ·
            refine ⟨25219897214483430014200649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16813264809655620009467099 25219897214483430014200649)
            ·
              refine ⟨18914922910862572510650487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25219897214483430014200649 18914922910862572510650487)
              ·
                refine ⟨28372384366293858765975731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18914922910862572510650487 28372384366293858765975731)
                ·
                  refine ⟨42558576549440788148963597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28372384366293858765975731 42558576549440788148963597)
                  ·
                    refine ⟨15959466206040295555861349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42558576549440788148963597 15959466206040295555861349)
                    ·
                      refine ⟨2992399913632555416724003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15959466206040295555861349 2992399913632555416724003)
                      ·
                        rfl

theorem cell23_5827678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5827678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827678 prefixEnd_5827678 := by exact prefixLift 5827678
  have htrace : WordTrace (prefixWord ++ tailWord_5827678) baseStart_5827678 baseEnd_5827678 := by
    simpa [prefixWord, tailWord_5827678, baseEnd_5827678] using wordTrace_append hprefix tailTrace_5827678
  have hstable : (prefixWord ++ tailWord_5827678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827678).length < 2 ^ (prefixWord ++ tailWord_5827678).sum := by decide
  have hdescent : baseEnd_5827678 < baseStart_5827678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827705 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 1, 4]
def baseStart_5827705 : Nat := 118140960795 + 5827705 * 2 ^ 59
def prefixEnd_5827705 : Nat := 4983230072969 + 3 ^ 40 * 5827705 * 2
def baseEnd_5827705 : Nat := 997471259203408937028793

theorem tailTrace_5827705 : CollatzResearch.WordTrace tailWord_5827705 prefixEnd_5827705 997471259203408937028793 := by
  unfold tailWord_5827705
  simp only [CollatzResearch.WordTrace]
  refine ⟨212553863352227552619804569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141702575568151701746536379 212553863352227552619804569)
  ·
    refine ⟨159415397514170664464853427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212553863352227552619804569 159415397514170664464853427)
    ·
      refine ⟨239123096271255996697280141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159415397514170664464853427 239123096271255996697280141)
      ·
        refine ⟨89671161101720998761480053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239123096271255996697280141 89671161101720998761480053)
        ·
          refine ⟨8406671353286343633888755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89671161101720998761480053 8406671353286343633888755)
          ·
            refine ⟨12610007029929515450833133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8406671353286343633888755 12610007029929515450833133)
            ·
              refine ⟨4728752636223568294062425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12610007029929515450833133 4728752636223568294062425)
              ·
                refine ⟨3546564477167676220546819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728752636223568294062425 3546564477167676220546819)
                ·
                  refine ⟨5319846715751514330820229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546564477167676220546819 5319846715751514330820229)
                  ·
                    refine ⟨997471259203408937028793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5319846715751514330820229 997471259203408937028793)
                    ·
                      rfl

theorem cell23_5827705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 4].length) (baseStart_5827705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827705 prefixEnd_5827705 := by exact prefixLift 5827705
  have htrace : WordTrace (prefixWord ++ tailWord_5827705) baseStart_5827705 baseEnd_5827705 := by
    simpa [prefixWord, tailWord_5827705, baseEnd_5827705] using wordTrace_append hprefix tailTrace_5827705
  have hstable : (prefixWord ++ tailWord_5827705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827705).length < 2 ^ (prefixWord ++ tailWord_5827705).sum := by decide
  have hdescent : baseEnd_5827705 < baseStart_5827705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827737 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5827737 : Nat := 118140960795 + 5827737 * 2 ^ 59
def prefixEnd_5827737 : Nat := 4983230072969 + 3 ^ 40 * 5827737 * 2
def baseEnd_5827737 : Nat := 2992430208991170685886231

theorem tailTrace_5827737 : CollatzResearch.WordTrace tailWord_5827737 prefixEnd_5827737 2992430208991170685886231 := by
  unfold tailWord_5827737
  simp only [CollatzResearch.WordTrace]
  refine ⟨212555030488111622084969465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141703353658741081389979643 212555030488111622084969465)
  ·
    refine ⟨159416272866083716563727099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212555030488111622084969465 159416272866083716563727099)
    ·
      refine ⟨239124409299125574845590649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159416272866083716563727099 239124409299125574845590649)
      ·
        refine ⟨179343306974344181134192987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239124409299125574845590649 179343306974344181134192987)
        ·
          refine ⟨269014960461516271701289481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179343306974344181134192987 269014960461516271701289481)
          ·
            refine ⟨201761220346137203775967111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269014960461516271701289481 201761220346137203775967111)
            ·
              refine ⟨302641830519205805663950667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201761220346137203775967111 302641830519205805663950667)
              ·
                refine ⟨453962745778808708495926001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302641830519205805663950667 453962745778808708495926001)
                ·
                  refine ⟨340472059334106531371944501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453962745778808708495926001 340472059334106531371944501)
                  ·
                    refine ⟨31919255562572487316119797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 340472059334106531371944501 31919255562572487316119797)
                    ·
                      refine ⟨2992430208991170685886231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31919255562572487316119797 2992430208991170685886231)
                      ·
                        rfl

theorem cell23_5827737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5827737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827737 prefixEnd_5827737 := by exact prefixLift 5827737
  have htrace : WordTrace (prefixWord ++ tailWord_5827737) baseStart_5827737 baseEnd_5827737 := by
    simpa [prefixWord, tailWord_5827737, baseEnd_5827737] using wordTrace_append hprefix tailTrace_5827737
  have hstable : (prefixWord ++ tailWord_5827737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827737).length < 2 ^ (prefixWord ++ tailWord_5827737).sum := by decide
  have hdescent : baseEnd_5827737 < baseStart_5827737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827738 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5827738 : Nat := 118140960795 + 5827738 * 2 ^ 59
def prefixEnd_5827738 : Nat := 4983230072969 + 3 ^ 40 * 5827738 * 2
def baseEnd_5827738 : Nat := 2992430722471825181973727

theorem tailTrace_5827738 : CollatzResearch.WordTrace tailWord_5827738 prefixEnd_5827738 2992430722471825181973727 := by
  unfold tailWord_5827738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53138766740276999813938967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141703377974071999503837245 53138766740276999813938967)
  ·
    refine ⟨79708150110415499720908451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53138766740276999813938967 79708150110415499720908451)
    ·
      refine ⟨119562225165623249581362677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79708150110415499720908451 119562225165623249581362677)
      ·
        refine ⟨11208958609277179648252751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119562225165623249581362677 11208958609277179648252751)
        ·
          refine ⟨16813437913915769472379127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11208958609277179648252751 16813437913915769472379127)
          ·
            refine ⟨25220156870873654208568691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16813437913915769472379127 25220156870873654208568691)
            ·
              refine ⟨37830235306310481312853037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25220156870873654208568691 37830235306310481312853037)
              ·
                refine ⟨14186338239866430492319889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37830235306310481312853037 14186338239866430492319889)
                ·
                  refine ⟨10639753679899822869239917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14186338239866430492319889 10639753679899822869239917)
                  ·
                    refine ⟨3989907629962433575964969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10639753679899822869239917 3989907629962433575964969)
                    ·
                      refine ⟨2992430722471825181973727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989907629962433575964969 2992430722471825181973727)
                      ·
                        rfl

theorem cell23_5827738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5827738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827738 prefixEnd_5827738 := by exact prefixLift 5827738
  have htrace : WordTrace (prefixWord ++ tailWord_5827738) baseStart_5827738 baseEnd_5827738 := by
    simpa [prefixWord, tailWord_5827738, baseEnd_5827738] using wordTrace_append hprefix tailTrace_5827738
  have hstable : (prefixWord ++ tailWord_5827738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827738).length < 2 ^ (prefixWord ++ tailWord_5827738).sum := by decide
  have hdescent : baseEnd_5827738 < baseStart_5827738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827744 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_5827744 : Nat := 118140960795 + 5827744 * 2 ^ 59
def prefixEnd_5827744 : Nat := 4983230072969 + 3 ^ 40 * 5827744 * 2
def baseEnd_5827744 : Nat := 997477934451917386166233

theorem tailTrace_5827744 : CollatzResearch.WordTrace tailWord_5827744 prefixEnd_5827744 997477934451917386166233 := by
  unfold tailWord_5827744
  simp only [CollatzResearch.WordTrace]
  refine ⟨106277642899543131140237143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141703523866057508186982857 106277642899543131140237143)
  ·
    refine ⟨159416464349314696710355715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106277642899543131140237143 159416464349314696710355715)
    ·
      refine ⟨239124696523972045065533573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159416464349314696710355715 239124696523972045065533573)
      ·
        refine ⟨44835880598244758449787545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239124696523972045065533573 44835880598244758449787545)
        ·
          refine ⟨33626910448683568837340659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44835880598244758449787545 33626910448683568837340659)
          ·
            refine ⟨50440365673025353256010989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33626910448683568837340659 50440365673025353256010989)
            ·
              refine ⟨18915137127384507471004121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50440365673025353256010989 18915137127384507471004121)
              ·
                refine ⟨14186352845538380603253091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18915137127384507471004121 14186352845538380603253091)
                ·
                  refine ⟨21279529268307570904879637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14186352845538380603253091 21279529268307570904879637)
                  ·
                    refine ⟨997477934451917386166233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21279529268307570904879637 997477934451917386166233)
                    ·
                      rfl

theorem cell23_5827744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_5827744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827744 prefixEnd_5827744 := by exact prefixLift 5827744
  have htrace : WordTrace (prefixWord ++ tailWord_5827744) baseStart_5827744 baseEnd_5827744 := by
    simpa [prefixWord, tailWord_5827744, baseEnd_5827744] using wordTrace_append hprefix tailTrace_5827744
  have hstable : (prefixWord ++ tailWord_5827744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827744).length < 2 ^ (prefixWord ++ tailWord_5827744).sum := by decide
  have hdescent : baseEnd_5827744 < baseStart_5827744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827748 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_5827748 : Nat := 118140960795 + 5827748 * 2 ^ 59
def prefixEnd_5827748 : Nat := 4983230072969 + 3 ^ 40 * 5827748 * 2
def baseEnd_5827748 : Nat := 997478619092790047616227

theorem tailTrace_5827748 : CollatzResearch.WordTrace tailWord_5827748 prefixEnd_5827748 997478619092790047616227 := by
  unfold tailWord_5827748
  simp only [CollatzResearch.WordTrace]
  refine ⟨106277715845535885481809949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141703621127381180642413265 106277715845535885481809949)
  ·
    refine ⟨39854143442075957055678731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106277715845535885481809949 39854143442075957055678731)
    ·
      refine ⟨59781215163113935583518097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39854143442075957055678731 59781215163113935583518097)
      ·
        refine ⟨44835911372335451687638573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59781215163113935583518097 44835911372335451687638573)
        ·
          refine ⟨16813466764625794382864465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44835911372335451687638573 16813466764625794382864465)
          ·
            refine ⟨12610100073469345787148349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16813466764625794382864465 12610100073469345787148349)
            ·
              refine ⟨4728787527551004670180631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12610100073469345787148349 4728787527551004670180631)
              ·
                refine ⟨7093181291326507005270947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728787527551004670180631 7093181291326507005270947)
                ·
                  refine ⟨10639771936989760507906421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7093181291326507005270947 10639771936989760507906421)
                  ·
                    refine ⟨997478619092790047616227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10639771936989760507906421 997478619092790047616227)
                    ·
                      rfl

theorem cell23_5827748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_5827748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827748 prefixEnd_5827748 := by exact prefixLift 5827748
  have htrace : WordTrace (prefixWord ++ tailWord_5827748) baseStart_5827748 baseEnd_5827748 := by
    simpa [prefixWord, tailWord_5827748, baseEnd_5827748] using wordTrace_append hprefix tailTrace_5827748
  have hstable : (prefixWord ++ tailWord_5827748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827748).length < 2 ^ (prefixWord ++ tailWord_5827748).sum := by decide
  have hdescent : baseEnd_5827748 < baseStart_5827748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827762 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_5827762 : Nat := 118140960795 + 5827762 * 2 ^ 59
def prefixEnd_5827762 : Nat := 4983230072969 + 3 ^ 40 * 5827762 * 2
def baseEnd_5827762 : Nat := 2992443046007533088073617

theorem tailTrace_5827762 : CollatzResearch.WordTrace tailWord_5827762 prefixEnd_5827762 2992443046007533088073617 := by
  unfold tailWord_5827762
  simp only [CollatzResearch.WordTrace]
  refine ⟨53138985578255262838657385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141703961542014034236419693 53138985578255262838657385)
  ·
    refine ⟨39854239183691447128993039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53138985578255262838657385 39854239183691447128993039)
    ·
      refine ⟨59781358775537170693489559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39854239183691447128993039 59781358775537170693489559)
      ·
        refine ⟨89672038163305756040234339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59781358775537170693489559 89672038163305756040234339)
        ·
          refine ⟨134508057244958634060351509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89672038163305756040234339 134508057244958634060351509)
          ·
            refine ⟨6305065183357435971578977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134508057244958634060351509 6305065183357435971578977)
            ·
              refine ⟨4728798887518076978684233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305065183357435971578977 4728798887518076978684233)
              ·
                refine ⟨3546599165638557734013175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728798887518076978684233 3546599165638557734013175)
                ·
                  refine ⟨5319898748457836601019763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546599165638557734013175 5319898748457836601019763)
                  ·
                    refine ⟨7979848122686754901529645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319898748457836601019763 7979848122686754901529645)
                    ·
                      refine ⟨2992443046007533088073617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979848122686754901529645 2992443046007533088073617)
                      ·
                        rfl

theorem cell23_5827762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_5827762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827762 prefixEnd_5827762 := by exact prefixLift 5827762
  have htrace : WordTrace (prefixWord ++ tailWord_5827762) baseStart_5827762 baseEnd_5827762 := by
    simpa [prefixWord, tailWord_5827762, baseEnd_5827762] using wordTrace_append hprefix tailTrace_5827762
  have hstable : (prefixWord ++ tailWord_5827762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827762).length < 2 ^ (prefixWord ++ tailWord_5827762).sum := by decide
  have hdescent : baseEnd_5827762 < baseStart_5827762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827789 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5827789 : Nat := 118140960795 + 5827789 * 2 ^ 59
def prefixEnd_5827789 : Nat := 4983230072969 + 3 ^ 40 * 5827789 * 2
def baseEnd_5827789 : Nat := 2992456909985204482435993

theorem tailTrace_5827789 : CollatzResearch.WordTrace tailWord_5827789 prefixEnd_5827789 2992456909985204482435993 := by
  unfold tailWord_5827789
  simp only [CollatzResearch.WordTrace]
  refine ⟨212556927083923234965862421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141704618055948823310574947 212556927083923234965862421)
  ·
    refine ⟨9963605957058901639024801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212556927083923234965862421 9963605957058901639024801)
    ·
      refine ⟨7472704467794176229268601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9963605957058901639024801 7472704467794176229268601)
      ·
        refine ⟨5604528350845632171951451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7472704467794176229268601 5604528350845632171951451)
        ·
          refine ⟨8406792526268448257927177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604528350845632171951451 8406792526268448257927177)
          ·
            refine ⟨6305094394701336193445383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8406792526268448257927177 6305094394701336193445383)
            ·
              refine ⟨9457641592052004290168075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305094394701336193445383 9457641592052004290168075)
              ·
                refine ⟨14186462388078006435252113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9457641592052004290168075 14186462388078006435252113)
                ·
                  refine ⟨10639846791058504826439085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14186462388078006435252113 10639846791058504826439085)
                  ·
                    refine ⟨3989942546646939309914657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10639846791058504826439085 3989942546646939309914657)
                    ·
                      refine ⟨2992456909985204482435993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3989942546646939309914657 2992456909985204482435993)
                      ·
                        rfl

theorem cell23_5827789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5827789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827789 prefixEnd_5827789 := by exact prefixLift 5827789
  have htrace : WordTrace (prefixWord ++ tailWord_5827789) baseStart_5827789 baseEnd_5827789 := by
    simpa [prefixWord, tailWord_5827789, baseEnd_5827789] using wordTrace_append hprefix tailTrace_5827789
  have hstable : (prefixWord ++ tailWord_5827789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827789).length < 2 ^ (prefixWord ++ tailWord_5827789).sum := by decide
  have hdescent : baseEnd_5827789 < baseStart_5827789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827801 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 3]
def baseStart_5827801 : Nat := 118140960795 + 5827801 * 2 ^ 59
def prefixEnd_5827801 : Nat := 4983230072969 + 3 ^ 40 * 5827801 * 2
def baseEnd_5827801 : Nat := 2992463071753058435485937

theorem tailTrace_5827801 : CollatzResearch.WordTrace tailWord_5827801 prefixEnd_5827801 2992463071753058435485937 := by
  unfold tailWord_5827801
  simp only [CollatzResearch.WordTrace]
  refine ⟨212557364759879761015299257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141704909839919840676866171 212557364759879761015299257)
  ·
    refine ⟨159418023569909820761474443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212557364759879761015299257 159418023569909820761474443)
    ·
      refine ⟨239127035354864731142211665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159418023569909820761474443 239127035354864731142211665)
      ·
        refine ⟨179345276516148548356658749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239127035354864731142211665 179345276516148548356658749)
        ·
          refine ⟨67254478693555705633747031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179345276516148548356658749 67254478693555705633747031)
          ·
            refine ⟨100881718040333558450620547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67254478693555705633747031 100881718040333558450620547)
            ·
              refine ⟨151322577060500337675930821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100881718040333558450620547 151322577060500337675930821)
              ·
                refine ⟨28372983198843813314237029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151322577060500337675930821 28372983198843813314237029)
                ·
                  refine ⟨5319934349783214996419443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28372983198843813314237029 5319934349783214996419443)
                  ·
                    refine ⟨7979901524674822494629165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319934349783214996419443 7979901524674822494629165)
                    ·
                      refine ⟨2992463071753058435485937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979901524674822494629165 2992463071753058435485937)
                      ·
                        rfl

theorem cell23_5827801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_5827801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827801 prefixEnd_5827801 := by exact prefixLift 5827801
  have htrace : WordTrace (prefixWord ++ tailWord_5827801) baseStart_5827801 baseEnd_5827801 := by
    simpa [prefixWord, tailWord_5827801, baseEnd_5827801] using wordTrace_append hprefix tailTrace_5827801
  have hstable : (prefixWord ++ tailWord_5827801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827801).length < 2 ^ (prefixWord ++ tailWord_5827801).sum := by decide
  have hdescent : baseEnd_5827801 < baseStart_5827801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827805 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5827805 : Nat := 118140960795 + 5827805 * 2 ^ 59
def prefixEnd_5827805 : Nat := 4983230072969 + 3 ^ 40 * 5827805 * 2
def baseEnd_5827805 : Nat := 2992465125675676419835919

theorem tailTrace_5827805 : CollatzResearch.WordTrace tailWord_5827805 prefixEnd_5827805 2992465125675676419835919 := by
  unfold tailWord_5827805
  simp only [CollatzResearch.WordTrace]
  refine ⟨212557510651865269698444869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141705007101243513132296579 212557510651865269698444869)
  ·
    refine ⟨39854533247224738068458413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212557510651865269698444869 39854533247224738068458413)
    ·
      refine ⟨14945449967709276775671905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39854533247224738068458413 14945449967709276775671905)
      ·
        refine ⟨11209087475781957581753929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14945449967709276775671905 11209087475781957581753929)
        ·
          refine ⟨8406815606836468186315447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11209087475781957581753929 8406815606836468186315447)
          ·
            refine ⟨12610223410254702279473171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8406815606836468186315447 12610223410254702279473171)
            ·
              refine ⟨18915335115382053419209757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610223410254702279473171 18915335115382053419209757)
              ·
                refine ⟨7093250668268270032203659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18915335115382053419209757 7093250668268270032203659)
                ·
                  refine ⟨10639876002402405048305489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7093250668268270032203659 10639876002402405048305489)
                  ·
                    refine ⟨7979907001801803786229117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10639876002402405048305489 7979907001801803786229117)
                    ·
                      refine ⟨2992465125675676419835919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979907001801803786229117 2992465125675676419835919)
                      ·
                        rfl

theorem cell23_5827805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5827805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827805 prefixEnd_5827805 := by exact prefixLift 5827805
  have htrace : WordTrace (prefixWord ++ tailWord_5827805) baseStart_5827805 baseEnd_5827805 := by
    simpa [prefixWord, tailWord_5827805, baseEnd_5827805] using wordTrace_append hprefix tailTrace_5827805
  have hstable : (prefixWord ++ tailWord_5827805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827805).length < 2 ^ (prefixWord ++ tailWord_5827805).sum := by decide
  have hdescent : baseEnd_5827805 < baseStart_5827805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827818 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_5827818 : Nat := 118140960795 + 5827818 * 2 ^ 59
def prefixEnd_5827818 : Nat := 4983230072969 + 3 ^ 40 * 5827818 * 2
def baseEnd_5827818 : Nat := 2992471800924184868973359

theorem tailTrace_5827818 : CollatzResearch.WordTrace tailWord_5827818 prefixEnd_5827818 2992471800924184868973359 := by
  unfold tailWord_5827818
  simp only [CollatzResearch.WordTrace]
  refine ⟨53139496200204543229667027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141705323200545448612445405 53139496200204543229667027)
  ·
    refine ⟨79709244300306814844500541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53139496200204543229667027 79709244300306814844500541)
    ·
      refine ⟨29890966612615055566687703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79709244300306814844500541 29890966612615055566687703)
      ·
        refine ⟨44836449918922583350031555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29890966612615055566687703 44836449918922583350031555)
        ·
          refine ⟨67254674878383875025047333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44836449918922583350031555 67254674878383875025047333)
          ·
            refine ⟨12610251539696976567196375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67254674878383875025047333 12610251539696976567196375)
            ·
              refine ⟨18915377309545464850794563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610251539696976567196375 18915377309545464850794563)
              ·
                refine ⟨28373065964318197276191845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18915377309545464850794563 28373065964318197276191845)
                ·
                  refine ⟨5319949868309661989285971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28373065964318197276191845 5319949868309661989285971)
                  ·
                    refine ⟨7979924802464492983928957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5319949868309661989285971 7979924802464492983928957)
                    ·
                      refine ⟨2992471800924184868973359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7979924802464492983928957 2992471800924184868973359)
                      ·
                        rfl

theorem cell23_5827818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_5827818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827818 prefixEnd_5827818 := by exact prefixLift 5827818
  have htrace : WordTrace (prefixWord ++ tailWord_5827818) baseStart_5827818 baseEnd_5827818 := by
    simpa [prefixWord, tailWord_5827818, baseEnd_5827818] using wordTrace_append hprefix tailTrace_5827818
  have hstable : (prefixWord ++ tailWord_5827818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827818).length < 2 ^ (prefixWord ++ tailWord_5827818).sum := by decide
  have hdescent : baseEnd_5827818 < baseStart_5827818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827834 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_5827834 : Nat := 118140960795 + 5827834 * 2 ^ 59
def prefixEnd_5827834 : Nat := 4983230072969 + 3 ^ 40 * 5827834 * 2
def baseEnd_5827834 : Nat := 997493338871552268791095

theorem tailTrace_5827834 : CollatzResearch.WordTrace tailWord_5827834 prefixEnd_5827834 997493338871552268791095 := by
  unfold tailWord_5827834
  simp only [CollatzResearch.WordTrace]
  refine ⟨53139642092190051912812639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141705712245840138434167037 53139642092190051912812639)
  ·
    refine ⟨79709463138285077869218959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53139642092190051912812639 79709463138285077869218959)
    ·
      refine ⟨119564194707427616803828439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79709463138285077869218959 119564194707427616803828439)
      ·
        refine ⟨179346292061141425205742659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119564194707427616803828439 179346292061141425205742659)
        ·
          refine ⟨269019438091712137808613989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179346292061141425205742659 269019438091712137808613989)
          ·
            refine ⟨50441144642196025839115123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269019438091712137808613989 50441144642196025839115123)
            ·
              refine ⟨75661716963294038758672685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50441144642196025839115123 75661716963294038758672685)
              ·
                refine ⟨28373143861235264534502257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75661716963294038758672685 28373143861235264534502257)
                ·
                  refine ⟨21279857895926448400876693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28373143861235264534502257 21279857895926448400876693)
                  ·
                    refine ⟨997493338871552268791095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21279857895926448400876693 997493338871552268791095)
                    ·
                      rfl

theorem cell23_5827834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_5827834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827834 prefixEnd_5827834 := by exact prefixLift 5827834
  have htrace : WordTrace (prefixWord ++ tailWord_5827834) baseStart_5827834 baseEnd_5827834 := by
    simpa [prefixWord, tailWord_5827834, baseEnd_5827834] using wordTrace_append hprefix tailTrace_5827834
  have hstable : (prefixWord ++ tailWord_5827834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827834).length < 2 ^ (prefixWord ++ tailWord_5827834).sum := by decide
  have hdescent : baseEnd_5827834 < baseStart_5827834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827892 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_5827892 : Nat := 118140960795 + 5827892 * 2 ^ 59
def prefixEnd_5827892 : Nat := 4983230072969 + 3 ^ 40 * 5827892 * 2
def baseEnd_5827892 : Nat := 2992509798492617579448019

theorem tailTrace_5827892 : CollatzResearch.WordTrace tailWord_5827892 prefixEnd_5827892 2992509798492617579448019 := by
  unfold tailWord_5827892
  simp only [CollatzResearch.WordTrace]
  refine ⟨106280341901275041778430965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141707122535033389037907953 106280341901275041778430965)
  ·
    refine ⟨9963782053244535166727903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106280341901275041778430965 9963782053244535166727903)
    ·
      refine ⟨14945673079866802750091855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9963782053244535166727903 14945673079866802750091855)
      ·
        refine ⟨22418509619800204125137783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14945673079866802750091855 22418509619800204125137783)
        ·
          refine ⟨33627764429700306187706675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22418509619800204125137783 33627764429700306187706675)
          ·
            refine ⟨50441646644550459281560013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33627764429700306187706675 50441646644550459281560013)
            ·
              refine ⟨18915617491706422230585005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50441646644550459281560013 18915617491706422230585005)
              ·
                refine ⟨7093356559389908336469377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18915617491706422230585005 7093356559389908336469377)
                ·
                  refine ⟨5320017419542431252352033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7093356559389908336469377 5320017419542431252352033)
                  ·
                    refine ⟨3990013064656823439264025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320017419542431252352033 3990013064656823439264025)
                    ·
                      refine ⟨2992509798492617579448019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990013064656823439264025 2992509798492617579448019)
                      ·
                        rfl

theorem cell23_5827892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_5827892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827892 prefixEnd_5827892 := by exact prefixLift 5827892
  have htrace : WordTrace (prefixWord ++ tailWord_5827892) baseStart_5827892 baseEnd_5827892 := by
    simpa [prefixWord, tailWord_5827892, baseEnd_5827892] using wordTrace_append hprefix tailTrace_5827892
  have hstable : (prefixWord ++ tailWord_5827892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827892).length < 2 ^ (prefixWord ++ tailWord_5827892).sum := by decide
  have hdescent : baseEnd_5827892 < baseStart_5827892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827904 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_5827904 : Nat := 118140960795 + 5827904 * 2 ^ 59
def prefixEnd_5827904 : Nat := 4983230072969 + 3 ^ 40 * 5827904 * 2
def baseEnd_5827904 : Nat := 2992515960260471532497963

theorem tailTrace_5827904 : CollatzResearch.WordTrace tailWord_5827904 prefixEnd_5827904 2992515960260471532497963 := by
  unfold tailWord_5827904
  simp only [CollatzResearch.WordTrace]
  refine ⟨106280560739253304803149383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141707414319004406404199177 106280560739253304803149383)
  ·
    refine ⟨159420841108879957204724075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106280560739253304803149383 159420841108879957204724075)
    ·
      refine ⟨239131261663319935807086113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159420841108879957204724075 239131261663319935807086113)
      ·
        refine ⟨179348446247489951855314585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239131261663319935807086113 179348446247489951855314585)
        ·
          refine ⟨134511334685617463891485939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179348446247489951855314585 134511334685617463891485939)
          ·
            refine ⟨201767002028426195837228909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134511334685617463891485939 201767002028426195837228909)
            ·
              refine ⟨75662625760659823438960841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201767002028426195837228909 75662625760659823438960841)
              ·
                refine ⟨56746969320494867579220631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75662625760659823438960841 56746969320494867579220631)
                ·
                  refine ⟨85120453980742301368830947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56746969320494867579220631 85120453980742301368830947)
                  ·
                    refine ⟨127680680971113452053246421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85120453980742301368830947 127680680971113452053246421)
                    ·
                      refine ⟨2992515960260471532497963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127680680971113452053246421 2992515960260471532497963)
                      ·
                        rfl

theorem cell23_5827904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_5827904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827904 prefixEnd_5827904 := by exact prefixLift 5827904
  have htrace : WordTrace (prefixWord ++ tailWord_5827904) baseStart_5827904 baseEnd_5827904 := by
    simpa [prefixWord, tailWord_5827904, baseEnd_5827904] using wordTrace_append hprefix tailTrace_5827904
  have hstable : (prefixWord ++ tailWord_5827904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827904).length < 2 ^ (prefixWord ++ tailWord_5827904).sum := by decide
  have hdescent : baseEnd_5827904 < baseStart_5827904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827911 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 2, 5]
def baseStart_5827911 : Nat := 118140960795 + 5827911 * 2 ^ 59
def prefixEnd_5827911 : Nat := 4983230072969 + 3 ^ 40 * 5827911 * 2
def baseEnd_5827911 : Nat := 997506518208351001703477

theorem tailTrace_5827911 : CollatzResearch.WordTrace tailWord_5827911 prefixEnd_5827911 997506518208351001703477 := by
  unfold tailWord_5827911
  simp only [CollatzResearch.WordTrace]
  refine ⟨212561376789481249801803587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141707584526320833201202391 212561376789481249801803587)
  ·
    refine ⟨318842065184221874702705381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212561376789481249801803587 318842065184221874702705381)
    ·
      refine ⟨59782887222041601506757259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318842065184221874702705381 59782887222041601506757259)
      ·
        refine ⟨89674330833062402260135889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59782887222041601506757259 89674330833062402260135889)
        ·
          refine ⟨67255748124796801695101917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89674330833062402260135889 67255748124796801695101917)
          ·
            refine ⟨25220905546798800635663219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67255748124796801695101917 25220905546798800635663219)
            ·
              refine ⟨37831358320198200953494829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25220905546798800635663219 37831358320198200953494829)
              ·
                refine ⟨14186759370074325357560561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37831358320198200953494829 14186759370074325357560561)
                ·
                  refine ⟨10640069527555744018170421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14186759370074325357560561 10640069527555744018170421)
                  ·
                    refine ⟨997506518208351001703477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10640069527555744018170421 997506518208351001703477)
                    ·
                      rfl

theorem cell23_5827911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_5827911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827911 prefixEnd_5827911 := by exact prefixLift 5827911
  have htrace : WordTrace (prefixWord ++ tailWord_5827911) baseStart_5827911 baseEnd_5827911 := by
    simpa [prefixWord, tailWord_5827911, baseEnd_5827911] using wordTrace_append hprefix tailTrace_5827911
  have hstable : (prefixWord ++ tailWord_5827911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827911).length < 2 ^ (prefixWord ++ tailWord_5827911).sum := by decide
  have hdescent : baseEnd_5827911 < baseStart_5827911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827948 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_5827948 : Nat := 118140960795 + 5827948 * 2 ^ 59
def prefixEnd_5827948 : Nat := 4983230072969 + 3 ^ 40 * 5827948 * 2
def baseEnd_5827948 : Nat := 2992538553409269360347761

theorem tailTrace_5827948 : CollatzResearch.WordTrace tailWord_5827948 prefixEnd_5827948 2992538553409269360347761 := by
  unfold tailWord_5827948
  simp only [CollatzResearch.WordTrace]
  refine ⟨106281363145173602560450249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141708484193564803413933665 106281363145173602560450249)
  ·
    refine ⟨79711022358880201920337687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106281363145173602560450249 79711022358880201920337687)
    ·
      refine ⟨119566533538320302880506531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79711022358880201920337687 119566533538320302880506531)
      ·
        refine ⟨179349800307480454320759797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119566533538320302880506531 179349800307480454320759797)
        ·
          refine ⟨16814043778826292592571231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179349800307480454320759797 16814043778826292592571231)
          ·
            refine ⟨25221065668239438888856847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16814043778826292592571231 25221065668239438888856847)
            ·
              refine ⟨37831598502359158333285271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221065668239438888856847 37831598502359158333285271)
              ·
                refine ⟨56747397753538737499927907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37831598502359158333285271 56747397753538737499927907)
                ·
                  refine ⟨85121096630308106249891861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56747397753538737499927907 85121096630308106249891861)
                  ·
                    refine ⟨3990051404545692480463681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85121096630308106249891861 3990051404545692480463681)
                    ·
                      refine ⟨2992538553409269360347761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990051404545692480463681 2992538553409269360347761)
                      ·
                        rfl

theorem cell23_5827948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_5827948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827948 prefixEnd_5827948 := by exact prefixLift 5827948
  have htrace : WordTrace (prefixWord ++ tailWord_5827948) baseStart_5827948 baseEnd_5827948 := by
    simpa [prefixWord, tailWord_5827948, baseEnd_5827948] using wordTrace_append hprefix tailTrace_5827948
  have hstable : (prefixWord ++ tailWord_5827948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827948).length < 2 ^ (prefixWord ++ tailWord_5827948).sum := by decide
  have hdescent : baseEnd_5827948 < baseStart_5827948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827951 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_5827951 : Nat := 118140960795 + 5827951 * 2 ^ 59
def prefixEnd_5827951 : Nat := 4983230072969 + 3 ^ 40 * 5827951 * 2
def baseEnd_5827951 : Nat := 2992540093851232848610247

theorem tailTrace_5827951 : CollatzResearch.WordTrace tailWord_5827951 prefixEnd_5827951 2992540093851232848610247 := by
  unfold tailWord_5827951
  simp only [CollatzResearch.WordTrace]
  refine ⟨212562835709336336633259707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141708557139557557755506471 212562835709336336633259707)
  ·
    refine ⟨318844253564004504949889561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212562835709336336633259707 318844253564004504949889561)
    ·
      refine ⟨239133190173003378712417171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318844253564004504949889561 239133190173003378712417171)
      ·
        refine ⟨358699785259505068068625757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239133190173003378712417171 358699785259505068068625757)
        ·
          refine ⟨134512419472314400525734659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358699785259505068068625757 134512419472314400525734659)
          ·
            refine ⟨201768629208471600788601989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134512419472314400525734659 201768629208471600788601989)
            ·
              refine ⟨37831617976588425147862873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201768629208471600788601989 37831617976588425147862873)
              ·
                refine ⟨28373713482441318860897155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37831617976588425147862873 28373713482441318860897155)
                ·
                  refine ⟨42560570223661978291345733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28373713482441318860897155 42560570223661978291345733)
                  ·
                    refine ⟨7980106916936620929627325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42560570223661978291345733 7980106916936620929627325)
                    ·
                      refine ⟨2992540093851232848610247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7980106916936620929627325 2992540093851232848610247)
                      ·
                        rfl

theorem cell23_5827951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_5827951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827951 prefixEnd_5827951 := by exact prefixLift 5827951
  have htrace : WordTrace (prefixWord ++ tailWord_5827951) baseStart_5827951 baseEnd_5827951 := by
    simpa [prefixWord, tailWord_5827951, baseEnd_5827951] using wordTrace_append hprefix tailTrace_5827951
  have hstable : (prefixWord ++ tailWord_5827951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827951).length < 2 ^ (prefixWord ++ tailWord_5827951).sum := by decide
  have hdescent : baseEnd_5827951 < baseStart_5827951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827975 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 1, 4]
def baseStart_5827975 : Nat := 118140960795 + 5827975 * 2 ^ 59
def prefixEnd_5827975 : Nat := 4983230072969 + 3 ^ 40 * 5827975 * 2
def baseEnd_5827975 : Nat := 997517472462313584903379

theorem tailTrace_5827975 : CollatzResearch.WordTrace tailWord_5827975 prefixEnd_5827975 997517472462313584903379 := by
  unfold tailWord_5827975
  simp only [CollatzResearch.WordTrace]
  refine ⟨212563711061249388732133379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141709140707499592488088919 212563711061249388732133379)
  ·
    refine ⟨318845566591874083098200069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212563711061249388732133379 318845566591874083098200069)
    ·
      refine ⟨59783543735976390580912513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318845566591874083098200069 59783543735976390580912513)
      ·
        refine ⟨44837657801982292935684385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59783543735976390580912513 44837657801982292935684385)
        ·
          refine ⟨33628243351486719701763289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44837657801982292935684385 33628243351486719701763289)
          ·
            refine ⟨25221182513615039776322467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33628243351486719701763289 25221182513615039776322467)
            ·
              refine ⟨37831773770422559664483701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221182513615039776322467 37831773770422559664483701)
              ·
                refine ⟨3546728790977114968545347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37831773770422559664483701 3546728790977114968545347)
                ·
                  refine ⟨5320093186465672452818021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546728790977114968545347 5320093186465672452818021)
                  ·
                    refine ⟨997517472462313584903379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320093186465672452818021 997517472462313584903379)
                    ·
                      rfl

theorem cell23_5827975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_5827975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827975 prefixEnd_5827975 := by exact prefixLift 5827975
  have htrace : WordTrace (prefixWord ++ tailWord_5827975) baseStart_5827975 baseEnd_5827975 := by
    simpa [prefixWord, tailWord_5827975, baseEnd_5827975] using wordTrace_append hprefix tailTrace_5827975
  have hstable : (prefixWord ++ tailWord_5827975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827975).length < 2 ^ (prefixWord ++ tailWord_5827975).sum := by decide
  have hdescent : baseEnd_5827975 < baseStart_5827975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5827988 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 8]
def baseStart_5827988 : Nat := 118140960795 + 5827988 * 2 ^ 59
def prefixEnd_5827988 : Nat := 4983230072969 + 3 ^ 40 * 5827988 * 2
def baseEnd_5827988 : Nat := 332506565848383244871953

theorem tailTrace_5827988 : CollatzResearch.WordTrace tailWord_5827988 prefixEnd_5827988 332506565848383244871953 := by
  unfold tailWord_5827988
  simp only [CollatzResearch.WordTrace]
  refine ⟨106282092605101145976178309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141709456806801527968237745 106282092605101145976178309)
  ·
    refine ⟨19927892363456464870533433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106282092605101145976178309 19927892363456464870533433)
    ·
      refine ⟨14945919272592348652900075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19927892363456464870533433 14945919272592348652900075)
      ·
        refine ⟨22418878908888522979350113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14945919272592348652900075 22418878908888522979350113)
        ·
          refine ⟨16814159181666392234512585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22418878908888522979350113 16814159181666392234512585)
          ·
            refine ⟨12610619386249794175884439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16814159181666392234512585 12610619386249794175884439)
            ·
              refine ⟨18915929079374691263826659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610619386249794175884439 18915929079374691263826659)
              ·
                refine ⟨28373893619062036895739989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18915929079374691263826659 28373893619062036895739989)
                ·
                  refine ⟨332506565848383244871953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28373893619062036895739989 332506565848383244871953)
                  ·
                    rfl

theorem cell23_5827988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_5827988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5827988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5827988 prefixEnd_5827988 := by exact prefixLift 5827988
  have htrace : WordTrace (prefixWord ++ tailWord_5827988) baseStart_5827988 baseEnd_5827988 := by
    simpa [prefixWord, tailWord_5827988, baseEnd_5827988] using wordTrace_append hprefix tailTrace_5827988
  have hstable : (prefixWord ++ tailWord_5827988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5827988).length < 2 ^ (prefixWord ++ tailWord_5827988).sum := by decide
  have hdescent : baseEnd_5827988 < baseStart_5827988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5827988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828031 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 1, 6]
def baseStart_5828031 : Nat := 118140960795 + 5828031 * 2 ^ 59
def prefixEnd_5828031 : Nat := 4983230072969 + 3 ^ 40 * 5828031 * 2
def baseEnd_5828031 : Nat := 997527057434530845203293

theorem tailTrace_5828031 : CollatzResearch.WordTrace tailWord_5828031 prefixEnd_5828031 997527057434530845203293 := by
  unfold tailWord_5828031
  simp only [CollatzResearch.WordTrace]
  refine ⟨212565753549046510296171947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141710502366031006864114631 212565753549046510296171947)
  ·
    refine ⟨318848630323569765444257921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212565753549046510296171947 318848630323569765444257921)
    ·
      refine ⟨239136472742677324083193441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318848630323569765444257921 239136472742677324083193441)
      ·
        refine ⟨179352354557007993062395081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239136472742677324083193441 179352354557007993062395081)
        ·
          refine ⟨134514265917755994796796311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179352354557007993062395081 134514265917755994796796311)
          ·
            refine ⟨201771398876633992195194467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134514265917755994796796311 201771398876633992195194467)
            ·
              refine ⟨302657098314950988292791701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201771398876633992195194467 302657098314950988292791701)
              ·
                refine ⟨14187051483513327576224611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302657098314950988292791701 14187051483513327576224611)
                ·
                  refine ⟨21280577225269991364336917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14187051483513327576224611 21280577225269991364336917)
                  ·
                    refine ⟨997527057434530845203293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21280577225269991364336917 997527057434530845203293)
                    ·
                      rfl

theorem cell23_5828031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_5828031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828031 prefixEnd_5828031 := by exact prefixLift 5828031
  have htrace : WordTrace (prefixWord ++ tailWord_5828031) baseStart_5828031 baseEnd_5828031 := by
    simpa [prefixWord, tailWord_5828031, baseEnd_5828031] using wordTrace_append hprefix tailTrace_5828031
  have hstable : (prefixWord ++ tailWord_5828031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828031).length < 2 ^ (prefixWord ++ tailWord_5828031).sum := by decide
  have hdescent : baseEnd_5828031 < baseStart_5828031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828032 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 1, 1, 3]
def baseStart_5828032 : Nat := 118140960795 + 5828032 * 2 ^ 59
def prefixEnd_5828032 : Nat := 4983230072969 + 3 ^ 40 * 5828032 * 2
def baseEnd_5828032 : Nat := 2992581685784247031697375

theorem tailTrace_5828032 : CollatzResearch.WordTrace tailWord_5828032 prefixEnd_5828032 2992581685784247031697375 := by
  unfold tailWord_5828032
  simp only [CollatzResearch.WordTrace]
  refine ⟨106282895011021443733479175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141710526681361924977972233 106282895011021443733479175)
  ·
    refine ⟨159424342516532165600218763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106282895011021443733479175 159424342516532165600218763)
    ·
      refine ⟨239136513774798248400328145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159424342516532165600218763 239136513774798248400328145)
      ·
        refine ⟨179352385331098686300246109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239136513774798248400328145 179352385331098686300246109)
        ·
          refine ⟨67257144499162007362592291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179352385331098686300246109 67257144499162007362592291)
          ·
            refine ⟨100885716748743011043888437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67257144499162007362592291 100885716748743011043888437)
            ·
              refine ⟨9458035945194657285364541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100885716748743011043888437 9458035945194657285364541)
              ·
                refine ⟨3546763479447996482011703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458035945194657285364541 3546763479447996482011703)
                ·
                  refine ⟨5320145219171994723017555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546763479447996482011703 5320145219171994723017555)
                  ·
                    refine ⟨7980217828757992084526333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5320145219171994723017555 7980217828757992084526333)
                    ·
                      refine ⟨2992581685784247031697375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7980217828757992084526333 2992581685784247031697375)
                      ·
                        rfl

theorem cell23_5828032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_5828032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828032 prefixEnd_5828032 := by exact prefixLift 5828032
  have htrace : WordTrace (prefixWord ++ tailWord_5828032) baseStart_5828032 baseEnd_5828032 := by
    simpa [prefixWord, tailWord_5828032, baseEnd_5828032] using wordTrace_append hprefix tailTrace_5828032
  have hstable : (prefixWord ++ tailWord_5828032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828032).length < 2 ^ (prefixWord ++ tailWord_5828032).sum := by decide
  have hdescent : baseEnd_5828032 < baseStart_5828032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828058 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_5828058 : Nat := 118140960795 + 5828058 * 2 ^ 59
def prefixEnd_5828058 : Nat := 4983230072969 + 3 ^ 40 * 5828058 * 2
def baseEnd_5828058 : Nat := 2992595036281263929972255

theorem tailTrace_5828058 : CollatzResearch.WordTrace tailWord_5828058 prefixEnd_5828058 2992595036281263929972255 := by
  unfold tailWord_5828058
  simp only [CollatzResearch.WordTrace]
  refine ⟨53141684579987173476851207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141711158879965795938269885 53141684579987173476851207)
  ·
    refine ⟨79712526869980760215276811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53141684579987173476851207 79712526869980760215276811)
    ·
      refine ⟨119568790304971140322915217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79712526869980760215276811 119568790304971140322915217)
      ·
        refine ⟨89676592728728355242186413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119568790304971140322915217 89676592728728355242186413)
        ·
          refine ⟨33628722273273133215819905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89676592728728355242186413 33628722273273133215819905)
          ·
            refine ⟨25221541704954849911864929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33628722273273133215819905 25221541704954849911864929)
            ·
              refine ⟨18916156278716137433898697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25221541704954849911864929 18916156278716137433898697)
              ·
                refine ⟨14187117209037103075424023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18916156278716137433898697 14187117209037103075424023)
                ·
                  refine ⟨21280675813555654613136035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14187117209037103075424023 21280675813555654613136035)
                  ·
                    refine ⟨31921013720333481919704053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21280675813555654613136035 31921013720333481919704053)
                    ·
                      refine ⟨2992595036281263929972255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31921013720333481919704053 2992595036281263929972255)
                      ·
                        rfl

theorem cell23_5828058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_5828058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828058 prefixEnd_5828058 := by exact prefixLift 5828058
  have htrace : WordTrace (prefixWord ++ tailWord_5828058) baseStart_5828058 baseEnd_5828058 := by
    simpa [prefixWord, tailWord_5828058, baseEnd_5828058] using wordTrace_append hprefix tailTrace_5828058
  have hstable : (prefixWord ++ tailWord_5828058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828058).length < 2 ^ (prefixWord ++ tailWord_5828058).sum := by decide
  have hdescent : baseEnd_5828058 < baseStart_5828058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828065 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_5828065 : Nat := 118140960795 + 5828065 * 2 ^ 59
def prefixEnd_5828065 : Nat := 4983230072969 + 3 ^ 40 * 5828065 * 2
def baseEnd_5828065 : Nat := 997532876881948467528241

theorem tailTrace_5828065 : CollatzResearch.WordTrace tailWord_5828065 prefixEnd_5828065 997532876881948467528241 := by
  unfold tailWord_5828065
  simp only [CollatzResearch.WordTrace]
  refine ⟨212566993630923334102909649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141711329087282222735273099 212566993630923334102909649)
  ·
    refine ⟨159425245223192500577182237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212566993630923334102909649 159425245223192500577182237)
    ·
      refine ⟨59784466958697187716443339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159425245223192500577182237 59784466958697187716443339)
      ·
        refine ⟨89676700438045781574665009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59784466958697187716443339 89676700438045781574665009)
        ·
          refine ⟨67257525328534336180998757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89676700438045781574665009 67257525328534336180998757)
          ·
            refine ⟨12610785999100188033937267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67257525328534336180998757 12610785999100188033937267)
            ·
              refine ⟨18916178998650282050905901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610785999100188033937267 18916178998650282050905901)
              ·
                refine ⟨7093567124493855769089713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18916178998650282050905901 7093567124493855769089713)
                ·
                  refine ⟨5320175343370391826817285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7093567124493855769089713 5320175343370391826817285)
                  ·
                    refine ⟨997532876881948467528241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320175343370391826817285 997532876881948467528241)
                    ·
                      rfl

theorem cell23_5828065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_5828065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828065 prefixEnd_5828065 := by exact prefixLift 5828065
  have htrace : WordTrace (prefixWord ++ tailWord_5828065) baseStart_5828065 baseEnd_5828065 := by
    simpa [prefixWord, tailWord_5828065, baseEnd_5828065] using wordTrace_append hprefix tailTrace_5828065
  have hstable : (prefixWord ++ tailWord_5828065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828065).length < 2 ^ (prefixWord ++ tailWord_5828065).sum := by decide
  have hdescent : baseEnd_5828065 < baseStart_5828065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828085 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5828085 : Nat := 118140960795 + 5828085 * 2 ^ 59
def prefixEnd_5828085 : Nat := 4983230072969 + 3 ^ 40 * 5828085 * 2
def baseEnd_5828085 : Nat := 2992608900258935324334631

theorem tailTrace_5828085 : CollatzResearch.WordTrace tailWord_5828085 prefixEnd_5828085 2992608900258935324334631 := by
  unfold tailWord_5828085
  simp only [CollatzResearch.WordTrace]
  refine ⟨212567723090850877518637709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141711815393900585012425139 212567723090850877518637709)
  ·
    refine ⟨79712896159069079069489141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212567723090850877518637709 79712896159069079069489141)
    ·
      refine ⟨7473084014912726162764607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79712896159069079069489141 7473084014912726162764607)
      ·
        refine ⟨11209626022369089244146911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473084014912726162764607 11209626022369089244146911)
        ·
          refine ⟨16814439033553633866220367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11209626022369089244146911 16814439033553633866220367)
          ·
            refine ⟨25221658550330450799330551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16814439033553633866220367 25221658550330450799330551)
            ·
              refine ⟨37832487825495676198995827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221658550330450799330551 37832487825495676198995827)
              ·
                refine ⟨56748731738243514298493741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37832487825495676198995827 56748731738243514298493741)
                ·
                  refine ⟨21280774401841317861935153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56748731738243514298493741 21280774401841317861935153)
                  ·
                    refine ⟨15960580801380988396451365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21280774401841317861935153 15960580801380988396451365)
                    ·
                      refine ⟨2992608900258935324334631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15960580801380988396451365 2992608900258935324334631)
                      ·
                        rfl

theorem cell23_5828085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5828085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828085 prefixEnd_5828085 := by exact prefixLift 5828085
  have htrace : WordTrace (prefixWord ++ tailWord_5828085) baseStart_5828085 baseEnd_5828085 := by
    simpa [prefixWord, tailWord_5828085, baseEnd_5828085] using wordTrace_append hprefix tailTrace_5828085
  have hstable : (prefixWord ++ tailWord_5828085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828085).length < 2 ^ (prefixWord ++ tailWord_5828085).sum := by decide
  have hdescent : baseEnd_5828085 < baseStart_5828085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828088 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_5828088 : Nat := 118140960795 + 5828088 * 2 ^ 59
def prefixEnd_5828088 : Nat := 4983230072969 + 3 ^ 40 * 5828088 * 2
def baseEnd_5828088 : Nat := 2992610440700898812597117

theorem tailTrace_5828088 : CollatzResearch.WordTrace tailWord_5828088 prefixEnd_5828088 2992610440700898812597117 := by
  unfold tailWord_5828088
  simp only [CollatzResearch.WordTrace]
  refine ⟨106283916254920004515498459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141711888339893339353997945 106283916254920004515498459)
  ·
    refine ⟨159425874382380006773247689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106283916254920004515498459 159425874382380006773247689)
    ·
      refine ⟨119569405786785005079935767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159425874382380006773247689 119569405786785005079935767)
      ·
        refine ⟨179354108680177507619903651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119569405786785005079935767 179354108680177507619903651)
        ·
          refine ⟨269031163020266261429855477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179354108680177507619903651 269031163020266261429855477)
          ·
            refine ⟨25221671533149962009048951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 269031163020266261429855477 25221671533149962009048951)
            ·
              refine ⟨37832507299724943013573427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221671533149962009048951 37832507299724943013573427)
              ·
                refine ⟨56748760949587414520360141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37832507299724943013573427 56748760949587414520360141)
                ·
                  refine ⟨21280785356095280445135053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56748760949587414520360141 21280785356095280445135053)
                  ·
                    refine ⟨7980294508535730166925645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21280785356095280445135053 7980294508535730166925645)
                    ·
                      refine ⟨2992610440700898812597117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7980294508535730166925645 2992610440700898812597117)
                      ·
                        rfl

theorem cell23_5828088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_5828088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828088 prefixEnd_5828088 := by exact prefixLift 5828088
  have htrace : WordTrace (prefixWord ++ tailWord_5828088) baseStart_5828088 baseEnd_5828088 := by
    simpa [prefixWord, tailWord_5828088, baseEnd_5828088] using wordTrace_append hprefix tailTrace_5828088
  have hstable : (prefixWord ++ tailWord_5828088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828088).length < 2 ^ (prefixWord ++ tailWord_5828088).sum := by decide
  have hdescent : baseEnd_5828088 < baseStart_5828088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828106 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_5828106 : Nat := 118140960795 + 5828106 * 2 ^ 59
def prefixEnd_5828106 : Nat := 4983230072969 + 3 ^ 40 * 5828106 * 2
def baseEnd_5828106 : Nat := 2992619683352679742172035

theorem tailTrace_5828106 : CollatzResearch.WordTrace tailWord_5828106 prefixEnd_5828106 2992619683352679742172035 := by
  unfold tailWord_5828106
  simp only [CollatzResearch.WordTrace]
  refine ⟨53142122255943699526288043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141712326015849865403434781 53142122255943699526288043)
  ·
    refine ⟨79713183383915549289432065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53142122255943699526288043 79713183383915549289432065)
    ·
      refine ⟨59784887537936661967074049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79713183383915549289432065 59784887537936661967074049)
      ·
        refine ⟨44838665653452496475305537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59784887537936661967074049 44838665653452496475305537)
        ·
          refine ⟨33628999240089372356479153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44838665653452496475305537 33628999240089372356479153)
          ·
            refine ⟨25221749430067029267359365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33628999240089372356479153 25221749430067029267359365)
            ·
              refine ⟨4729078018137567987629881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25221749430067029267359365 4729078018137567987629881)
              ·
                refine ⟨3546808513603175990722411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4729078018137567987629881 3546808513603175990722411)
                ·
                  refine ⟨5320212770404763986083617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546808513603175990722411 5320212770404763986083617)
                  ·
                    refine ⟨3990159577803572989562713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320212770404763986083617 3990159577803572989562713)
                    ·
                      refine ⟨2992619683352679742172035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990159577803572989562713 2992619683352679742172035)
                      ·
                        rfl

theorem cell23_5828106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_5828106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828106 prefixEnd_5828106 := by exact prefixLift 5828106
  have htrace : WordTrace (prefixWord ++ tailWord_5828106) baseStart_5828106 baseEnd_5828106 := by
    simpa [prefixWord, tailWord_5828106, baseEnd_5828106] using wordTrace_append hprefix tailTrace_5828106
  have hstable : (prefixWord ++ tailWord_5828106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828106).length < 2 ^ (prefixWord ++ tailWord_5828106).sum := by decide
  have hdescent : baseEnd_5828106 < baseStart_5828106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828115 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 3, 3, 2]
def baseStart_5828115 : Nat := 118140960795 + 5828115 * 2 ^ 59
def prefixEnd_5828115 : Nat := 4983230072969 + 3 ^ 40 * 5828115 * 2
def baseEnd_5828115 : Nat := 2992624304678570206959493

theorem tailTrace_5828115 : CollatzResearch.WordTrace tailWord_5828115 prefixEnd_5828115 2992624304678570206959493 := by
  unfold tailWord_5828115
  simp only [CollatzResearch.WordTrace]
  refine ⟨212568817280742192642229799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141712544853828128428153199 212568817280742192642229799)
  ·
    refine ⟨318853225921113288963344699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212568817280742192642229799 318853225921113288963344699)
    ·
      refine ⟨478279838881669933445017049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318853225921113288963344699 478279838881669933445017049)
      ·
        refine ⟨358709879161252450083762787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478279838881669933445017049 358709879161252450083762787)
        ·
          refine ⟨538064818741878675125644181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358709879161252450083762787 538064818741878675125644181)
          ·
            refine ⟨25221788378525562896514571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 538064818741878675125644181 25221788378525562896514571)
            ·
              refine ⟨37832682567788344344771857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25221788378525562896514571 37832682567788344344771857)
              ·
                refine ⟨28374511925841258258578893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37832682567788344344771857 28374511925841258258578893)
                ·
                  refine ⟨10640441972190471846967085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28374511925841258258578893 10640441972190471846967085)
                  ·
                    refine ⟨3990165739571426942612657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10640441972190471846967085 3990165739571426942612657)
                    ·
                      refine ⟨2992624304678570206959493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990165739571426942612657 2992624304678570206959493)
                      ·
                        rfl

theorem cell23_5828115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3, 2].length) (baseStart_5828115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828115 prefixEnd_5828115 := by exact prefixLift 5828115
  have htrace : WordTrace (prefixWord ++ tailWord_5828115) baseStart_5828115 baseEnd_5828115 := by
    simpa [prefixWord, tailWord_5828115, baseEnd_5828115] using wordTrace_append hprefix tailTrace_5828115
  have hstable : (prefixWord ++ tailWord_5828115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828115).length < 2 ^ (prefixWord ++ tailWord_5828115).sum := by decide
  have hdescent : baseEnd_5828115 < baseStart_5828115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828138 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5828138 : Nat := 118140960795 + 5828138 * 2 ^ 59
def prefixEnd_5828138 : Nat := 4983230072969 + 3 ^ 40 * 5828138 * 2
def baseEnd_5828138 : Nat := 997545371577874538990629

theorem tailTrace_5828138 : CollatzResearch.WordTrace tailWord_5828138 prefixEnd_5828138 997545371577874538990629 := by
  unfold tailWord_5828138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53142414039914716892579267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141713104106439245046878045 53142414039914716892579267)
  ·
    refine ⟨79713621059872075338868901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53142414039914716892579267 79713621059872075338868901)
    ·
      refine ⟨14946303948726014126037919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79713621059872075338868901 14946303948726014126037919)
      ·
        refine ⟨22419455923089021189056879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14946303948726014126037919 22419455923089021189056879)
        ·
          refine ⟨33629183884633531783585319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22419455923089021189056879 33629183884633531783585319)
          ·
            refine ⟨50443775826950297675377979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33629183884633531783585319 50443775826950297675377979)
            ·
              refine ⟨75665663740425446513066969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50443775826950297675377979 75665663740425446513066969)
              ·
                refine ⟨56749247805319084884800227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75665663740425446513066969 56749247805319084884800227)
                ·
                  refine ⟨85123871707978627327200341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56749247805319084884800227 85123871707978627327200341)
                  ·
                    refine ⟨997545371577874538990629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85123871707978627327200341 997545371577874538990629)
                    ·
                      rfl

theorem cell23_5828138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5828138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828138 prefixEnd_5828138 := by exact prefixLift 5828138
  have htrace : WordTrace (prefixWord ++ tailWord_5828138) baseStart_5828138 baseEnd_5828138 := by
    simpa [prefixWord, tailWord_5828138, baseEnd_5828138] using wordTrace_append hprefix tailTrace_5828138
  have hstable : (prefixWord ++ tailWord_5828138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828138).length < 2 ^ (prefixWord ++ tailWord_5828138).sum := by decide
  have hdescent : baseEnd_5828138 < baseStart_5828138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828149 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_5828149 : Nat := 118140960795 + 5828149 * 2 ^ 59
def prefixEnd_5828149 : Nat := 4983230072969 + 3 ^ 40 * 5828149 * 2
def baseEnd_5828149 : Nat := 2992641763020823073934337

theorem tailTrace_5828149 : CollatzResearch.WordTrace tailWord_5828149 prefixEnd_5828149 2992641763020823073934337 := by
  unfold tailWord_5828149
  simp only [CollatzResearch.WordTrace]
  refine ⟨212570057362619016448967501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141713371575079344299311667 212570057362619016448967501)
  ·
    refine ⟨79713771510982131168362813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212570057362619016448967501 79713771510982131168362813)
    ·
      refine ⟨29892664316618299188136055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79713771510982131168362813 29892664316618299188136055)
      ·
        refine ⟨44838996474927448782204083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29892664316618299188136055 44838996474927448782204083)
        ·
          refine ⟨67258494712391173173306125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44838996474927448782204083 67258494712391173173306125)
          ·
            refine ⟨25221935517146689939989797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67258494712391173173306125 25221935517146689939989797)
            ·
              refine ⟨4729112909465004363748087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25221935517146689939989797 4729112909465004363748087)
              ·
                refine ⟨7093669364197506545622131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729112909465004363748087 7093669364197506545622131)
                ·
                  refine ⟨10640504046296259818433197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7093669364197506545622131 10640504046296259818433197)
                  ·
                    refine ⟨3990189017361097431912449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10640504046296259818433197 3990189017361097431912449)
                    ·
                      refine ⟨2992641763020823073934337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990189017361097431912449 2992641763020823073934337)
                      ·
                        rfl

theorem cell23_5828149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_5828149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828149 prefixEnd_5828149 := by exact prefixLift 5828149
  have htrace : WordTrace (prefixWord ++ tailWord_5828149) baseStart_5828149 baseEnd_5828149 := by
    simpa [prefixWord, tailWord_5828149, baseEnd_5828149] using wordTrace_append hprefix tailTrace_5828149
  have hstable : (prefixWord ++ tailWord_5828149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828149).length < 2 ^ (prefixWord ++ tailWord_5828149).sum := by decide
  have hdescent : baseEnd_5828149 < baseStart_5828149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828156 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_5828156 : Nat := 118140960795 + 5828156 * 2 ^ 59
def prefixEnd_5828156 : Nat := 4983230072969 + 3 ^ 40 * 5828156 * 2
def baseEnd_5828156 : Nat := 2992645357385404546546805

theorem tailTrace_5828156 : CollatzResearch.WordTrace tailWord_5828156 prefixEnd_5828156 2992645357385404546546805 := by
  unfold tailWord_5828156
  simp only [CollatzResearch.WordTrace]
  refine ⟨106285156336796828322236161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141713541782395771096314881 106285156336796828322236161)
  ·
    refine ⟨79713867252597621241677121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106285156336796828322236161 79713867252597621241677121)
    ·
      refine ⟨59785400439448215931257841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79713867252597621241677121 59785400439448215931257841)
      ·
        refine ⟨44839050329586161948443381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59785400439448215931257841 44839050329586161948443381)
        ·
          refine ⟨4203660968398702682666567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44839050329586161948443381 4203660968398702682666567)
          ·
            refine ⟨6305491452598054023999851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203660968398702682666567 6305491452598054023999851)
            ·
              refine ⟨9458237178897081035999777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305491452598054023999851 9458237178897081035999777)
              ·
                refine ⟨7093677884172810776999833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9458237178897081035999777 7093677884172810776999833)
                ·
                  refine ⟨5320258413129608082749875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7093677884172810776999833 5320258413129608082749875)
                  ·
                    refine ⟨7980387619694412124124813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5320258413129608082749875 7980387619694412124124813)
                    ·
                      refine ⟨2992645357385404546546805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7980387619694412124124813 2992645357385404546546805)
                      ·
                        rfl

theorem cell23_5828156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_5828156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828156 prefixEnd_5828156 := by exact prefixLift 5828156
  have htrace : WordTrace (prefixWord ++ tailWord_5828156) baseStart_5828156 baseEnd_5828156 := by
    simpa [prefixWord, tailWord_5828156, baseEnd_5828156] using wordTrace_append hprefix tailTrace_5828156
  have hstable : (prefixWord ++ tailWord_5828156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828156).length < 2 ^ (prefixWord ++ tailWord_5828156).sum := by decide
  have hdescent : baseEnd_5828156 < baseStart_5828156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828202 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_5828202 : Nat := 118140960795 + 5828202 * 2 ^ 59
def prefixEnd_5828202 : Nat := 4983230072969 + 3 ^ 40 * 5828202 * 2
def baseEnd_5828202 : Nat := 332518775277279040730177

theorem tailTrace_5828202 : CollatzResearch.WordTrace tailWord_5828202 prefixEnd_5828202 332518775277279040730177 := by
  unfold tailWord_5828202
  simp only [CollatzResearch.WordTrace]
  refine ⟨53142997607856751625161715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141714660287618004333764573 53142997607856751625161715)
  ·
    refine ⟨79714496411785127437742573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53142997607856751625161715 79714496411785127437742573)
    ·
      refine ⟨29892936154419422789153465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79714496411785127437742573 29892936154419422789153465)
      ·
        refine ⟨22419702115814567091865099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29892936154419422789153465 22419702115814567091865099)
        ·
          refine ⟨33629553173721850637797649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22419702115814567091865099 33629553173721850637797649)
          ·
            refine ⟨25222164880291387978348237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33629553173721850637797649 25222164880291387978348237)
            ·
              refine ⟨9458311830109270491880589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25222164880291387978348237 9458311830109270491880589)
              ·
                refine ⟨3546866936290976434455221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458311830109270491880589 3546866936290976434455221)
                ·
                  refine ⟨332518775277279040730177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3546866936290976434455221 332518775277279040730177)
                  ·
                    rfl

theorem cell23_5828202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_5828202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828202 prefixEnd_5828202 := by exact prefixLift 5828202
  have htrace : WordTrace (prefixWord ++ tailWord_5828202) baseStart_5828202 baseEnd_5828202 := by
    simpa [prefixWord, tailWord_5828202, baseEnd_5828202] using wordTrace_append hprefix tailTrace_5828202
  have hstable : (prefixWord ++ tailWord_5828202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828202).length < 2 ^ (prefixWord ++ tailWord_5828202).sum := by decide
  have hdescent : baseEnd_5828202 < baseStart_5828202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828218 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_5828218 : Nat := 118140960795 + 5828218 * 2 ^ 59
def prefixEnd_5828218 : Nat := 4983230072969 + 3 ^ 40 * 5828218 * 2
def baseEnd_5828218 : Nat := 2992677193185983303971519

theorem tailTrace_5828218 : CollatzResearch.WordTrace tailWord_5828218 prefixEnd_5828218 2992677193185983303971519 := by
  unfold tailWord_5828218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53143143499842260308307327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141715049332912694155486205 53143143499842260308307327)
  ·
    refine ⟨79714715249763390462460991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53143143499842260308307327 79714715249763390462460991)
    ·
      refine ⟨119572072874645085693691487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79714715249763390462460991 119572072874645085693691487)
      ·
        refine ⟨179358109311967628540537231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119572072874645085693691487 179358109311967628540537231)
        ·
          refine ⟨269037163967951442810805847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179358109311967628540537231 269037163967951442810805847)
          ·
            refine ⟨403555745951927164216208771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269037163967951442810805847 403555745951927164216208771)
            ·
              refine ⟨605333618927890746324313157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403555745951927164216208771 605333618927890746324313157)
              ·
                refine ⟨113500053548979514935808717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605333618927890746324313157 113500053548979514935808717)
                ·
                  refine ⟨42562520080867318100928269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113500053548979514935808717 42562520080867318100928269)
                  ·
                    refine ⟨15960945030325244287848101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42562520080867318100928269 15960945030325244287848101)
                    ·
                      refine ⟨2992677193185983303971519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15960945030325244287848101 2992677193185983303971519)
                      ·
                        rfl

theorem cell23_5828218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_5828218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828218 prefixEnd_5828218 := by exact prefixLift 5828218
  have htrace : WordTrace (prefixWord ++ tailWord_5828218) baseStart_5828218 baseEnd_5828218 := by
    simpa [prefixWord, tailWord_5828218, baseEnd_5828218] using wordTrace_append hprefix tailTrace_5828218
  have hstable : (prefixWord ++ tailWord_5828218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828218).length < 2 ^ (prefixWord ++ tailWord_5828218).sum := by decide
  have hdescent : baseEnd_5828218 < baseStart_5828218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828225 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5828225 : Nat := 118140960795 + 5828225 * 2 ^ 59
def prefixEnd_5828225 : Nat := 4983230072969 + 3 ^ 40 * 5828225 * 2
def baseEnd_5828225 : Nat := 2992680787550564776583987

theorem tailTrace_5828225 : CollatzResearch.WordTrace tailWord_5828225 prefixEnd_5828225 2992680787550564776583987 := by
  unfold tailWord_5828225
  simp only [CollatzResearch.WordTrace]
  refine ⟨212572829310343681428734129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141715219540229120952489419 212572829310343681428734129)
  ·
    refine ⟨159429621982757761071550597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212572829310343681428734129 159429621982757761071550597)
    ·
      refine ⟨29893054121767080200915737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159429621982757761071550597 29893054121767080200915737)
      ·
        refine ⟨22419790591325310150686803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29893054121767080200915737 22419790591325310150686803)
        ·
          refine ⟨33629685886987965226030205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22419790591325310150686803 33629685886987965226030205)
          ·
            refine ⟨12611132207620486959761327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33629685886987965226030205 12611132207620486959761327)
            ·
              refine ⟨18916698311430730439641991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611132207620486959761327 18916698311430730439641991)
              ·
                refine ⟨28375047467146095659462987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18916698311430730439641991 28375047467146095659462987)
                ·
                  refine ⟨42562571200719143489194481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28375047467146095659462987 42562571200719143489194481)
                  ·
                    refine ⟨31921928400539357616895861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42562571200719143489194481 31921928400539357616895861)
                    ·
                      refine ⟨2992680787550564776583987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31921928400539357616895861 2992680787550564776583987)
                      ·
                        rfl

theorem cell23_5828225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5828225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828225 prefixEnd_5828225 := by exact prefixLift 5828225
  have htrace : WordTrace (prefixWord ++ tailWord_5828225) baseStart_5828225 baseEnd_5828225 := by
    simpa [prefixWord, tailWord_5828225, baseEnd_5828225] using wordTrace_append hprefix tailTrace_5828225
  have hstable : (prefixWord ++ tailWord_5828225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828225).length < 2 ^ (prefixWord ++ tailWord_5828225).sum := by decide
  have hdescent : baseEnd_5828225 < baseStart_5828225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828235 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 6, 2]
def baseStart_5828235 : Nat := 118140960795 + 5828235 * 2 ^ 59
def prefixEnd_5828235 : Nat := 4983230072969 + 3 ^ 40 * 5828235 * 2
def baseEnd_5828235 : Nat := 2992685922357109737458941

theorem tailTrace_5828235 : CollatzResearch.WordTrace tailWord_5828235 prefixEnd_5828235 2992685922357109737458941 := by
  unfold tailWord_5828235
  simp only [CollatzResearch.WordTrace]
  refine ⟨212573194040307453136598159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141715462693538302091065439 212573194040307453136598159)
  ·
    refine ⟨318859791060461179704897239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212573194040307453136598159 318859791060461179704897239)
    ·
      refine ⟨478289686590691769557345859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318859791060461179704897239 478289686590691769557345859)
      ·
        refine ⟨717434529886037654336018789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478289686590691769557345859 717434529886037654336018789)
        ·
          refine ⟨134518974353632060188003523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 717434529886037654336018789 134518974353632060188003523)
          ·
            refine ⟨201778461530448090282005285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134518974353632060188003523 201778461530448090282005285)
            ·
              refine ⟨37833461536959016927875991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201778461530448090282005285 37833461536959016927875991)
              ·
                refine ⟨56750192305438525391813987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37833461536959016927875991 56750192305438525391813987)
                ·
                  refine ⟨85125288458157788087720981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56750192305438525391813987 85125288458157788087720981)
                  ·
                    refine ⟨3990247896476146316611921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85125288458157788087720981 3990247896476146316611921)
                    ·
                      refine ⟨2992685922357109737458941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990247896476146316611921 2992685922357109737458941)
                      ·
                        rfl

theorem cell23_5828235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6, 2].length) (baseStart_5828235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828235 prefixEnd_5828235 := by exact prefixLift 5828235
  have htrace : WordTrace (prefixWord ++ tailWord_5828235) baseStart_5828235 baseEnd_5828235 := by
    simpa [prefixWord, tailWord_5828235, baseEnd_5828235] using wordTrace_append hprefix tailTrace_5828235
  have hstable : (prefixWord ++ tailWord_5828235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828235).length < 2 ^ (prefixWord ++ tailWord_5828235).sum := by decide
  have hdescent : baseEnd_5828235 < baseStart_5828235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828245 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_5828245 : Nat := 118140960795 + 5828245 * 2 ^ 59
def prefixEnd_5828245 : Nat := 4983230072969 + 3 ^ 40 * 5828245 * 2
def baseEnd_5828245 : Nat := 997563685721218232777965

theorem tailTrace_5828245 : CollatzResearch.WordTrace tailWord_5828245 prefixEnd_5828245 997563685721218232777965 := by
  unfold tailWord_5828245
  simp only [CollatzResearch.WordTrace]
  refine ⟨212573558770271224844462189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141715705846847483229641459 212573558770271224844462189)
  ·
    refine ⟨79715084538851709316673321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212573558770271224844462189 79715084538851709316673321)
    ·
      refine ⟨59786313404138781987504991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79715084538851709316673321 59786313404138781987504991)
      ·
        refine ⟨89679470106208172981257487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59786313404138781987504991 89679470106208172981257487)
        ·
          refine ⟨134519205159312259471886231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89679470106208172981257487 134519205159312259471886231)
          ·
            refine ⟨201778807738968389207829347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134519205159312259471886231 201778807738968389207829347)
            ·
              refine ⟨302668211608452583811744021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201778807738968389207829347 302668211608452583811744021)
              ·
                refine ⟨14187572419146214866175501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302668211608452583811744021 14187572419146214866175501)
                ·
                  refine ⟨5320339657179830574815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14187572419146214866175501 5320339657179830574815813)
                  ·
                    refine ⟨997563685721218232777965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320339657179830574815813 997563685721218232777965)
                    ·
                      rfl

theorem cell23_5828245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_5828245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828245 prefixEnd_5828245 := by exact prefixLift 5828245
  have htrace : WordTrace (prefixWord ++ tailWord_5828245) baseStart_5828245 baseEnd_5828245 := by
    simpa [prefixWord, tailWord_5828245, baseEnd_5828245] using wordTrace_append hprefix tailTrace_5828245
  have hstable : (prefixWord ++ tailWord_5828245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828245).length < 2 ^ (prefixWord ++ tailWord_5828245).sum := by decide
  have hdescent : baseEnd_5828245 < baseStart_5828245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828275 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 6]
def baseStart_5828275 : Nat := 118140960795 + 5828275 * 2 ^ 59
def prefixEnd_5828275 : Nat := 4983230072969 + 3 ^ 40 * 5828275 * 2
def baseEnd_5828275 : Nat := 332522940175921064550973

theorem tailTrace_5828275 : CollatzResearch.WordTrace tailWord_5828275 prefixEnd_5828275 332522940175921064550973 := by
  unfold tailWord_5828275
  simp only [CollatzResearch.WordTrace]
  refine ⟨212574652960162539968054279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141716435306775026645369519 212574652960162539968054279)
  ·
    refine ⟨318861979440243809952081419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212574652960162539968054279 318861979440243809952081419)
    ·
      refine ⟨478292969160365714928122129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318861979440243809952081419 478292969160365714928122129)
      ·
        refine ⟨358719726870274286196091597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478292969160365714928122129 358719726870274286196091597)
        ·
          refine ⟨134519897576352857323534349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358719726870274286196091597 134519897576352857323534349)
          ·
            refine ⟨50444961591132321496325381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134519897576352857323534349 50444961591132321496325381)
            ·
              refine ⟨9458430298337310280561009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50444961591132321496325381 9458430298337310280561009)
              ·
                refine ⟨7093822723752982710420757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9458430298337310280561009 7093822723752982710420757)
                ·
                  refine ⟨332522940175921064550973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7093822723752982710420757 332522940175921064550973)
                  ·
                    rfl

theorem cell23_5828275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 6].length) (baseStart_5828275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828275 prefixEnd_5828275 := by exact prefixLift 5828275
  have htrace : WordTrace (prefixWord ++ tailWord_5828275) baseStart_5828275 baseEnd_5828275 := by
    simpa [prefixWord, tailWord_5828275, baseEnd_5828275] using wordTrace_append hprefix tailTrace_5828275
  have hstable : (prefixWord ++ tailWord_5828275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828275).length < 2 ^ (prefixWord ++ tailWord_5828275).sum := by decide
  have hdescent : baseEnd_5828275 < baseStart_5828275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828279 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 1, 4]
def baseStart_5828279 : Nat := 118140960795 + 5828279 * 2 ^ 59
def prefixEnd_5828279 : Nat := 4983230072969 + 3 ^ 40 * 5828279 * 2
def baseEnd_5828279 : Nat := 997569505168635855102913

theorem tailTrace_5828279 : CollatzResearch.WordTrace tailWord_5828279 prefixEnd_5828279 997569505168635855102913 := by
  unfold tailWord_5828279
  simp only [CollatzResearch.WordTrace]
  refine ⟨212574798852148048651199891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141716532568098699100799927 212574798852148048651199891)
  ·
    refine ⟨318862198278222072976799837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212574798852148048651199891 318862198278222072976799837)
    ·
      refine ⟨119573324354333277366299939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318862198278222072976799837 119573324354333277366299939)
      ·
        refine ⟨179359986531499916049449909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119573324354333277366299939 179359986531499916049449909)
        ·
          refine ⟨16814998737328117129635929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179359986531499916049449909 16814998737328117129635929)
          ·
            refine ⟨12611249052996087847226947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16814998737328117129635929 12611249052996087847226947)
            ·
              refine ⟨18916873579494131770840421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611249052996087847226947 18916873579494131770840421)
              ·
                refine ⟨3546913796155149707032579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18916873579494131770840421 3546913796155149707032579)
                ·
                  refine ⟨5320370694232724560548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546913796155149707032579 5320370694232724560548869)
                  ·
                    refine ⟨997569505168635855102913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320370694232724560548869 997569505168635855102913)
                    ·
                      rfl

theorem cell23_5828279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_5828279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828279 prefixEnd_5828279 := by exact prefixLift 5828279
  have htrace : WordTrace (prefixWord ++ tailWord_5828279) baseStart_5828279 baseEnd_5828279 := by
    simpa [prefixWord, tailWord_5828279, baseEnd_5828279] using wordTrace_append hprefix tailTrace_5828279
  have hstable : (prefixWord ++ tailWord_5828279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828279).length < 2 ^ (prefixWord ++ tailWord_5828279).sum := by decide
  have hdescent : baseEnd_5828279 < baseStart_5828279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828305 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_5828305 : Nat := 118140960795 + 5828305 * 2 ^ 59
def prefixEnd_5828305 : Nat := 4983230072969 + 3 ^ 40 * 5828305 * 2
def baseEnd_5828305 : Nat := 997573955334308154527873

theorem tailTrace_5828305 : CollatzResearch.WordTrace tailWord_5828305 prefixEnd_5828305 997573955334308154527873 := by
  unfold tailWord_5828305
  simp only [CollatzResearch.WordTrace]
  refine ⟨212575747150053855091646369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141717164766702570061097579 212575747150053855091646369)
  ·
    refine ⟨159431810362540391318734777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212575747150053855091646369 159431810362540391318734777)
    ·
      refine ⟨119573857771905293489051083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159431810362540391318734777 119573857771905293489051083)
      ·
        refine ⟨179360786657857940233576625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119573857771905293489051083 179360786657857940233576625)
        ·
          refine ⟨134520589993393455175182469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179360786657857940233576625 134520589993393455175182469)
          ·
            refine ⟨25222610623761272845346713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134520589993393455175182469 25222610623761272845346713)
            ·
              refine ⟨18916957967820954634010035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25222610623761272845346713 18916957967820954634010035)
              ·
                refine ⟨28375436951731431951015053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18916957967820954634010035 28375436951731431951015053)
                ·
                  refine ⟨10640788856899286981630645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28375436951731431951015053 10640788856899286981630645)
                  ·
                    refine ⟨997573955334308154527873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10640788856899286981630645 997573955334308154527873)
                    ·
                      rfl

theorem cell23_5828305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_5828305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828305 prefixEnd_5828305 := by exact prefixLift 5828305
  have htrace : WordTrace (prefixWord ++ tailWord_5828305) baseStart_5828305 baseEnd_5828305 := by
    simpa [prefixWord, tailWord_5828305, baseEnd_5828305] using wordTrace_append hprefix tailTrace_5828305
  have hstable : (prefixWord ++ tailWord_5828305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828305).length < 2 ^ (prefixWord ++ tailWord_5828305).sum := by decide
  have hdescent : baseEnd_5828305 < baseStart_5828305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828312 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_5828312 : Nat := 118140960795 + 5828312 * 2 ^ 59
def prefixEnd_5828312 : Nat := 4983230072969 + 3 ^ 40 * 5828312 * 2
def baseEnd_5828312 : Nat := 2992725460367505936196087

theorem tailTrace_5828312 : CollatzResearch.WordTrace tailWord_5828312 prefixEnd_5828312 2992725460367505936196087 := by
  unfold tailWord_5828312
  simp only [CollatzResearch.WordTrace]
  refine ⟨106288001230514247643575595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141717334974018996858100793 106288001230514247643575595)
  ·
    refine ⟨159432001845771371465363393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106288001230514247643575595 159432001845771371465363393)
    ·
      refine ⟨119574001384328528599022545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159432001845771371465363393 119574001384328528599022545)
      ·
        refine ⟨89680501038246396449266909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119574001384328528599022545 89680501038246396449266909)
        ·
          refine ⟨33630187889342398668475091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89680501038246396449266909 33630187889342398668475091)
          ·
            refine ⟨50445281834013598002712637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33630187889342398668475091 50445281834013598002712637)
            ·
              refine ⟨18916980687755099251017239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50445281834013598002712637 18916980687755099251017239)
              ·
                refine ⟨28375471031632648876525859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18916980687755099251017239 28375471031632648876525859)
                ·
                  refine ⟨42563206547448973314788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28375471031632648876525859 42563206547448973314788789)
                  ·
                    refine ⟨3990300613823341248261449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42563206547448973314788789 3990300613823341248261449)
                    ·
                      refine ⟨2992725460367505936196087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990300613823341248261449 2992725460367505936196087)
                      ·
                        rfl

theorem cell23_5828312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_5828312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828312 prefixEnd_5828312 := by exact prefixLift 5828312
  have htrace : WordTrace (prefixWord ++ tailWord_5828312) baseStart_5828312 baseEnd_5828312 := by
    simpa [prefixWord, tailWord_5828312, baseEnd_5828312] using wordTrace_append hprefix tailTrace_5828312
  have hstable : (prefixWord ++ tailWord_5828312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828312).length < 2 ^ (prefixWord ++ tailWord_5828312).sum := by decide
  have hdescent : baseEnd_5828312 < baseStart_5828312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828370 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5828370 : Nat := 118140960795 + 5828370 * 2 ^ 59
def prefixEnd_5828370 : Nat := 4983230072969 + 3 ^ 40 * 5828370 * 2
def baseEnd_5828370 : Nat := 2992755242245466709270821

theorem tailTrace_5828370 : CollatzResearch.WordTrace tailWord_5828370 prefixEnd_5828370 2992755242245466709270821 := by
  unfold tailWord_5828370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53144529473704592798190641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141718745263212247461841709 53144529473704592798190641)
  ·
    refine ⟨39858397105278444598642981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53144529473704592798190641 39858397105278444598642981)
    ·
      refine ⟨7473449457239708362245559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39858397105278444598642981 7473449457239708362245559)
      ·
        refine ⟨11210174185859562543368339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473449457239708362245559 11210174185859562543368339)
        ·
          refine ⟨16815261278789343815052509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210174185859562543368339 16815261278789343815052509)
          ·
            refine ⟨6305722979546003930644691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16815261278789343815052509 6305722979546003930644691)
            ·
              refine ⟨9458584469319005895967037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305722979546003930644691 9458584469319005895967037)
              ·
                refine ⟨3546969175994627210987639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458584469319005895967037 3546969175994627210987639)
                ·
                  refine ⟨5320453763991940816481459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546969175994627210987639 5320453763991940816481459)
                  ·
                    refine ⟨7980680645987911224722189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5320453763991940816481459 7980680645987911224722189)
                    ·
                      refine ⟨2992755242245466709270821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7980680645987911224722189 2992755242245466709270821)
                      ·
                        rfl

theorem cell23_5828370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5828370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828370 prefixEnd_5828370 := by exact prefixLift 5828370
  have htrace : WordTrace (prefixWord ++ tailWord_5828370) baseStart_5828370 baseEnd_5828370 := by
    simpa [prefixWord, tailWord_5828370, baseEnd_5828370] using wordTrace_append hprefix tailTrace_5828370
  have hstable : (prefixWord ++ tailWord_5828370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828370).length < 2 ^ (prefixWord ++ tailWord_5828370).sum := by decide
  have hdescent : baseEnd_5828370 < baseStart_5828370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828403 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 2, 4]
def baseStart_5828403 : Nat := 118140960795 + 5828403 * 2 ^ 59
def prefixEnd_5828403 : Nat := 4983230072969 + 3 ^ 40 * 5828403 * 2
def baseEnd_5828403 : Nat := 997590729035688360052723

theorem tailTrace_5828403 : CollatzResearch.WordTrace tailWord_5828403 prefixEnd_5828403 997590729035688360052723 := by
  unfold tailWord_5828403
  simp only [CollatzResearch.WordTrace]
  refine ⟨212579321503698817828713863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141719547669132545219142575 212579321503698817828713863)
  ·
    refine ⟨318868982255548226743070795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212579321503698817828713863 318868982255548226743070795)
    ·
      refine ⟨478303473383322340114606193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318868982255548226743070795 478303473383322340114606193)
      ·
        refine ⟨358727605037491755085954645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478303473383322340114606193 358727605037491755085954645)
        ·
          refine ⟨4203839121533106504913531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 358727605037491755085954645 4203839121533106504913531)
          ·
            refine ⟨6305758682299659757370297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203839121533106504913531 6305758682299659757370297)
            ·
              refine ⟨4729319011724744818027723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305758682299659757370297 4729319011724744818027723)
              ·
                refine ⟨7093978517587117227041585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729319011724744818027723 7093978517587117227041585)
                ·
                  refine ⟨5320483888190337920281189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7093978517587117227041585 5320483888190337920281189)
                  ·
                    refine ⟨997590729035688360052723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320483888190337920281189 997590729035688360052723)
                    ·
                      rfl

theorem cell23_5828403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 4].length) (baseStart_5828403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828403 prefixEnd_5828403 := by exact prefixLift 5828403
  have htrace : WordTrace (prefixWord ++ tailWord_5828403) baseStart_5828403 baseEnd_5828403 := by
    simpa [prefixWord, tailWord_5828403, baseEnd_5828403] using wordTrace_append hprefix tailTrace_5828403
  have hstable : (prefixWord ++ tailWord_5828403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828403).length < 2 ^ (prefixWord ++ tailWord_5828403).sum := by decide
  have hdescent : baseEnd_5828403 < baseStart_5828403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828419 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 3, 3, 2]
def baseStart_5828419 : Nat := 118140960795 + 5828419 * 2 ^ 59
def prefixEnd_5828419 : Nat := 4983230072969 + 3 ^ 40 * 5828419 * 2
def baseEnd_5828419 : Nat := 2992780402797537017558095

theorem tailTrace_5828419 : CollatzResearch.WordTrace tailWord_5828419 prefixEnd_5828419 2992780402797537017558095 := by
  unfold tailWord_5828419
  simp only [CollatzResearch.WordTrace]
  refine ⟨212579905071640852561296311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141719936714427235040864207 212579905071640852561296311)
  ·
    refine ⟨318869857607461278841944467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212579905071640852561296311 318869857607461278841944467)
    ·
      refine ⟨478304786411191918262916701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318869857607461278841944467 478304786411191918262916701)
      ·
        refine ⟨179364294904196969348593763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478304786411191918262916701 179364294904196969348593763)
        ·
          refine ⟨269046442356295454022890645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179364294904196969348593763 269046442356295454022890645)
          ·
            refine ⟨12611551985451349407322999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269046442356295454022890645 12611551985451349407322999)
            ·
              refine ⟨18917327978177024110984499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611551985451349407322999 18917327978177024110984499)
              ·
                refine ⟨28375991967265536166476749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18917327978177024110984499 28375991967265536166476749)
                ·
                  refine ⟨10640996987724576062428781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28375991967265536166476749 10640996987724576062428781)
                  ·
                    refine ⟨3990373870396716023410793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10640996987724576062428781 3990373870396716023410793)
                    ·
                      refine ⟨2992780402797537017558095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990373870396716023410793 2992780402797537017558095)
                      ·
                        rfl

theorem cell23_5828419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_5828419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828419 prefixEnd_5828419 := by exact prefixLift 5828419
  have htrace : WordTrace (prefixWord ++ tailWord_5828419) baseStart_5828419 baseEnd_5828419 := by
    simpa [prefixWord, tailWord_5828419, baseEnd_5828419] using wordTrace_append hprefix tailTrace_5828419
  have hstable : (prefixWord ++ tailWord_5828419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828419).length < 2 ^ (prefixWord ++ tailWord_5828419).sum := by decide
  have hdescent : baseEnd_5828419 < baseStart_5828419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828444 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5828444 : Nat := 118140960795 + 5828444 * 2 ^ 59
def prefixEnd_5828444 : Nat := 4983230072969 + 3 ^ 40 * 5828444 * 2
def baseEnd_5828444 : Nat := 2992793239813899419745481

theorem tailTrace_5828444 : CollatzResearch.WordTrace tailWord_5828444 prefixEnd_5828444 2992793239813899419745481 := by
  unfold tailWord_5828444
  simp only [CollatzResearch.WordTrace]
  refine ⟨106290408448275140915478193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141720544597700187887304257 106290408448275140915478193)
  ·
    refine ⟨79717806336206355686608645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106290408448275140915478193 79717806336206355686608645)
    ·
      refine ⟨14947088688038691691239121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79717806336206355686608645 14947088688038691691239121)
      ·
        refine ⟨11210316516029018768429341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14947088688038691691239121 11210316516029018768429341)
        ·
          refine ⟨4203868693510882038161003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11210316516029018768429341 4203868693510882038161003)
          ·
            refine ⟨6305803040266323057241505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203868693510882038161003 6305803040266323057241505)
            ·
              refine ⟨4729352280199742292931129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305803040266323057241505 4729352280199742292931129)
              ·
                refine ⟨3547014210149806719698347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4729352280199742292931129 3547014210149806719698347)
                ·
                  refine ⟨5320521315224710079547521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547014210149806719698347 5320521315224710079547521)
                  ·
                    refine ⟨3990390986418532559660641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320521315224710079547521 3990390986418532559660641)
                    ·
                      refine ⟨2992793239813899419745481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990390986418532559660641 2992793239813899419745481)
                      ·
                        rfl

theorem cell23_5828444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5828444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828444 prefixEnd_5828444 := by exact prefixLift 5828444
  have htrace : WordTrace (prefixWord ++ tailWord_5828444) baseStart_5828444 baseEnd_5828444 := by
    simpa [prefixWord, tailWord_5828444, baseEnd_5828444] using wordTrace_append hprefix tailTrace_5828444
  have hstable : (prefixWord ++ tailWord_5828444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828444).length < 2 ^ (prefixWord ++ tailWord_5828444).sum := by decide
  have hdescent : baseEnd_5828444 < baseStart_5828444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828489 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 5]
def baseStart_5828489 : Nat := 118140960795 + 5828489 * 2 ^ 59
def prefixEnd_5828489 : Nat := 4983230072969 + 3 ^ 40 * 5828489 * 2
def baseEnd_5828489 : Nat := 332535149604816860409197

theorem tailTrace_5828489 : CollatzResearch.WordTrace tailWord_5828489 prefixEnd_5828489 332535149604816860409197 := by
  unfold tailWord_5828489
  simp only [CollatzResearch.WordTrace]
  refine ⟨212582458181387254516344521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141721638787591503010896347 212582458181387254516344521)
  ·
    refine ⟨159436843636040440887258391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212582458181387254516344521 159436843636040440887258391)
    ·
      refine ⟨239155265454060661330887587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159436843636040440887258391 239155265454060661330887587)
      ·
        refine ⟨358732898181090991996331381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239155265454060661330887587 358732898181090991996331381)
        ·
          refine ⟨33631209204477280499656067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 358732898181090991996331381 33631209204477280499656067)
          ·
            refine ⟨50446813806715920749484101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33631209204477280499656067 50446813806715920749484101)
            ·
              refine ⟨9458777588759235140528269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50446813806715920749484101 9458777588759235140528269)
              ·
                refine ⟨3547041595784713177698101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458777588759235140528269 3547041595784713177698101)
                ·
                  refine ⟨332535149604816860409197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3547041595784713177698101 332535149604816860409197)
                  ·
                    rfl

theorem cell23_5828489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 5].length) (baseStart_5828489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828489 prefixEnd_5828489 := by exact prefixLift 5828489
  have htrace : WordTrace (prefixWord ++ tailWord_5828489) baseStart_5828489 baseEnd_5828489 := by
    simpa [prefixWord, tailWord_5828489, baseEnd_5828489] using wordTrace_append hprefix tailTrace_5828489
  have hstable : (prefixWord ++ tailWord_5828489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828489).length < 2 ^ (prefixWord ++ tailWord_5828489).sum := by decide
  have hdescent : baseEnd_5828489 < baseStart_5828489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828500 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5828500 : Nat := 118140960795 + 5828500 * 2 ^ 59
def prefixEnd_5828500 : Nat := 4983230072969 + 3 ^ 40 * 5828500 * 2
def baseEnd_5828500 : Nat := 2992821994730551200645223

theorem tailTrace_5828500 : CollatzResearch.WordTrace tailWord_5828500 prefixEnd_5828500 2992821994730551200645223 := by
  unfold tailWord_5828500
  simp only [CollatzResearch.WordTrace]
  refine ⟨106291429692173701697497477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141721906256231602263329969 106291429692173701697497477)
  ·
    refine ⟨19929643067282569068280777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106291429692173701697497477 19929643067282569068280777)
    ·
      refine ⟨14947232300461926801210583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19929643067282569068280777 14947232300461926801210583)
      ·
        refine ⟨22420848450692890201815875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14947232300461926801210583 22420848450692890201815875)
        ·
          refine ⟨33631272676039335302723813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22420848450692890201815875 33631272676039335302723813)
          ·
            refine ⟨6305863626757375369260715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33631272676039335302723813 6305863626757375369260715)
            ·
              refine ⟨9458795440136063053891073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305863626757375369260715 9458795440136063053891073)
              ·
                refine ⟨7094096580102047290418305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9458795440136063053891073 7094096580102047290418305)
                ·
                  refine ⟨5320572435076535467813729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7094096580102047290418305 5320572435076535467813729)
                  ·
                    refine ⟨3990429326307401600860297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320572435076535467813729 3990429326307401600860297)
                    ·
                      refine ⟨2992821994730551200645223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990429326307401600860297 2992821994730551200645223)
                      ·
                        rfl

theorem cell23_5828500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5828500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828500 prefixEnd_5828500 := by exact prefixLift 5828500
  have htrace : WordTrace (prefixWord ++ tailWord_5828500) baseStart_5828500 baseEnd_5828500 := by
    simpa [prefixWord, tailWord_5828500, baseEnd_5828500] using wordTrace_append hprefix tailTrace_5828500
  have hstable : (prefixWord ++ tailWord_5828500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828500).length < 2 ^ (prefixWord ++ tailWord_5828500).sum := by decide
  have hdescent : baseEnd_5828500 < baseStart_5828500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828540 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 5]
def baseStart_5828540 : Nat := 118140960795 + 5828540 * 2 ^ 59
def prefixEnd_5828540 : Nat := 4983230072969 + 3 ^ 40 * 5828540 * 2
def baseEnd_5828540 : Nat := 332538059328525671571671

theorem tailTrace_5828540 : CollatzResearch.WordTrace tailWord_5828540 prefixEnd_5828540 332538059328525671571671 := by
  unfold tailWord_5828540
  simp only [CollatzResearch.WordTrace]
  refine ⟨106292159152101245113225537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141722878869468326817634049 106292159152101245113225537)
  ·
    refine ⟨79719119364075933834919153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106292159152101245113225537 79719119364075933834919153)
    ·
      refine ⟨59789339523056950376189365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79719119364075933834919153 59789339523056950376189365)
      ·
        refine ⟨5605250580286589097767753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59789339523056950376189365 5605250580286589097767753)
        ·
          refine ⟨4203937935214941823325815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605250580286589097767753 4203937935214941823325815)
          ·
            refine ⟨6305906902822412734988723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203937935214941823325815 6305906902822412734988723)
            ·
              refine ⟨9458860354233619102483085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305906902822412734988723 9458860354233619102483085)
              ·
                refine ⟨3547072632837607163431157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458860354233619102483085 3547072632837607163431157)
                ·
                  refine ⟨332538059328525671571671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3547072632837607163431157 332538059328525671571671)
                  ·
                    rfl

theorem cell23_5828540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_5828540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828540 prefixEnd_5828540 := by exact prefixLift 5828540
  have htrace : WordTrace (prefixWord ++ tailWord_5828540) baseStart_5828540 baseEnd_5828540 := by
    simpa [prefixWord, tailWord_5828540, baseEnd_5828540] using wordTrace_append hprefix tailTrace_5828540
  have hstable : (prefixWord ++ tailWord_5828540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828540).length < 2 ^ (prefixWord ++ tailWord_5828540).sum := by decide
  have hdescent : baseEnd_5828540 < baseStart_5828540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828559 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_5828559 : Nat := 118140960795 + 5828559 * 2 ^ 59
def prefixEnd_5828559 : Nat := 4983230072969 + 3 ^ 40 * 5828559 * 2
def baseEnd_5828559 : Nat := 2992852290089166469807451

theorem tailTrace_5828559 : CollatzResearch.WordTrace tailWord_5828559 prefixEnd_5828559 2992852290089166469807451 := by
  unfold tailWord_5828559
  simp only [CollatzResearch.WordTrace]
  refine ⟨212585011291133656471392731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141723340860755770980928487 212585011291133656471392731)
  ·
    refine ⟨318877516936700484707089097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212585011291133656471392731 318877516936700484707089097)
    ·
      refine ⟨239158137702525363530316823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318877516936700484707089097 239158137702525363530316823)
      ·
        refine ⟨358737206553788045295475235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239158137702525363530316823 358737206553788045295475235)
        ·
          refine ⟨538105809830682067943212853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358737206553788045295475235 538105809830682067943212853)
          ·
            refine ⟨50447419671626443869676205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 538105809830682067943212853 50447419671626443869676205)
            ·
              refine ⟨18917782376859916451128577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50447419671626443869676205 18917782376859916451128577)
              ·
                refine ⟨14188336782644937338346433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18917782376859916451128577 14188336782644937338346433)
                ·
                  refine ⟨10641252586983703003759825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14188336782644937338346433 10641252586983703003759825)
                  ·
                    refine ⟨7980939440237777252819869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10641252586983703003759825 7980939440237777252819869)
                    ·
                      refine ⟨2992852290089166469807451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7980939440237777252819869 2992852290089166469807451)
                      ·
                        rfl

theorem cell23_5828559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_5828559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828559 prefixEnd_5828559 := by exact prefixLift 5828559
  have htrace : WordTrace (prefixWord ++ tailWord_5828559) baseStart_5828559 baseEnd_5828559 := by
    simpa [prefixWord, tailWord_5828559, baseEnd_5828559] using wordTrace_append hprefix tailTrace_5828559
  have hstable : (prefixWord ++ tailWord_5828559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828559).length < 2 ^ (prefixWord ++ tailWord_5828559).sum := by decide
  have hdescent : baseEnd_5828559 < baseStart_5828559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828579 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 6]
def baseStart_5828579 : Nat := 118140960795 + 5828579 * 2 ^ 59
def prefixEnd_5828579 : Nat := 4983230072969 + 3 ^ 40 * 5828579 * 2
def baseEnd_5828579 : Nat := 332540284411361821284151

theorem tailTrace_5828579 : CollatzResearch.WordTrace tailWord_5828579 prefixEnd_5828579 332540284411361821284151 := by
  unfold tailWord_5828579
  simp only [CollatzResearch.WordTrace]
  refine ⟨212585740751061199887120791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141723827167374133258080527 212585740751061199887120791)
  ·
    refine ⟨318878611126591799830681187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212585740751061199887120791 318878611126591799830681187)
    ·
      refine ⟨478317916689887699746021781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318878611126591799830681187 478317916689887699746021781)
      ·
        refine ⟨22421152344838485925594771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 478317916689887699746021781 22421152344838485925594771)
        ·
          refine ⟨33631728517257728888392157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22421152344838485925594771 33631728517257728888392157)
          ·
            refine ⟨12611898193971648333147059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33631728517257728888392157 12611898193971648333147059)
            ·
              refine ⟨18917847290957472499720589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611898193971648333147059 18917847290957472499720589)
              ·
                refine ⟨7094192734109052187395221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18917847290957472499720589 7094192734109052187395221)
                ·
                  refine ⟨332540284411361821284151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7094192734109052187395221 332540284411361821284151)
                  ·
                    rfl

theorem cell23_5828579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 6].length) (baseStart_5828579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828579 prefixEnd_5828579 := by exact prefixLift 5828579
  have htrace : WordTrace (prefixWord ++ tailWord_5828579) baseStart_5828579 baseEnd_5828579 := by
    simpa [prefixWord, tailWord_5828579, baseEnd_5828579] using wordTrace_append hprefix tailTrace_5828579
  have hstable : (prefixWord ++ tailWord_5828579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828579).length < 2 ^ (prefixWord ++ tailWord_5828579).sum := by decide
  have hdescent : baseEnd_5828579 < baseStart_5828579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828616 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_5828616 : Nat := 118140960795 + 5828616 * 2 ^ 59
def prefixEnd_5828616 : Nat := 4983230072969 + 3 ^ 40 * 5828616 * 2
def baseEnd_5828616 : Nat := 2992881558486472746794689

theorem tailTrace_5828616 : CollatzResearch.WordTrace tailWord_5828616 prefixEnd_5828616 2992881558486472746794689 := by
  unfold tailWord_5828616
  simp only [CollatzResearch.WordTrace]
  refine ⟨106293545125963577603108851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141724726834618103470811801 106293545125963577603108851)
  ·
    refine ⟨159440317688945366404663277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106293545125963577603108851 159440317688945366404663277)
    ·
      refine ⟨59790119133354512401748729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159440317688945366404663277 59790119133354512401748729)
      ·
        refine ⟨44842589350015884301311547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59790119133354512401748729 44842589350015884301311547)
        ·
          refine ⟨67263884025023826451967321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44842589350015884301311547 67263884025023826451967321)
          ·
            refine ⟨50447913018767869838975491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67263884025023826451967321 50447913018767869838975491)
            ·
              refine ⟨75671869528151804758463237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50447913018767869838975491 75671869528151804758463237)
              ·
                refine ⟨14188475536528463392211857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75671869528151804758463237 14188475536528463392211857)
                ·
                  refine ⟨10641356652396347544158893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14188475536528463392211857 10641356652396347544158893)
                  ·
                    refine ⟨3990508744648630329059585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10641356652396347544158893 3990508744648630329059585)
                    ·
                      refine ⟨2992881558486472746794689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990508744648630329059585 2992881558486472746794689)
                      ·
                        rfl

theorem cell23_5828616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_5828616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828616 prefixEnd_5828616 := by exact prefixLift 5828616
  have htrace : WordTrace (prefixWord ++ tailWord_5828616) baseStart_5828616 baseEnd_5828616 := by
    simpa [prefixWord, tailWord_5828616, baseEnd_5828616] using wordTrace_append hprefix tailTrace_5828616
  have hstable : (prefixWord ++ tailWord_5828616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828616).length < 2 ^ (prefixWord ++ tailWord_5828616).sum := by decide
  have hdescent : baseEnd_5828616 < baseStart_5828616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828639 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 1, 6]
def baseStart_5828639 : Nat := 118140960795 + 5828639 * 2 ^ 59
def prefixEnd_5828639 : Nat := 4983230072969 + 3 ^ 40 * 5828639 * 2
def baseEnd_5828639 : Nat := 997631122847175385602361

theorem tailTrace_5828639 : CollatzResearch.WordTrace tailWord_5828639 prefixEnd_5828639 997631122847175385602361 := by
  unfold tailWord_5828639
  simp only [CollatzResearch.WordTrace]
  refine ⟨212587929130843830134304971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141725286087229220089536647 212587929130843830134304971)
  ·
    refine ⟨318881893696265745201457457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212587929130843830134304971 318881893696265745201457457)
    ·
      refine ⟨239161420272199308901093093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318881893696265745201457457 239161420272199308901093093)
      ·
        refine ⟨44842766301037370418954955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239161420272199308901093093 44842766301037370418954955)
        ·
          refine ⟨67264149451556055628432433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44842766301037370418954955 67264149451556055628432433)
          ·
            refine ⟨50448112088667041721324325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67264149451556055628432433 50448112088667041721324325)
            ·
              refine ⟨9459021016625070322748311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50448112088667041721324325 9459021016625070322748311)
              ·
                refine ⟨14188531524937605484122467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459021016625070322748311 14188531524937605484122467)
                ·
                  refine ⟨21282797287406408226183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14188531524937605484122467 21282797287406408226183701)
                  ·
                    refine ⟨997631122847175385602361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21282797287406408226183701 997631122847175385602361)
                    ·
                      rfl

theorem cell23_5828639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_5828639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828639 prefixEnd_5828639 := by exact prefixLift 5828639
  have htrace : WordTrace (prefixWord ++ tailWord_5828639) baseStart_5828639 baseEnd_5828639 := by
    simpa [prefixWord, tailWord_5828639, baseEnd_5828639] using wordTrace_append hprefix tailTrace_5828639
  have hstable : (prefixWord ++ tailWord_5828639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828639).length < 2 ^ (prefixWord ++ tailWord_5828639).sum := by decide
  have hdescent : baseEnd_5828639 < baseStart_5828639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828650 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5828650 : Nat := 118140960795 + 5828650 * 2 ^ 59
def prefixEnd_5828650 : Nat := 4983230072969 + 3 ^ 40 * 5828650 * 2
def baseEnd_5828650 : Nat := 2992899016828725613769533

theorem tailTrace_5828650 : CollatzResearch.WordTrace tailWord_5828650 prefixEnd_5828650 2992899016828725613769533 := by
  unfold tailWord_5828650
  simp only [CollatzResearch.WordTrace]
  refine ⟨53147082583450994753238851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141725553555869319341970269 53147082583450994753238851)
  ·
    refine ⟨79720623875176492129858277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53147082583450994753238851 79720623875176492129858277)
    ·
      refine ⟨14947616976595592274348427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79720623875176492129858277 14947616976595592274348427)
      ·
        refine ⟨22421425464893388411522641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14947616976595592274348427 22421425464893388411522641)
        ·
          refine ⟨16816069098670041308641981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22421425464893388411522641 16816069098670041308641981)
          ·
            refine ⟨6306025912001265490740743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16816069098670041308641981 6306025912001265490740743)
            ·
              refine ⟨9459038868001898236111115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306025912001265490740743 9459038868001898236111115)
              ·
                refine ⟨14188558302002847354166673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459038868001898236111115 14188558302002847354166673)
                ·
                  refine ⟨10641418726502135515625005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14188558302002847354166673 10641418726502135515625005)
                  ·
                    refine ⟨3990532022438300818359377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10641418726502135515625005 3990532022438300818359377)
                    ·
                      refine ⟨2992899016828725613769533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990532022438300818359377 2992899016828725613769533)
                      ·
                        rfl

theorem cell23_5828650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5828650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828650 prefixEnd_5828650 := by exact prefixLift 5828650
  have htrace : WordTrace (prefixWord ++ tailWord_5828650) baseStart_5828650 baseEnd_5828650 := by
    simpa [prefixWord, tailWord_5828650, baseEnd_5828650] using wordTrace_append hprefix tailTrace_5828650
  have hstable : (prefixWord ++ tailWord_5828650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828650).length < 2 ^ (prefixWord ++ tailWord_5828650).sum := by decide
  have hdescent : baseEnd_5828650 < baseStart_5828650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828659 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4]
def baseStart_5828659 : Nat := 118140960795 + 5828659 * 2 ^ 59
def prefixEnd_5828659 : Nat := 4983230072969 + 3 ^ 40 * 5828659 * 2
def baseEnd_5828659 : Nat := 2992903638154616078556991

theorem tailTrace_5828659 : CollatzResearch.WordTrace tailWord_5828659 prefixEnd_5828659 2992903638154616078556991 := by
  unfold tailWord_5828659
  simp only [CollatzResearch.WordTrace]
  refine ⟨212588658590771373550033031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141725772393847582366688687 212588658590771373550033031)
  ·
    refine ⟨318882987886157060325049547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212588658590771373550033031 318882987886157060325049547)
    ·
      refine ⟨478324481829235590487574321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318882987886157060325049547 478324481829235590487574321)
      ·
        refine ⟨358743361371926692865680741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478324481829235590487574321 358743361371926692865680741)
        ·
          refine ⟨67264380257236254912315139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358743361371926692865680741 67264380257236254912315139)
          ·
            refine ⟨100896570385854382368472709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67264380257236254912315139 100896570385854382368472709)
            ·
              refine ⟨18918106947347696694088633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100896570385854382368472709 18918106947347696694088633)
              ·
                refine ⟨14188580210510772520566475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18918106947347696694088633 14188580210510772520566475)
                ·
                  refine ⟨21282870315766158780849713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14188580210510772520566475 21282870315766158780849713)
                  ·
                    refine ⟨15962152736824619085637285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21282870315766158780849713 15962152736824619085637285)
                    ·
                      refine ⟨2992903638154616078556991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15962152736824619085637285 2992903638154616078556991)
                      ·
                        rfl

theorem cell23_5828659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_5828659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828659 prefixEnd_5828659 := by exact prefixLift 5828659
  have htrace : WordTrace (prefixWord ++ tailWord_5828659) baseStart_5828659 baseEnd_5828659 := by
    simpa [prefixWord, tailWord_5828659, baseEnd_5828659] using wordTrace_append hprefix tailTrace_5828659
  have hstable : (prefixWord ++ tailWord_5828659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828659).length < 2 ^ (prefixWord ++ tailWord_5828659).sum := by decide
  have hdescent : baseEnd_5828659 < baseStart_5828659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828673 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5828673 : Nat := 118140960795 + 5828673 * 2 ^ 59
def prefixEnd_5828673 : Nat := 4983230072969 + 3 ^ 40 * 5828673 * 2
def baseEnd_5828673 : Nat := 997636942294593007927309

theorem tailTrace_5828673 : CollatzResearch.WordTrace tailWord_5828673 prefixEnd_5828673 997636942294593007927309 := by
  unfold tailWord_5828673
  simp only [CollatzResearch.WordTrace]
  refine ⟨212589169212720653941042673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141726112808480435960695115 212589169212720653941042673)
  ·
    refine ⟨159441876909540490455782005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212589169212720653941042673 159441876909540490455782005)
    ·
      refine ⟨14947675960269420980229563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159441876909540490455782005 14947675960269420980229563)
      ·
        refine ⟨22421513940404131470344345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14947675960269420980229563 22421513940404131470344345)
        ·
          refine ⟨16816135455303098602758259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22421513940404131470344345 16816135455303098602758259)
          ·
            refine ⟨25224203182954647904137389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16816135455303098602758259 25224203182954647904137389)
            ·
              refine ⟨9459076193607992964051521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25224203182954647904137389 9459076193607992964051521)
              ·
                refine ⟨7094307145205994723038641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9459076193607992964051521 7094307145205994723038641)
                ·
                  refine ⟨5320730358904496042278981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7094307145205994723038641 5320730358904496042278981)
                  ·
                    refine ⟨997636942294593007927309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320730358904496042278981 997636942294593007927309)
                    ·
                      rfl

theorem cell23_5828673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5828673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828673 prefixEnd_5828673 := by exact prefixLift 5828673
  have htrace : WordTrace (prefixWord ++ tailWord_5828673) baseStart_5828673 baseEnd_5828673 := by
    simpa [prefixWord, tailWord_5828673, baseEnd_5828673] using wordTrace_append hprefix tailTrace_5828673
  have hstable : (prefixWord ++ tailWord_5828673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828673).length < 2 ^ (prefixWord ++ tailWord_5828673).sum := by decide
  have hdescent : baseEnd_5828673 < baseStart_5828673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828690 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_5828690 : Nat := 118140960795 + 5828690 * 2 ^ 59
def prefixEnd_5828690 : Nat := 4983230072969 + 3 ^ 40 * 5828690 * 2
def baseEnd_5828690 : Nat := 997639852018301819089783

theorem tailTrace_5828690 : CollatzResearch.WordTrace tailWord_5828690 prefixEnd_5828690 997639852018301819089783 := by
  unfold tailWord_5828690
  simp only [CollatzResearch.WordTrace]
  refine ⟨53147447313414766461102881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141726526169106043896274349 53147447313414766461102881)
  ·
    refine ⟨39860585485061074845827161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53147447313414766461102881 39860585485061074845827161)
    ·
      refine ⟨29895439113795806134370371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39860585485061074845827161 29895439113795806134370371)
      ·
        refine ⟨44843158670693709201555557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29895439113795806134370371 44843158670693709201555557)
        ·
          refine ⟨8408092250755070475291667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44843158670693709201555557 8408092250755070475291667)
          ·
            refine ⟨12612138376132605712937501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408092250755070475291667 12612138376132605712937501)
            ·
              refine ⟨4729551891049727142351563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12612138376132605712937501 4729551891049727142351563)
              ·
                refine ⟨7094327836574590713527345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729551891049727142351563 7094327836574590713527345)
                ·
                  refine ⟨5320745877430943035145509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7094327836574590713527345 5320745877430943035145509)
                  ·
                    refine ⟨997639852018301819089783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320745877430943035145509 997639852018301819089783)
                    ·
                      rfl

theorem cell23_5828690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_5828690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828690 prefixEnd_5828690 := by exact prefixLift 5828690
  have htrace : WordTrace (prefixWord ++ tailWord_5828690) baseStart_5828690 baseEnd_5828690 := by
    simpa [prefixWord, tailWord_5828690, baseEnd_5828690] using wordTrace_append hprefix tailTrace_5828690
  have hstable : (prefixWord ++ tailWord_5828690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828690).length < 2 ^ (prefixWord ++ tailWord_5828690).sum := by decide
  have hdescent : baseEnd_5828690 < baseStart_5828690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828696 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_5828696 : Nat := 118140960795 + 5828696 * 2 ^ 59
def prefixEnd_5828696 : Nat := 4983230072969 + 3 ^ 40 * 5828696 * 2
def baseEnd_5828696 : Nat := 2992922636938832433794321

theorem tailTrace_5828696 : CollatzResearch.WordTrace tailWord_5828696 prefixEnd_5828696 2992922636938832433794321 := by
  unfold tailWord_5828696
  simp only [CollatzResearch.WordTrace]
  refine ⟨106295004045818664434564971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141726672061091552579419961 106295004045818664434564971)
  ·
    refine ⟨159442506068727996651847457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106295004045818664434564971 159442506068727996651847457)
    ·
      refine ⟨119581879551545997488885593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159442506068727996651847457 119581879551545997488885593)
      ·
        refine ⟨89686409663659498116664195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119581879551545997488885593 89686409663659498116664195)
        ·
          refine ⟨134529614495489247174996293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89686409663659498116664195 134529614495489247174996293)
          ·
            refine ⟨25224302717904233845311805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134529614495489247174996293 25224302717904233845311805)
            ·
              refine ⟨9459113519214087691991927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25224302717904233845311805 9459113519214087691991927)
              ·
                refine ⟨14188670278821131537987891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459113519214087691991927 14188670278821131537987891)
                ·
                  refine ⟨21283005418231697306981837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14188670278821131537987891 21283005418231697306981837)
                  ·
                    refine ⟨7981127031836886490118189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21283005418231697306981837 7981127031836886490118189)
                    ·
                      refine ⟨2992922636938832433794321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7981127031836886490118189 2992922636938832433794321)
                      ·
                        rfl

theorem cell23_5828696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_5828696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828696 prefixEnd_5828696 := by exact prefixLift 5828696
  have htrace : WordTrace (prefixWord ++ tailWord_5828696) baseStart_5828696 baseEnd_5828696 := by
    simpa [prefixWord, tailWord_5828696, baseEnd_5828696] using wordTrace_append hprefix tailTrace_5828696
  have hstable : (prefixWord ++ tailWord_5828696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828696).length < 2 ^ (prefixWord ++ tailWord_5828696).sum := by decide
  have hdescent : baseEnd_5828696 < baseStart_5828696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828709 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5828709 : Nat := 118140960795 + 5828709 * 2 ^ 59
def prefixEnd_5828709 : Nat := 4983230072969 + 3 ^ 40 * 5828709 * 2
def baseEnd_5828709 : Nat := 2992929312187340882931761

theorem tailTrace_5828709 : CollatzResearch.WordTrace tailWord_5828709 prefixEnd_5828709 2992929312187340882931761 := by
  unfold tailWord_5828709
  simp only [CollatzResearch.WordTrace]
  refine ⟨212590482240590232089353181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141726988160393488059568787 212590482240590232089353181)
  ·
    refine ⟨79721430840221337033507443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212590482240590232089353181 79721430840221337033507443)
    ·
      refine ⟨119582146260332005550261165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79721430840221337033507443 119582146260332005550261165)
      ·
        refine ⟨44843304847624502081347937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119582146260332005550261165 44843304847624502081347937)
        ·
          refine ⟨33632478635718376561010953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44843304847624502081347937 33632478635718376561010953)
          ·
            refine ⟨25224358976788782420758215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33632478635718376561010953 25224358976788782420758215)
            ·
              refine ⟨37836538465183173631137323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25224358976788782420758215 37836538465183173631137323)
              ·
                refine ⟨56754807697774760446705985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37836538465183173631137323 56754807697774760446705985)
                ·
                  refine ⟨42566105773331070335029489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56754807697774760446705985 42566105773331070335029489)
                  ·
                    refine ⟨31924579329998302751272117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42566105773331070335029489 31924579329998302751272117)
                    ·
                      refine ⟨2992929312187340882931761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31924579329998302751272117 2992929312187340882931761)
                      ·
                        rfl

theorem cell23_5828709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5828709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828709 prefixEnd_5828709 := by exact prefixLift 5828709
  have htrace : WordTrace (prefixWord ++ tailWord_5828709) baseStart_5828709 baseEnd_5828709 := by
    simpa [prefixWord, tailWord_5828709, baseEnd_5828709] using wordTrace_append hprefix tailTrace_5828709
  have hstable : (prefixWord ++ tailWord_5828709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828709).length < 2 ^ (prefixWord ++ tailWord_5828709).sum := by decide
  have hdescent : baseEnd_5828709 < baseStart_5828709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828714 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_5828714 : Nat := 118140960795 + 5828714 * 2 ^ 59
def prefixEnd_5828714 : Nat := 4983230072969 + 3 ^ 40 * 5828714 * 2
def baseEnd_5828714 : Nat := 2992931879590613363369239

theorem tailTrace_5828714 : CollatzResearch.WordTrace tailWord_5828714 prefixEnd_5828714 2992931879590613363369239 := by
  unfold tailWord_5828714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53147666151393029485821299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141727109737048078628856797 53147666151393029485821299)
  ·
    refine ⟨79721499227089544228731949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53147666151393029485821299 79721499227089544228731949)
    ·
      refine ⟨29895562210158579085774481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79721499227089544228731949 29895562210158579085774481)
      ·
        refine ⟨22421671657618934314330861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29895562210158579085774481 22421671657618934314330861)
        ·
          refine ⟨8408126871607100367874073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22421671657618934314330861 8408126871607100367874073)
          ·
            refine ⟨6306095153705325275905555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8408126871607100367874073 6306095153705325275905555)
            ·
              refine ⟨9459142730557987913858333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306095153705325275905555 9459142730557987913858333)
              ·
                refine ⟨3547178523959245467696875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9459142730557987913858333 3547178523959245467696875)
                ·
                  refine ⟨5320767785938868201545313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547178523959245467696875 5320767785938868201545313)
                  ·
                    refine ⟨3990575839454151151158985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5320767785938868201545313 3990575839454151151158985)
                    ·
                      refine ⟨2992931879590613363369239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990575839454151151158985 2992931879590613363369239)
                      ·
                        rfl

theorem cell23_5828714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_5828714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828714 prefixEnd_5828714 := by exact prefixLift 5828714
  have htrace : WordTrace (prefixWord ++ tailWord_5828714) baseStart_5828714 baseEnd_5828714 := by
    simpa [prefixWord, tailWord_5828714, baseEnd_5828714] using wordTrace_append hprefix tailTrace_5828714
  have hstable : (prefixWord ++ tailWord_5828714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828714).length < 2 ^ (prefixWord ++ tailWord_5828714).sum := by decide
  have hdescent : baseEnd_5828714 < baseStart_5828714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828770 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5828770 : Nat := 118140960795 + 5828770 * 2 ^ 59
def prefixEnd_5828770 : Nat := 4983230072969 + 3 ^ 40 * 5828770 * 2
def baseEnd_5828770 : Nat := 2992960634507265144268981

theorem tailTrace_5828770 : CollatzResearch.WordTrace tailWord_5828770 prefixEnd_5828770 2992960634507265144268981 := by
  unfold tailWord_5828770
  simp only [CollatzResearch.WordTrace]
  refine ⟨53148176773342309876830941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141728471395579493004882509 53148176773342309876830941)
  ·
    refine ⟨19930566290003366203811603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53148176773342309876830941 19930566290003366203811603)
    ·
      refine ⟨29895849435005049305717405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19930566290003366203811603 29895849435005049305717405)
      ·
        refine ⟨11210943538126893489644027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29895849435005049305717405 11210943538126893489644027)
        ·
          refine ⟨16816415307190340234466041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210943538126893489644027 16816415307190340234466041)
          ·
            refine ⟨12612311480392755175849531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16816415307190340234466041 12612311480392755175849531)
            ·
              refine ⟨18918467220589132763774297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12612311480392755175849531 18918467220589132763774297)
              ·
                refine ⟨14188850415441849572830723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18918467220589132763774297 14188850415441849572830723)
                ·
                  refine ⟨21283275623162774359246085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14188850415441849572830723 21283275623162774359246085)
                  ·
                    refine ⟨3990614179343020192358641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21283275623162774359246085 3990614179343020192358641)
                    ·
                      refine ⟨2992960634507265144268981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3990614179343020192358641 2992960634507265144268981)
                      ·
                        rfl

theorem cell23_5828770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5828770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828770 prefixEnd_5828770 := by exact prefixLift 5828770
  have htrace : WordTrace (prefixWord ++ tailWord_5828770) baseStart_5828770 baseEnd_5828770 := by
    simpa [prefixWord, tailWord_5828770, baseEnd_5828770] using wordTrace_append hprefix tailTrace_5828770
  have hstable : (prefixWord ++ tailWord_5828770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828770).length < 2 ^ (prefixWord ++ tailWord_5828770).sum := by decide
  have hdescent : baseEnd_5828770 < baseStart_5828770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828786 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_5828786 : Nat := 118140960795 + 5828786 * 2 ^ 59
def prefixEnd_5828786 : Nat := 4983230072969 + 3 ^ 40 * 5828786 * 2
def baseEnd_5828786 : Nat := 2992968850197737081668907

theorem tailTrace_5828786 : CollatzResearch.WordTrace tailWord_5828786 prefixEnd_5828786 2992968850197737081668907 := by
  unfold tailWord_5828786
  simp only [CollatzResearch.WordTrace]
  refine ⟨53148322665327818559976553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141728860440874182826604141 53148322665327818559976553)
  ·
    refine ⟨39861241998995863919982415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53148322665327818559976553 39861241998995863919982415)
    ·
      refine ⟨59791862998493795879973623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39861241998995863919982415 59791862998493795879973623)
      ·
        refine ⟨89687794497740693819960435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59791862998493795879973623 89687794497740693819960435)
        ·
          refine ⟨134531691746611040729940653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89687794497740693819960435 134531691746611040729940653)
          ·
            refine ⟨50449384404979140273727745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134531691746611040729940653 50449384404979140273727745)
            ·
              refine ⟨37837038303734355205295809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50449384404979140273727745 37837038303734355205295809)
              ·
                refine ⟨28377778727800766403971857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37837038303734355205295809 28377778727800766403971857)
                ·
                  refine ⟨21283334045850574802978893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28377778727800766403971857 21283334045850574802978893)
                  ·
                    refine ⟨7981250267193965551117085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21283334045850574802978893 7981250267193965551117085)
                    ·
                      refine ⟨2992968850197737081668907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7981250267193965551117085 2992968850197737081668907)
                      ·
                        rfl

theorem cell23_5828786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_5828786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828786 prefixEnd_5828786 := by exact prefixLift 5828786
  have htrace : WordTrace (prefixWord ++ tailWord_5828786) baseStart_5828786 baseEnd_5828786 := by
    simpa [prefixWord, tailWord_5828786, baseEnd_5828786] using wordTrace_append hprefix tailTrace_5828786
  have hstable : (prefixWord ++ tailWord_5828786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828786).length < 2 ^ (prefixWord ++ tailWord_5828786).sum := by decide
  have hdescent : baseEnd_5828786 < baseStart_5828786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828836 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_5828836 : Nat := 118140960795 + 5828836 * 2 ^ 59
def prefixEnd_5828836 : Nat := 4983230072969 + 3 ^ 40 * 5828836 * 2
def baseEnd_5828836 : Nat := 997664841410153962014559

theorem tailTrace_5828836 : CollatzResearch.WordTrace tailWord_5828836 prefixEnd_5828836 997664841410153962014559 := by
  unfold tailWord_5828836
  simp only [CollatzResearch.WordTrace]
  refine ⟨106297557155565066389613181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141730076207420088519484241 106297557155565066389613181)
  ·
    refine ⟨39861583933336899896104943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106297557155565066389613181 39861583933336899896104943)
    ·
      refine ⟨59792375900005349844157415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39861583933336899896104943 59792375900005349844157415)
      ·
        refine ⟨89688563850008024766236123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59792375900005349844157415 89688563850008024766236123)
        ·
          refine ⟨134532845775012037149354185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89688563850008024766236123 134532845775012037149354185)
          ·
            refine ⟨100899634331259027862015639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134532845775012037149354185 100899634331259027862015639)
            ·
              refine ⟨151349451496888541793023459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100899634331259027862015639 151349451496888541793023459)
              ·
                refine ⟨227024177245332812689535189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151349451496888541793023459 227024177245332812689535189)
                ·
                  refine ⟨5320879154187487797410981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 227024177245332812689535189 5320879154187487797410981)
                  ·
                    refine ⟨997664841410153962014559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320879154187487797410981 997664841410153962014559)
                    ·
                      rfl

theorem cell23_5828836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_5828836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828836 prefixEnd_5828836 := by exact prefixLift 5828836
  have htrace : WordTrace (prefixWord ++ tailWord_5828836) baseStart_5828836 baseEnd_5828836 := by
    simpa [prefixWord, tailWord_5828836, baseEnd_5828836] using wordTrace_append hprefix tailTrace_5828836
  have hstable : (prefixWord ++ tailWord_5828836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828836).length < 2 ^ (prefixWord ++ tailWord_5828836).sum := by decide
  have hdescent : baseEnd_5828836 < baseStart_5828836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828876 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_5828876 : Nat := 118140960795 + 5828876 * 2 ^ 59
def prefixEnd_5828876 : Nat := 4983230072969 + 3 ^ 40 * 5828876 * 2
def baseEnd_5828876 : Nat := 2993015063456641729543493

theorem tailTrace_5828876 : CollatzResearch.WordTrace tailWord_5828876 prefixEnd_5828876 2993015063456641729543493 := by
  unfold tailWord_5828876
  simp only [CollatzResearch.WordTrace]
  refine ⟨106298286615492609805341241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141731048820656813073788321 106298286615492609805341241)
  ·
    refine ⟨79723714961619457354005931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106298286615492609805341241 79723714961619457354005931)
    ·
      refine ⟨119585572442429186031008897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79723714961619457354005931 119585572442429186031008897)
      ·
        refine ⟨89689179331821889523256673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119585572442429186031008897 89689179331821889523256673)
        ·
          refine ⟨67266884498866417142442505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89689179331821889523256673 67266884498866417142442505)
          ·
            refine ⟨50450163374149812856831879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67266884498866417142442505 50450163374149812856831879)
            ·
              refine ⟨75675245061224719285247819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50450163374149812856831879 75675245061224719285247819)
              ·
                refine ⟨113512867591837078927871729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75675245061224719285247819 113512867591837078927871729)
                ·
                  refine ⟨85134650693877809195903797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113512867591837078927871729 85134650693877809195903797)
                  ·
                    refine ⟨7981373502551044612115981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85134650693877809195903797 7981373502551044612115981)
                    ·
                      refine ⟨2993015063456641729543493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7981373502551044612115981 2993015063456641729543493)
                      ·
                        rfl

theorem cell23_5828876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_5828876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828876 prefixEnd_5828876 := by exact prefixLift 5828876
  have htrace : WordTrace (prefixWord ++ tailWord_5828876) baseStart_5828876 baseEnd_5828876 := by
    simpa [prefixWord, tailWord_5828876, baseEnd_5828876] using wordTrace_append hprefix tailTrace_5828876
  have hstable : (prefixWord ++ tailWord_5828876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828876).length < 2 ^ (prefixWord ++ tailWord_5828876).sum := by decide
  have hdescent : baseEnd_5828876 < baseStart_5828876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828879 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 9]
def baseStart_5828879 : Nat := 118140960795 + 5828879 * 2 ^ 59
def prefixEnd_5828879 : Nat := 4983230072969 + 3 ^ 40 * 5828879 * 2
def baseEnd_5828879 : Nat := 997672201299535072601993

theorem tailTrace_5828879 : CollatzResearch.WordTrace tailWord_5828879 prefixEnd_5828879 997672201299535072601993 := by
  unfold tailWord_5828879
  simp only [CollatzResearch.WordTrace]
  refine ⟨212596682649974351123041691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141731121766649567415361127 212596682649974351123041691)
  ·
    refine ⟨318895023974961526684562537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212596682649974351123041691 318895023974961526684562537)
    ·
      refine ⟨239171267981221145013421903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318895023974961526684562537 239171267981221145013421903)
      ·
        refine ⟨358756901971831717520132855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239171267981221145013421903 358756901971831717520132855)
        ·
          refine ⟨538135352957747576280199283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358756901971831717520132855 538135352957747576280199283)
          ·
            refine ⟨807203029436621364420298925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538135352957747576280199283 807203029436621364420298925)
            ·
              refine ⟨302701136038733011657612097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807203029436621364420298925 302701136038733011657612097)
              ·
                refine ⟨227025852029049758743209073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302701136038733011657612097 227025852029049758743209073)
                ·
                  refine ⟨170269389021787319057406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227025852029049758743209073 170269389021787319057406805)
                  ·
                    refine ⟨997672201299535072601993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170269389021787319057406805 997672201299535072601993)
                    ·
                      rfl

theorem cell23_5828879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_5828879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828879 prefixEnd_5828879 := by exact prefixLift 5828879
  have htrace : WordTrace (prefixWord ++ tailWord_5828879) baseStart_5828879 baseEnd_5828879 := by
    simpa [prefixWord, tailWord_5828879, baseEnd_5828879] using wordTrace_append hprefix tailTrace_5828879
  have hstable : (prefixWord ++ tailWord_5828879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828879).length < 2 ^ (prefixWord ++ tailWord_5828879).sum := by decide
  have hdescent : baseEnd_5828879 < baseStart_5828879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828887 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 1, 4]
def baseStart_5828887 : Nat := 118140960795 + 5828887 * 2 ^ 59
def prefixEnd_5828887 : Nat := 4983230072969 + 3 ^ 40 * 5828887 * 2
def baseEnd_5828887 : Nat := 997673570581280395501981

theorem tailTrace_5828887 : CollatzResearch.WordTrace tailWord_5828887 prefixEnd_5828887 997673570581280395501981 := by
  unfold tailWord_5828887
  simp only [CollatzResearch.WordTrace]
  refine ⟨212596974433945368489332915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141731316289296912326221943 212596974433945368489332915)
  ·
    refine ⟨318895461650918052733999373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212596974433945368489332915 318895461650918052733999373)
    ·
      refine ⟨119585798119094269775249765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318895461650918052733999373 119585798119094269775249765)
      ·
        refine ⟨22422337147330175582859331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119585798119094269775249765 22422337147330175582859331)
        ·
          refine ⟨33633505720995263374288997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22422337147330175582859331 33633505720995263374288997)
          ·
            refine ⟨6306282322686611882679187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33633505720995263374288997 6306282322686611882679187)
            ·
              refine ⟨9459423484029917824018781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306282322686611882679187 9459423484029917824018781)
              ·
                refine ⟨3547283806511219184007043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9459423484029917824018781 3547283806511219184007043)
                ·
                  refine ⟨5320925709766828776010565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547283806511219184007043 5320925709766828776010565)
                  ·
                    refine ⟨997673570581280395501981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320925709766828776010565 997673570581280395501981)
                    ·
                      rfl

theorem cell23_5828887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_5828887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828887 prefixEnd_5828887 := by exact prefixLift 5828887
  have htrace : WordTrace (prefixWord ++ tailWord_5828887) baseStart_5828887 baseEnd_5828887 := by
    simpa [prefixWord, tailWord_5828887, baseEnd_5828887] using wordTrace_append hprefix tailTrace_5828887
  have hstable : (prefixWord ++ tailWord_5828887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828887).length < 2 ^ (prefixWord ++ tailWord_5828887).sum := by decide
  have hdescent : baseEnd_5828887 < baseStart_5828887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828904 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 1, 4]
def baseStart_5828904 : Nat := 118140960795 + 5828904 * 2 ^ 59
def prefixEnd_5828904 : Nat := 4983230072969 + 3 ^ 40 * 5828904 * 2
def baseEnd_5828904 : Nat := 997676480304989206664455

theorem tailTrace_5828904 : CollatzResearch.WordTrace tailWord_5828904 prefixEnd_5828904 997676480304989206664455 := by
  unfold tailWord_5828904
  simp only [CollatzResearch.WordTrace]
  refine ⟨106298797237441890196350883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141731729649922520261801177 106298797237441890196350883)
  ·
    refine ⟨159448195856162835294526325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106298797237441890196350883 159448195856162835294526325)
    ·
      refine ⟨14948268361515265808861843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159448195856162835294526325 14948268361515265808861843)
      ·
        refine ⟨22422402542272898713292765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14948268361515265808861843 22422402542272898713292765)
        ·
          refine ⟨8408400953352337017484787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22422402542272898713292765 8408400953352337017484787)
          ·
            refine ⟨12612601430028505526227181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408400953352337017484787 12612601430028505526227181)
            ·
              refine ⟨4729725536260689572335193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12612601430028505526227181 4729725536260689572335193)
              ·
                refine ⟨3547294152195517179251395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4729725536260689572335193 3547294152195517179251395)
                ·
                  refine ⟨5320941228293275768877093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547294152195517179251395 5320941228293275768877093)
                  ·
                    refine ⟨997676480304989206664455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320941228293275768877093 997676480304989206664455)
                    ·
                      rfl

theorem cell23_5828904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_5828904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828904 prefixEnd_5828904 := by exact prefixLift 5828904
  have htrace : WordTrace (prefixWord ++ tailWord_5828904) baseStart_5828904 baseEnd_5828904 := by
    simpa [prefixWord, tailWord_5828904, baseEnd_5828904] using wordTrace_append hprefix tailTrace_5828904
  have hstable : (prefixWord ++ tailWord_5828904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828904).length < 2 ^ (prefixWord ++ tailWord_5828904).sum := by decide
  have hdescent : baseEnd_5828904 < baseStart_5828904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828936 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_5828936 : Nat := 118140960795 + 5828936 * 2 ^ 59
def prefixEnd_5828936 : Nat := 4983230072969 + 3 ^ 40 * 5828936 * 2
def baseEnd_5828936 : Nat := 2993045872295911494793217

theorem tailTrace_5828936 : CollatzResearch.WordTrace tailWord_5828936 prefixEnd_5828936 2993045872295911494793217 := by
  unfold tailWord_5828936
  simp only [CollatzResearch.WordTrace]
  refine ⟨106299380805383924928933331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141732507740511899905244441 106299380805383924928933331)
  ·
    refine ⟨159449071208075887393399997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106299380805383924928933331 159449071208075887393399997)
    ·
      refine ⟨59793401703028457772524999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159449071208075887393399997 59793401703028457772524999)
      ·
        refine ⟨89690102554542686658787499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59793401703028457772524999 89690102554542686658787499)
        ·
          refine ⟨134535153831814029988181249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89690102554542686658787499 134535153831814029988181249)
          ·
            refine ⟨100901365373860522491135937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134535153831814029988181249 100901365373860522491135937)
            ·
              refine ⟨75676024030395391868351953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100901365373860522491135937 75676024030395391868351953)
              ·
                refine ⟨56757018022796543901263965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75676024030395391868351953 56757018022796543901263965)
                ·
                  refine ⟨21283881758548703962973987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56757018022796543901263965 21283881758548703962973987)
                  ·
                    refine ⟨31925822637823055944460981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21283881758548703962973987 31925822637823055944460981)
                    ·
                      refine ⟨2993045872295911494793217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31925822637823055944460981 2993045872295911494793217)
                      ·
                        rfl

theorem cell23_5828936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_5828936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828936 prefixEnd_5828936 := by exact prefixLift 5828936
  have htrace : WordTrace (prefixWord ++ tailWord_5828936) baseStart_5828936 baseEnd_5828936 := by
    simpa [prefixWord, tailWord_5828936, baseEnd_5828936] using wordTrace_append hprefix tailTrace_5828936
  have hstable : (prefixWord ++ tailWord_5828936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828936).length < 2 ^ (prefixWord ++ tailWord_5828936).sum := by decide
  have hdescent : baseEnd_5828936 < baseStart_5828936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5828970 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5828970 : Nat := 118140960795 + 5828970 * 2 ^ 59
def prefixEnd_5828970 : Nat := 4983230072969 + 3 ^ 40 * 5828970 * 2
def baseEnd_5828970 : Nat := 2993063330638164361768061

theorem tailTrace_5828970 : CollatzResearch.WordTrace tailWord_5828970 prefixEnd_5828970 2993063330638164361768061 := by
  unfold tailWord_5828970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53150000423161168416151091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141733334461763115776402909 53150000423161168416151091)
  ·
    refine ⟨79725000634741752624226637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53150000423161168416151091 79725000634741752624226637)
    ·
      refine ⟨29896875238028157234084989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79725000634741752624226637 29896875238028157234084989)
      ·
        refine ⟨11211328214260558962781871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29896875238028157234084989 11211328214260558962781871)
        ·
          refine ⟨16816992321390838444172807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11211328214260558962781871 16816992321390838444172807)
          ·
            refine ⟨25225488482086257666259211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16816992321390838444172807 25225488482086257666259211)
            ·
              refine ⟨37838232723129386499388817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25225488482086257666259211 37838232723129386499388817)
              ·
                refine ⟨28378674542347039874541613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37838232723129386499388817 28378674542347039874541613)
                ·
                  refine ⟨10642002953380139952953105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28378674542347039874541613 10642002953380139952953105)
                  ·
                    refine ⟨7981502215035104964714829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10642002953380139952953105 7981502215035104964714829)
                    ·
                      refine ⟨2993063330638164361768061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7981502215035104964714829 2993063330638164361768061)
                      ·
                        rfl

theorem cell23_5828970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5828970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5828970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5828970 prefixEnd_5828970 := by exact prefixLift 5828970
  have htrace : WordTrace (prefixWord ++ tailWord_5828970) baseStart_5828970 baseEnd_5828970 := by
    simpa [prefixWord, tailWord_5828970, baseEnd_5828970] using wordTrace_append hprefix tailTrace_5828970
  have hstable : (prefixWord ++ tailWord_5828970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5828970).length < 2 ^ (prefixWord ++ tailWord_5828970).sum := by decide
  have hdescent : baseEnd_5828970 < baseStart_5828970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5828970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829000 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5829000 : Nat := 118140960795 + 5829000 * 2 ^ 59
def prefixEnd_5829000 : Nat := 4983230072969 + 3 ^ 40 * 5829000 * 2
def baseEnd_5829000 : Nat := 2993078735057799244392923

theorem tailTrace_5829000 : CollatzResearch.WordTrace tailWord_5829000 prefixEnd_5829000 2993078735057799244392923 := by
  unfold tailWord_5829000
  simp only [CollatzResearch.WordTrace]
  refine ⟨106300547941267994394098227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141734063921690659192130969 106300547941267994394098227)
  ·
    refine ⟨159450821911901991591147341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106300547941267994394098227 159450821911901991591147341)
    ·
      refine ⟨59794058216963246846680253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159450821911901991591147341 59794058216963246846680253)
      ·
        refine ⟨22422771831361217567505095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59794058216963246846680253 22422771831361217567505095)
        ·
          refine ⟨33634157747041826351257643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22422771831361217567505095 33634157747041826351257643)
          ·
            refine ⟨50451236620562739526886465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33634157747041826351257643 50451236620562739526886465)
            ·
              refine ⟨37838427465422054645164849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50451236620562739526886465 37838427465422054645164849)
              ·
                refine ⟨28378820599066540983873637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37838427465422054645164849 28378820599066540983873637)
                ·
                  refine ⟨5321028862324976434476307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28378820599066540983873637 5321028862324976434476307)
                  ·
                    refine ⟨7981543293487464651714461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5321028862324976434476307 7981543293487464651714461)
                    ·
                      refine ⟨2993078735057799244392923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7981543293487464651714461 2993078735057799244392923)
                      ·
                        rfl

theorem cell23_5829000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5829000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829000 prefixEnd_5829000 := by exact prefixLift 5829000
  have htrace : WordTrace (prefixWord ++ tailWord_5829000) baseStart_5829000 baseEnd_5829000 := by
    simpa [prefixWord, tailWord_5829000, baseEnd_5829000] using wordTrace_append hprefix tailTrace_5829000
  have hstable : (prefixWord ++ tailWord_5829000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829000).length < 2 ^ (prefixWord ++ tailWord_5829000).sum := by decide
  have hdescent : baseEnd_5829000 < baseStart_5829000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829073 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_5829073 : Nat := 118140960795 + 5829073 * 2 ^ 59
def prefixEnd_5829073 : Nat := 4983230072969 + 3 ^ 40 * 5829073 * 2
def baseEnd_5829073 : Nat := 2993116219145577458780087

theorem tailTrace_5829073 : CollatzResearch.WordTrace tailWord_5829073 prefixEnd_5829073 2993116219145577458780087 := by
  unfold tailWord_5829073
  simp only [CollatzResearch.WordTrace]
  refine ⟨212603758411271522255603873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141735838940847681503735915 212603758411271522255603873)
  ·
    refine ⟨159452818808453641691702905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212603758411271522255603873 159452818808453641691702905)
    ·
      refine ⟨119589614106340231268777179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159452818808453641691702905 119589614106340231268777179)
      ·
        refine ⟨179384421159510346903165769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119589614106340231268777179 179384421159510346903165769)
        ·
          refine ⟨134538315869632760177374327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179384421159510346903165769 134538315869632760177374327)
          ·
            refine ⟨201807473804449140266061491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134538315869632760177374327 201807473804449140266061491)
            ·
              refine ⟨302711210706673710399092237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201807473804449140266061491 302711210706673710399092237)
              ·
                refine ⟨113516704015002641399659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302711210706673710399092237 113516704015002641399659589)
                ·
                  refine ⟨21284382002812995262436173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113516704015002641399659589 21284382002812995262436173)
                  ·
                    refine ⟨7981643251054873223413565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21284382002812995262436173 7981643251054873223413565)
                    ·
                      refine ⟨2993116219145577458780087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7981643251054873223413565 2993116219145577458780087)
                      ·
                        rfl

theorem cell23_5829073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_5829073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829073 prefixEnd_5829073 := by exact prefixLift 5829073
  have htrace : WordTrace (prefixWord ++ tailWord_5829073) baseStart_5829073 baseEnd_5829073 := by
    simpa [prefixWord, tailWord_5829073, baseEnd_5829073] using wordTrace_append hprefix tailTrace_5829073
  have hstable : (prefixWord ++ tailWord_5829073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829073).length < 2 ^ (prefixWord ++ tailWord_5829073).sum := by decide
  have hdescent : baseEnd_5829073 < baseStart_5829073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829113 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5829113 : Nat := 118140960795 + 5829113 * 2 ^ 59
def prefixEnd_5829113 : Nat := 4983230072969 + 3 ^ 40 * 5829113 * 2
def baseEnd_5829113 : Nat := 2993136758371757302279903

theorem tailTrace_5829113 : CollatzResearch.WordTrace tailWord_5829113 prefixEnd_5829113 2993136758371757302279903 := by
  unfold tailWord_5829113
  simp only [CollatzResearch.WordTrace]
  refine ⟨212605217331126609087059993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141736811554084406058039995 212605217331126609087059993)
  ·
    refine ⟨159453912998344956815294995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212605217331126609087059993 159453912998344956815294995)
    ·
      refine ⟨239180869497517435222942493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159453912998344956815294995 239180869497517435222942493)
      ·
        refine ⟨89692826061569038208603435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239180869497517435222942493 89692826061569038208603435)
        ·
          refine ⟨134539239092353557312905153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89692826061569038208603435 134539239092353557312905153)
          ·
            refine ⟨100904429319265167984678865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134539239092353557312905153 100904429319265167984678865)
            ·
              refine ⟨75678321989448875988509149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100904429319265167984678865 75678321989448875988509149)
              ·
                refine ⟨28379370746043328495690931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75678321989448875988509149 28379370746043328495690931)
                ·
                  refine ⟨42569056119064992743536397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28379370746043328495690931 42569056119064992743536397)
                  ·
                    refine ⟨15963396044649372278826149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42569056119064992743536397 15963396044649372278826149)
                    ·
                      refine ⟨2993136758371757302279903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15963396044649372278826149 2993136758371757302279903)
                      ·
                        rfl

theorem cell23_5829113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5829113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829113 prefixEnd_5829113 := by exact prefixLift 5829113
  have htrace : WordTrace (prefixWord ++ tailWord_5829113) baseStart_5829113 baseEnd_5829113 := by
    simpa [prefixWord, tailWord_5829113, baseEnd_5829113] using wordTrace_append hprefix tailTrace_5829113
  have hstable : (prefixWord ++ tailWord_5829113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829113).length < 2 ^ (prefixWord ++ tailWord_5829113).sum := by decide
  have hdescent : baseEnd_5829113 < baseStart_5829113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829130 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5829130 : Nat := 118140960795 + 5829130 * 2 ^ 59
def prefixEnd_5829130 : Nat := 4983230072969 + 3 ^ 40 * 5829130 * 2
def baseEnd_5829130 : Nat := 2993145487542883735767325

theorem tailTrace_5829130 : CollatzResearch.WordTrace tailWord_5829130 prefixEnd_5829130 2993145487542883735767325 := by
  unfold tailWord_5829130
  simp only [CollatzResearch.WordTrace]
  refine ⟨53151459343016255247607211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141737224914710013993619229 53151459343016255247607211)
  ·
    refine ⟨79727189014524382871410817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53151459343016255247607211 79727189014524382871410817)
    ·
      refine ⟨59795391760893287153558113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79727189014524382871410817 59795391760893287153558113)
      ·
        refine ⟨44846543820669965365168585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59795391760893287153558113 44846543820669965365168585)
        ·
          refine ⟨33634907865502474023876439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44846543820669965365168585 33634907865502474023876439)
          ·
            refine ⟨50452361798253711035814659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33634907865502474023876439 50452361798253711035814659)
            ·
              refine ⟨75678542697380566553721989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50452361798253711035814659 75678542697380566553721989)
              ·
                refine ⟨14189726755758856228822873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75678542697380566553721989 14189726755758856228822873)
                ·
                  refine ⟨10642295066819142171617155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14189726755758856228822873 10642295066819142171617155)
                  ·
                    refine ⟨15963442600228713257425733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10642295066819142171617155 15963442600228713257425733)
                    ·
                      refine ⟨2993145487542883735767325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15963442600228713257425733 2993145487542883735767325)
                      ·
                        rfl

theorem cell23_5829130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5829130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829130 prefixEnd_5829130 := by exact prefixLift 5829130
  have htrace : WordTrace (prefixWord ++ tailWord_5829130) baseStart_5829130 baseEnd_5829130 := by
    simpa [prefixWord, tailWord_5829130, baseEnd_5829130] using wordTrace_append hprefix tailTrace_5829130
  have hstable : (prefixWord ++ tailWord_5829130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829130).length < 2 ^ (prefixWord ++ tailWord_5829130).sum := by decide
  have hdescent : baseEnd_5829130 < baseStart_5829130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829217 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_5829217 : Nat := 118140960795 + 5829217 * 2 ^ 59
def prefixEnd_5829217 : Nat := 4983230072969 + 3 ^ 40 * 5829217 * 2
def baseEnd_5829217 : Nat := 997730053453274965126475

theorem tailTrace_5829217 : CollatzResearch.WordTrace tailWord_5829217 prefixEnd_5829217 997730053453274965126475 := by
  unfold tailWord_5829217
  simp only [CollatzResearch.WordTrace]
  refine ⟨212609010522749834848845905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141739340348499889899230603 212609010522749834848845905)
  ·
    refine ⟨159456757892062376136634429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212609010522749834848845905 159456757892062376136634429)
    ·
      refine ⟨59796284209523391051237911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159456757892062376136634429 59796284209523391051237911)
      ·
        refine ⟨89694426314285086576856867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59796284209523391051237911 89694426314285086576856867)
        ·
          refine ⟨134541639471427629865285301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89694426314285086576856867 134541639471427629865285301)
          ·
            refine ⟨12613278700446340299870497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134541639471427629865285301 12613278700446340299870497)
            ·
              refine ⟨9459959025334755224902873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12613278700446340299870497 9459959025334755224902873)
              ·
                refine ⟨7094969269001066418677155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9459959025334755224902873 7094969269001066418677155)
                ·
                  refine ⟨10642453903501599628015733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094969269001066418677155 10642453903501599628015733)
                  ·
                    refine ⟨997730053453274965126475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10642453903501599628015733 997730053453274965126475)
                    ·
                      rfl

theorem cell23_5829217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_5829217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829217 prefixEnd_5829217 := by exact prefixLift 5829217
  have htrace : WordTrace (prefixWord ++ tailWord_5829217) baseStart_5829217 baseEnd_5829217 := by
    simpa [prefixWord, tailWord_5829217, baseEnd_5829217] using wordTrace_append hprefix tailTrace_5829217
  have hstable : (prefixWord ++ tailWord_5829217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829217).length < 2 ^ (prefixWord ++ tailWord_5829217).sum := by decide
  have hdescent : baseEnd_5829217 < baseStart_5829217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829318 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5829318 : Nat := 118140960795 + 5829318 * 2 ^ 59
def prefixEnd_5829318 : Nat := 4983230072969 + 3 ^ 40 * 5829318 * 2
def baseEnd_5829318 : Nat := 2993242021905929000216461

theorem tailTrace_5829318 : CollatzResearch.WordTrace tailWord_5829318 prefixEnd_5829318 2993242021905929000216461 := by
  unfold tailWord_5829318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644146696730747784321019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141741796196922619398848405 6644146696730747784321019)
  ·
    refine ⟨9966220045096121676481529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644146696730747784321019 9966220045096121676481529)
    ·
      refine ⟨7474665033822091257361147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9966220045096121676481529 7474665033822091257361147)
      ·
        refine ⟨11211997550733136886041721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474665033822091257361147 11211997550733136886041721)
        ·
          refine ⟨8408998163049852664531291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11211997550733136886041721 8408998163049852664531291)
          ·
            refine ⟨12613497244574778996796937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408998163049852664531291 12613497244574778996796937)
            ·
              refine ⟨9460122933431084247597703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12613497244574778996796937 9460122933431084247597703)
              ·
                refine ⟨14190184400146626371396555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460122933431084247597703 14190184400146626371396555)
                ·
                  refine ⟨21285276600219939557094833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14190184400146626371396555 21285276600219939557094833)
                  ·
                    refine ⟨15963957450164954667821125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21285276600219939557094833 15963957450164954667821125)
                    ·
                      refine ⟨2993242021905929000216461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15963957450164954667821125 2993242021905929000216461)
                      ·
                        rfl

theorem cell23_5829318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5829318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829318 prefixEnd_5829318 := by exact prefixLift 5829318
  have htrace : WordTrace (prefixWord ++ tailWord_5829318) baseStart_5829318 baseEnd_5829318 := by
    simpa [prefixWord, tailWord_5829318, baseEnd_5829318] using wordTrace_append hprefix tailTrace_5829318
  have hstable : (prefixWord ++ tailWord_5829318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829318).length < 2 ^ (prefixWord ++ tailWord_5829318).sum := by decide
  have hdescent : baseEnd_5829318 < baseStart_5829318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829320 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_5829320 : Nat := 118140960795 + 5829320 * 2 ^ 59
def prefixEnd_5829320 : Nat := 4983230072969 + 3 ^ 40 * 5829320 * 2
def baseEnd_5829320 : Nat := 997747682955745997463817

theorem tailTrace_5829320 : CollatzResearch.WordTrace tailWord_5829320 prefixEnd_5829320 997747682955745997463817 := by
  unfold tailWord_5829320
  simp only [CollatzResearch.WordTrace]
  refine ⟨106306383620688341719922707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141741844827584455626563609 106306383620688341719922707)
  ·
    refine ⟨159459575431032512579884061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106306383620688341719922707 159459575431032512579884061)
    ·
      refine ⟨59797340786637192217456523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159459575431032512579884061 59797340786637192217456523)
      ·
        refine ⟨89696011179955788326184785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59797340786637192217456523 89696011179955788326184785)
        ·
          refine ⟨67272008384966841244638589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89696011179955788326184785 67272008384966841244638589)
          ·
            refine ⟨25227003144362565466739471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67272008384966841244638589 25227003144362565466739471)
            ·
              refine ⟨37840504716543848200109207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25227003144362565466739471 37840504716543848200109207)
              ·
                refine ⟨56760757074815772300163811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37840504716543848200109207 56760757074815772300163811)
                ·
                  refine ⟨85141135612223658450245717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56760757074815772300163811 85141135612223658450245717)
                  ·
                    refine ⟨997747682955745997463817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85141135612223658450245717 997747682955745997463817)
                    ·
                      rfl

theorem cell23_5829320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_5829320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829320 prefixEnd_5829320 := by exact prefixLift 5829320
  have htrace : WordTrace (prefixWord ++ tailWord_5829320) baseStart_5829320 baseEnd_5829320 := by
    simpa [prefixWord, tailWord_5829320, baseEnd_5829320] using wordTrace_append hprefix tailTrace_5829320
  have hstable : (prefixWord ++ tailWord_5829320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829320).length < 2 ^ (prefixWord ++ tailWord_5829320).sum := by decide
  have hdescent : baseEnd_5829320 < baseStart_5829320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829344 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2]
def baseStart_5829344 : Nat := 118140960795 + 5829344 * 2 ^ 59
def prefixEnd_5829344 : Nat := 4983230072969 + 3 ^ 40 * 5829344 * 2
def baseEnd_5829344 : Nat := 2993255372402945898491341

theorem tailTrace_5829344 : CollatzResearch.WordTrace tailWord_5829344 prefixEnd_5829344 2993255372402945898491341 := by
  unfold tailWord_5829344
  simp only [CollatzResearch.WordTrace]
  refine ⟨106306821296644867769359543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141742428395526490359146057 106306821296644867769359543)
  ·
    refine ⟨159460231944967301654039315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106306821296644867769359543 159460231944967301654039315)
    ·
      refine ⟨239190347917450952481058973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159460231944967301654039315 239190347917450952481058973)
      ·
        refine ⟨89696380469044107180397115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239190347917450952481058973 89696380469044107180397115)
        ·
          refine ⟨134544570703566160770595673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89696380469044107180397115 134544570703566160770595673)
          ·
            refine ⟨100908428027674620577946755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134544570703566160770595673 100908428027674620577946755)
            ·
              refine ⟨151362642041511930866920133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100908428027674620577946755 151362642041511930866920133)
              ·
                refine ⟨28380495382783487037547525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151362642041511930866920133 28380495382783487037547525)
                ·
                  refine ⟨5321342884271903819540161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28380495382783487037547525 5321342884271903819540161)
                  ·
                    refine ⟨3991007163203927864655121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321342884271903819540161 3991007163203927864655121)
                    ·
                      refine ⟨2993255372402945898491341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991007163203927864655121 2993255372402945898491341)
                      ·
                        rfl

theorem cell23_5829344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_5829344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829344 prefixEnd_5829344 := by exact prefixLift 5829344
  have htrace : WordTrace (prefixWord ++ tailWord_5829344) baseStart_5829344 baseEnd_5829344 := by
    simpa [prefixWord, tailWord_5829344, baseEnd_5829344] using wordTrace_append hprefix tailTrace_5829344
  have hstable : (prefixWord ++ tailWord_5829344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829344).length < 2 ^ (prefixWord ++ tailWord_5829344).sum := by decide
  have hdescent : baseEnd_5829344 < baseStart_5829344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829348 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_5829348 : Nat := 118140960795 + 5829348 * 2 ^ 59
def prefixEnd_5829348 : Nat := 4983230072969 + 3 ^ 40 * 5829348 * 2
def baseEnd_5829348 : Nat := 2993257426325563882841323

theorem tailTrace_5829348 : CollatzResearch.WordTrace tailWord_5829348 prefixEnd_5829348 2993257426325563882841323 := by
  unfold tailWord_5829348
  simp only [CollatzResearch.WordTrace]
  refine ⟨106306894242637622110932349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141742525656850162814576465 106306894242637622110932349)
  ·
    refine ⟨39865085340989108291599631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106306894242637622110932349 39865085340989108291599631)
    ·
      refine ⟨59797628011483662437399447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39865085340989108291599631 59797628011483662437399447)
      ·
        refine ⟨89696442017225493656099171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59797628011483662437399447 89696442017225493656099171)
        ·
          refine ⟨134544663025838240484148757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89696442017225493656099171 134544663025838240484148757)
          ·
            refine ⟨6306781079336167522694473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134544663025838240484148757 6306781079336167522694473)
            ·
              refine ⟨4730085809502125642020855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6306781079336167522694473 4730085809502125642020855)
              ·
                refine ⟨7095128714253188463031283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730085809502125642020855 7095128714253188463031283)
                ·
                  refine ⟨10642693071379782694546925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7095128714253188463031283 10642693071379782694546925)
                  ·
                    refine ⟨3991009901767418510455097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10642693071379782694546925 3991009901767418510455097)
                    ·
                      refine ⟨2993257426325563882841323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991009901767418510455097 2993257426325563882841323)
                      ·
                        rfl

theorem cell23_5829348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_5829348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829348 prefixEnd_5829348 := by exact prefixLift 5829348
  have htrace : WordTrace (prefixWord ++ tailWord_5829348) baseStart_5829348 baseEnd_5829348 := by
    simpa [prefixWord, tailWord_5829348, baseEnd_5829348] using wordTrace_append hprefix tailTrace_5829348
  have hstable : (prefixWord ++ tailWord_5829348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829348).length < 2 ^ (prefixWord ++ tailWord_5829348).sum := by decide
  have hdescent : baseEnd_5829348 < baseStart_5829348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829357 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5829357 : Nat := 118140960795 + 5829357 * 2 ^ 59
def prefixEnd_5829357 : Nat := 4983230072969 + 3 ^ 40 * 5829357 * 2
def baseEnd_5829357 : Nat := 2993262047651454347628781

theorem tailTrace_5829357 : CollatzResearch.WordTrace tailWord_5829357 prefixEnd_5829357 2993262047651454347628781 := by
  unfold tailWord_5829357
  simp only [CollatzResearch.WordTrace]
  refine ⟨212614116742242638758942325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141742744494828425839294883 212614116742242638758942325)
  ·
    refine ⟨19932573444585247383650843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212614116742242638758942325 19932573444585247383650843)
    ·
      refine ⟨29898860166877871075476265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19932573444585247383650843 29898860166877871075476265)
      ·
        refine ⟨22424145125158403306607199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29898860166877871075476265 22424145125158403306607199)
        ·
          refine ⟨33636217687737604959910799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22424145125158403306607199 33636217687737604959910799)
          ·
            refine ⟨50454326531606407439866199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33636217687737604959910799 50454326531606407439866199)
            ·
              refine ⟨75681489797409611159799299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50454326531606407439866199 75681489797409611159799299)
              ·
                refine ⟨113522234696114416739698949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75681489797409611159799299 113522234696114416739698949)
                ·
                  refine ⟨21285419005521453138693553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113522234696114416739698949 21285419005521453138693553)
                  ·
                    refine ⟨15964064254141089854020165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21285419005521453138693553 15964064254141089854020165)
                    ·
                      refine ⟨2993262047651454347628781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15964064254141089854020165 2993262047651454347628781)
                      ·
                        rfl

theorem cell23_5829357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5829357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829357 prefixEnd_5829357 := by exact prefixLift 5829357
  have htrace : WordTrace (prefixWord ++ tailWord_5829357) baseStart_5829357 baseEnd_5829357 := by
    simpa [prefixWord, tailWord_5829357, baseEnd_5829357] using wordTrace_append hprefix tailTrace_5829357
  have hstable : (prefixWord ++ tailWord_5829357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829357).length < 2 ^ (prefixWord ++ tailWord_5829357).sum := by decide
  have hdescent : baseEnd_5829357 < baseStart_5829357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829374 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5829374 : Nat := 118140960795 + 5829374 * 2 ^ 59
def prefixEnd_5829374 : Nat := 4983230072969 + 3 ^ 40 * 5829374 * 2
def baseEnd_5829374 : Nat := 2993270776822580781116203

theorem tailTrace_5829374 : CollatzResearch.WordTrace tailWord_5829374 prefixEnd_5829374 2993270776822580781116203 := by
  unfold tailWord_5829374
  simp only [CollatzResearch.WordTrace]
  refine ⟨26576842097897631332788897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141743157855454033774874117 26576842097897631332788897)
  ·
    refine ⟨19932631573423223499591673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26576842097897631332788897 19932631573423223499591673)
    ·
      refine ⟨14949473680067417624693755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19932631573423223499591673 14949473680067417624693755)
      ·
        refine ⟨22424210520101126437040633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14949473680067417624693755 22424210520101126437040633)
        ·
          refine ⟨16818157890075844827780475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22424210520101126437040633 16818157890075844827780475)
          ·
            refine ⟨25227236835113767241670713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16818157890075844827780475 25227236835113767241670713)
            ·
              refine ⟨18920427626335325431253035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25227236835113767241670713 18920427626335325431253035)
              ·
                refine ⟨28380641439502988146879553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18920427626335325431253035 28380641439502988146879553)
                ·
                  refine ⟨21285481079627241110159665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28380641439502988146879553 21285481079627241110159665)
                  ·
                    refine ⟨15964110809720430832619749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21285481079627241110159665 15964110809720430832619749)
                    ·
                      refine ⟨2993270776822580781116203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15964110809720430832619749 2993270776822580781116203)
                      ·
                        rfl

theorem cell23_5829374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5829374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829374 prefixEnd_5829374 := by exact prefixLift 5829374
  have htrace : WordTrace (prefixWord ++ tailWord_5829374) baseStart_5829374 baseEnd_5829374 := by
    simpa [prefixWord, tailWord_5829374, baseEnd_5829374] using wordTrace_append hprefix tailTrace_5829374
  have hstable : (prefixWord ++ tailWord_5829374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829374).length < 2 ^ (prefixWord ++ tailWord_5829374).sum := by decide
  have hdescent : baseEnd_5829374 < baseStart_5829374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829378 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_5829378 : Nat := 118140960795 + 5829378 * 2 ^ 59
def prefixEnd_5829378 : Nat := 4983230072969 + 3 ^ 40 * 5829378 * 2
def baseEnd_5829378 : Nat := 2993272830745198765466185

theorem tailTrace_5829378 : CollatzResearch.WordTrace tailWord_5829378 prefixEnd_5829378 2993272830745198765466185 := by
  unfold tailWord_5829378
  simp only [CollatzResearch.WordTrace]
  refine ⟨53153720668791639836364197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141743255116777706230304525 53153720668791639836364197)
  ·
    refine ⟨9966322625398432469318287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53153720668791639836364197 9966322625398432469318287)
    ·
      refine ⟨14949483938097648703977431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9966322625398432469318287 14949483938097648703977431)
      ·
        refine ⟨22424225907146473055966147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14949483938097648703977431 22424225907146473055966147)
        ·
          refine ⟨33636338860719709583949221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22424225907146473055966147 33636338860719709583949221)
          ·
            refine ⟨6306813536384945546990479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33636338860719709583949221 6306813536384945546990479)
            ·
              refine ⟨9460220304577418320485719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306813536384945546990479 9460220304577418320485719)
              ·
                refine ⟨14190330456866127480728579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460220304577418320485719 14190330456866127480728579)
                ·
                  refine ⟨21285495685299191221092869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14190330456866127480728579 21285495685299191221092869)
                  ·
                    refine ⟨3991030440993598353954913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21285495685299191221092869 3991030440993598353954913)
                    ·
                      refine ⟨2993272830745198765466185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991030440993598353954913 2993272830745198765466185)
                      ·
                        rfl

theorem cell23_5829378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_5829378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829378 prefixEnd_5829378 := by exact prefixLift 5829378
  have htrace : WordTrace (prefixWord ++ tailWord_5829378) baseStart_5829378 baseEnd_5829378 := by
    simpa [prefixWord, tailWord_5829378, baseEnd_5829378] using wordTrace_append hprefix tailTrace_5829378
  have hstable : (prefixWord ++ tailWord_5829378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829378).length < 2 ^ (prefixWord ++ tailWord_5829378).sum := by decide
  have hdescent : baseEnd_5829378 < baseStart_5829378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829397 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_5829397 : Nat := 118140960795 + 5829397 * 2 ^ 59
def prefixEnd_5829397 : Nat := 4983230072969 + 3 ^ 40 * 5829397 * 2
def baseEnd_5829397 : Nat := 997760862292544730376199

theorem tailTrace_5829397 : CollatzResearch.WordTrace tailWord_5829397 prefixEnd_5829397 997760862292544730376199 := by
  unfold tailWord_5829397
  simp only [CollatzResearch.WordTrace]
  refine ⟨212615575662097725590398445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141743717108065150393598963 212615575662097725590398445)
  ·
    refine ⟨79730840873286647096399417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212615575662097725590398445 79730840873286647096399417)
    ·
      refine ⟨59798130654964985322299563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79730840873286647096399417 59798130654964985322299563)
      ·
        refine ⟨89697195982447477983449345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59798130654964985322299563 89697195982447477983449345)
        ·
          refine ⟨67272896986835608487587009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89697195982447477983449345 67272896986835608487587009)
          ·
            refine ⟨50454672740126706365690257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67272896986835608487587009 50454672740126706365690257)
            ·
              refine ⟨37841004555095029774267693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50454672740126706365690257 37841004555095029774267693)
              ·
                refine ⟨14190376708160636165350385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37841004555095029774267693 14190376708160636165350385)
                ·
                  refine ⟨10642782531120477124012789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14190376708160636165350385 10642782531120477124012789)
                  ·
                    refine ⟨997760862292544730376199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10642782531120477124012789 997760862292544730376199)
                    ·
                      rfl

theorem cell23_5829397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_5829397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829397 prefixEnd_5829397 := by exact prefixLift 5829397
  have htrace : WordTrace (prefixWord ++ tailWord_5829397) baseStart_5829397 baseEnd_5829397 := by
    simpa [prefixWord, tailWord_5829397, baseEnd_5829397] using wordTrace_append hprefix tailTrace_5829397
  have hstable : (prefixWord ++ tailWord_5829397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829397).length < 2 ^ (prefixWord ++ tailWord_5829397).sum := by decide
  have hdescent : baseEnd_5829397 < baseStart_5829397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829417 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_5829417 : Nat := 118140960795 + 5829417 * 2 ^ 59
def prefixEnd_5829417 : Nat := 4983230072969 + 3 ^ 40 * 5829417 * 2
def baseEnd_5829417 : Nat := 2993292856490724112878505

theorem tailTrace_5829417 : CollatzResearch.WordTrace tailWord_5829417 prefixEnd_5829417 2993292856490724112878505 := by
  unfold tailWord_5829417
  simp only [CollatzResearch.WordTrace]
  refine ⟨212616305122025269006126505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141744203414683512670751003 212616305122025269006126505)
  ·
    refine ⟨159462228841518951754594879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212616305122025269006126505 159462228841518951754594879)
    ·
      refine ⟨239193343262278427631892319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159462228841518951754594879 239193343262278427631892319)
      ·
        refine ⟨358790014893417641447838479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239193343262278427631892319 358790014893417641447838479)
        ·
          refine ⟨538185022340126462171757719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358790014893417641447838479 538185022340126462171757719)
          ·
            refine ⟨807277533510189693257636579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538185022340126462171757719 807277533510189693257636579)
            ·
              refine ⟨1210916300265284539886454869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807277533510189693257636579 1210916300265284539886454869)
              ·
                refine ⟨14190425393733803201794393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1210916300265284539886454869 14190425393733803201794393)
                ·
                  refine ⟨10642819045300352401345795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14190425393733803201794393 10642819045300352401345795)
                  ·
                    refine ⟨15964228567950528602018693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10642819045300352401345795 15964228567950528602018693)
                    ·
                      refine ⟨2993292856490724112878505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15964228567950528602018693 2993292856490724112878505)
                      ·
                        rfl

theorem cell23_5829417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_5829417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829417 prefixEnd_5829417 := by exact prefixLift 5829417
  have htrace : WordTrace (prefixWord ++ tailWord_5829417) baseStart_5829417 baseEnd_5829417 := by
    simpa [prefixWord, tailWord_5829417, baseEnd_5829417] using wordTrace_append hprefix tailTrace_5829417
  have hstable : (prefixWord ++ tailWord_5829417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829417).length < 2 ^ (prefixWord ++ tailWord_5829417).sum := by decide
  have hdescent : baseEnd_5829417 < baseStart_5829417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829418 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_5829418 : Nat := 118140960795 + 5829418 * 2 ^ 59
def prefixEnd_5829418 : Nat := 4983230072969 + 3 ^ 40 * 5829418 * 2
def baseEnd_5829418 : Nat := 332588152219042067662889

theorem tailTrace_5829418 : CollatzResearch.WordTrace tailWord_5829418 prefixEnd_5829418 332588152219042067662889 := by
  unfold tailWord_5829418
  simp only [CollatzResearch.WordTrace]
  refine ⟨53154085398755411544228227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141744227730014430784608605 53154085398755411544228227)
  ·
    refine ⟨79731128098133117316342341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53154085398755411544228227 79731128098133117316342341)
    ·
      refine ⟨14949586518399959496814189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79731128098133117316342341 14949586518399959496814189)
      ·
        refine ⟨5606094944399984811305321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14949586518399959496814189 5606094944399984811305321)
        ·
          refine ⟨4204571208299988608478991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606094944399984811305321 4204571208299988608478991)
          ·
            refine ⟨6306856812449982912718487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204571208299988608478991 6306856812449982912718487)
            ·
              refine ⟨9460285218674974369077731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306856812449982912718487 9460285218674974369077731)
              ·
                refine ⟨14190427828012461553616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460285218674974369077731 14190427828012461553616597)
                ·
                  refine ⟨332588152219042067662889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14190427828012461553616597 332588152219042067662889)
                  ·
                    rfl

theorem cell23_5829418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_5829418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829418 prefixEnd_5829418 := by exact prefixLift 5829418
  have htrace : WordTrace (prefixWord ++ tailWord_5829418) baseStart_5829418 baseEnd_5829418 := by
    simpa [prefixWord, tailWord_5829418, baseEnd_5829418] using wordTrace_append hprefix tailTrace_5829418
  have hstable : (prefixWord ++ tailWord_5829418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829418).length < 2 ^ (prefixWord ++ tailWord_5829418).sum := by decide
  have hdescent : baseEnd_5829418 < baseStart_5829418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829461 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_5829461 : Nat := 118140960795 + 5829461 * 2 ^ 59
def prefixEnd_5829461 : Nat := 4983230072969 + 3 ^ 40 * 5829461 * 2
def baseEnd_5829461 : Nat := 997771816546507313576101

theorem tailTrace_5829461 : CollatzResearch.WordTrace tailWord_5829461 prefixEnd_5829461 997771816546507313576101 := by
  unfold tailWord_5829461
  simp only [CollatzResearch.WordTrace]
  refine ⟨212617909933865864520728237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141745273289243909680485491 212617909933865864520728237)
  ·
    refine ⟨79731716225199699195273089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212617909933865864520728237 79731716225199699195273089)
    ·
      refine ⟨59798787168899774396454817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79731716225199699195273089 59798787168899774396454817)
      ·
        refine ⟨44849090376674830797341113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59798787168899774396454817 44849090376674830797341113)
        ·
          refine ⟨33636817782506123098005835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44849090376674830797341113 33636817782506123098005835)
          ·
            refine ⟨50455226673759184647008753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33636817782506123098005835 50455226673759184647008753)
            ·
              refine ⟨37841420005319388485256565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50455226673759184647008753 37841420005319388485256565)
              ·
                refine ⟨3547633125498692670492803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37841420005319388485256565 3547633125498692670492803)
                ·
                  refine ⟨5321449688248039005739205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547633125498692670492803 5321449688248039005739205)
                  ·
                    refine ⟨997771816546507313576101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321449688248039005739205 997771816546507313576101)
                    ·
                      rfl

theorem cell23_5829461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_5829461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829461 prefixEnd_5829461 := by exact prefixLift 5829461
  have htrace : WordTrace (prefixWord ++ tailWord_5829461) baseStart_5829461 baseEnd_5829461 := by
    simpa [prefixWord, tailWord_5829461, baseEnd_5829461] using wordTrace_append hprefix tailTrace_5829461
  have hstable : (prefixWord ++ tailWord_5829461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829461).length < 2 ^ (prefixWord ++ tailWord_5829461).sum := by decide
  have hdescent : baseEnd_5829461 < baseStart_5829461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829511 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_5829511 : Nat := 118140960795 + 5829511 * 2 ^ 59
def prefixEnd_5829511 : Nat := 4983230072969 + 3 ^ 40 * 5829511 * 2
def baseEnd_5829511 : Nat := 2993341123672246745103073

theorem tailTrace_5829511 : CollatzResearch.WordTrace tailWord_5829511 prefixEnd_5829511 2993341123672246745103073 := by
  unfold tailWord_5829511
  simp only [CollatzResearch.WordTrace]
  refine ⟨212619733583684723060048387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141746489055789815373365591 212619733583684723060048387)
  ·
    refine ⟨318929600375527084590072581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212619733583684723060048387 318929600375527084590072581)
    ·
      refine ⟨59799300070411328360638609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318929600375527084590072581 59799300070411328360638609)
      ·
        refine ⟨44849475052808496270478957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59799300070411328360638609 44849475052808496270478957)
        ·
          refine ⟨16818553144803186101429609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44849475052808496270478957 16818553144803186101429609)
          ·
            refine ⟨12613914858602389576072207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16818553144803186101429609 12613914858602389576072207)
            ·
              refine ⟨18920872287903584364108311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12613914858602389576072207 18920872287903584364108311)
              ·
                refine ⟨28381308431855376546162467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18920872287903584364108311 28381308431855376546162467)
                ·
                  refine ⟨42571962647783064819243701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28381308431855376546162467 42571962647783064819243701)
                  ·
                    refine ⟨3991121498229662326804097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42571962647783064819243701 3991121498229662326804097)
                    ·
                      refine ⟨2993341123672246745103073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991121498229662326804097 2993341123672246745103073)
                      ·
                        rfl

theorem cell23_5829511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_5829511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829511 prefixEnd_5829511 := by exact prefixLift 5829511
  have htrace : WordTrace (prefixWord ++ tailWord_5829511) baseStart_5829511 baseEnd_5829511 := by
    simpa [prefixWord, tailWord_5829511, baseEnd_5829511] using wordTrace_append hprefix tailTrace_5829511
  have hstable : (prefixWord ++ tailWord_5829511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829511).length < 2 ^ (prefixWord ++ tailWord_5829511).sum := by decide
  have hdescent : baseEnd_5829511 < baseStart_5829511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829561 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5829561 : Nat := 118140960795 + 5829561 * 2 ^ 59
def prefixEnd_5829561 : Nat := 4983230072969 + 3 ^ 40 * 5829561 * 2
def baseEnd_5829561 : Nat := 2993366797704971549477843

theorem tailTrace_5829561 : CollatzResearch.WordTrace tailWord_5829561 prefixEnd_5829561 2993366797704971549477843 := by
  unfold tailWord_5829561
  simp only [CollatzResearch.WordTrace]
  refine ⟨212621557233503581599368537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141747704822335721066245691 212621557233503581599368537)
  ·
    refine ⟨159466167925127686199526403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212621557233503581599368537 159466167925127686199526403)
    ·
      refine ⟨239199251887691529299289605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159466167925127686199526403 239199251887691529299289605)
      ·
        refine ⟨44849859728942161743616801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239199251887691529299289605 44849859728942161743616801)
        ·
          refine ⟨33637394796706621307712601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44849859728942161743616801 33637394796706621307712601)
          ·
            refine ⟨25228046097529965980784451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33637394796706621307712601 25228046097529965980784451)
            ·
              refine ⟨37842069146294948971176677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25228046097529965980784451 37842069146294948971176677)
              ·
                refine ⟨7095387964930302932095627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37842069146294948971176677 7095387964930302932095627)
                ·
                  refine ⟨10643081947395454398143441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7095387964930302932095627 10643081947395454398143441)
                  ·
                    refine ⟨7982311460546590798607581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10643081947395454398143441 7982311460546590798607581)
                    ·
                      refine ⟨2993366797704971549477843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7982311460546590798607581 2993366797704971549477843)
                      ·
                        rfl

theorem cell23_5829561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5829561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829561 prefixEnd_5829561 := by exact prefixLift 5829561
  have htrace : WordTrace (prefixWord ++ tailWord_5829561) baseStart_5829561 baseEnd_5829561 := by
    simpa [prefixWord, tailWord_5829561, baseEnd_5829561] using wordTrace_append hprefix tailTrace_5829561
  have hstable : (prefixWord ++ tailWord_5829561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829561).length < 2 ^ (prefixWord ++ tailWord_5829561).sum := by decide
  have hdescent : baseEnd_5829561 < baseStart_5829561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829575 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_5829575 : Nat := 118140960795 + 5829575 * 2 ^ 59
def prefixEnd_5829575 : Nat := 4983230072969 + 3 ^ 40 * 5829575 * 2
def baseEnd_5829575 : Nat := 2993373986434134494702779

theorem tailTrace_5829575 : CollatzResearch.WordTrace tailWord_5829575 prefixEnd_5829575 2993373986434134494702779 := by
  unfold tailWord_5829575
  simp only [CollatzResearch.WordTrace]
  refine ⟨212622067855452861990378179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141748045236968574660252119 212622067855452861990378179)
  ·
    refine ⟨318933101783179292985567269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212622067855452861990378179 318933101783179292985567269)
    ·
      refine ⟨59799956584346117434793863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318933101783179292985567269 59799956584346117434793863)
      ·
        refine ⟨89699934876519176152190795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59799956584346117434793863 89699934876519176152190795)
        ·
          refine ⟨134549902314778764228286193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89699934876519176152190795 134549902314778764228286193)
          ·
            refine ⟨100912426736084073171214645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134549902314778764228286193 100912426736084073171214645)
            ·
              refine ⟨9460540006507881859801373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100912426736084073171214645 9460540006507881859801373)
              ·
                refine ⟨3547702502440455697425515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9460540006507881859801373 3547702502440455697425515)
                ·
                  refine ⟨5321553753660683546138273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547702502440455697425515 5321553753660683546138273)
                  ·
                    refine ⟨3991165315245512659603705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321553753660683546138273 3991165315245512659603705)
                    ·
                      refine ⟨2993373986434134494702779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991165315245512659603705 2993373986434134494702779)
                      ·
                        rfl

theorem cell23_5829575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_5829575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829575 prefixEnd_5829575 := by exact prefixLift 5829575
  have htrace : WordTrace (prefixWord ++ tailWord_5829575) baseStart_5829575 baseEnd_5829575 := by
    simpa [prefixWord, tailWord_5829575, baseEnd_5829575] using wordTrace_append hprefix tailTrace_5829575
  have hstable : (prefixWord ++ tailWord_5829575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829575).length < 2 ^ (prefixWord ++ tailWord_5829575).sum := by decide
  have hdescent : baseEnd_5829575 < baseStart_5829575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829592 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 1, 2, 2]
def baseStart_5829592 : Nat := 118140960795 + 5829592 * 2 ^ 59
def prefixEnd_5829592 : Nat := 4983230072969 + 3 ^ 40 * 5829592 * 2
def baseEnd_5829592 : Nat := 2993382715605260928190201

theorem tailTrace_5829592 : CollatzResearch.WordTrace tailWord_5829592 prefixEnd_5829592 2993382715605260928190201 := by
  unfold tailWord_5829592
  simp only [CollatzResearch.WordTrace]
  refine ⟨106311343948195636946873515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141748458597594182595831353 106311343948195636946873515)
  ·
    refine ⟨159467015922293455420310273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106311343948195636946873515 159467015922293455420310273)
    ·
      refine ⟨119600261941720091565232705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159467015922293455420310273 119600261941720091565232705)
      ·
        refine ⟨89700196456290068673924529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119600261941720091565232705 89700196456290068673924529)
        ·
          refine ⟨67275147342217551505443397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89700196456290068673924529 67275147342217551505443397)
          ·
            refine ⟨12614090126665790907270637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67275147342217551505443397 12614090126665790907270637)
            ·
              refine ⟨4730283797499671590226489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12614090126665790907270637 4730283797499671590226489)
              ·
                refine ⟨3547712848124753692669867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4730283797499671590226489 3547712848124753692669867)
                ·
                  refine ⟨5321569272187130539004801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547712848124753692669867 5321569272187130539004801)
                  ·
                    refine ⟨3991176954140347904253601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321569272187130539004801 3991176954140347904253601)
                    ·
                      refine ⟨2993382715605260928190201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991176954140347904253601 2993382715605260928190201)
                      ·
                        rfl

theorem cell23_5829592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_5829592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829592 prefixEnd_5829592 := by exact prefixLift 5829592
  have htrace : WordTrace (prefixWord ++ tailWord_5829592) baseStart_5829592 baseEnd_5829592 := by
    simpa [prefixWord, tailWord_5829592, baseEnd_5829592] using wordTrace_append hprefix tailTrace_5829592
  have hstable : (prefixWord ++ tailWord_5829592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829592).length < 2 ^ (prefixWord ++ tailWord_5829592).sum := by decide
  have hdescent : baseEnd_5829592 < baseStart_5829592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829601 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_5829601 : Nat := 118140960795 + 5829601 * 2 ^ 59
def prefixEnd_5829601 : Nat := 4983230072969 + 3 ^ 40 * 5829601 * 2
def baseEnd_5829601 : Nat := 2993387336931151392977659

theorem tailTrace_5829601 : CollatzResearch.WordTrace tailWord_5829601 prefixEnd_5829601 2993387336931151392977659 := by
  unfold tailWord_5829601
  simp only [CollatzResearch.WordTrace]
  refine ⟨212623016153358668430824657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141748677435572445620549771 212623016153358668430824657)
  ·
    refine ⟨159467262115019001323118493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212623016153358668430824657 159467262115019001323118493)
    ·
      refine ⟨59800223293132125496169435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159467262115019001323118493 59800223293132125496169435)
      ·
        refine ⟨89700334939698188244254153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59800223293132125496169435 89700334939698188244254153)
        ·
          refine ⟨67275251204773641183190615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89700334939698188244254153 67275251204773641183190615)
          ·
            refine ⟨100912876807160461774785923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67275251204773641183190615 100912876807160461774785923)
            ·
              refine ⟨151369315210740692662178885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100912876807160461774785923 151369315210740692662178885)
              ·
                refine ⟨28381746602013879874158541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151369315210740692662178885 28381746602013879874158541)
                ·
                  refine ⟨10643154975755204952809453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28381746602013879874158541 10643154975755204952809453)
                  ·
                    refine ⟨3991183115908201857303545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10643154975755204952809453 3991183115908201857303545)
                    ·
                      refine ⟨2993387336931151392977659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991183115908201857303545 2993387336931151392977659)
                      ·
                        rfl

theorem cell23_5829601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_5829601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829601 prefixEnd_5829601 := by exact prefixLift 5829601
  have htrace : WordTrace (prefixWord ++ tailWord_5829601) baseStart_5829601 baseEnd_5829601 := by
    simpa [prefixWord, tailWord_5829601, baseEnd_5829601] using wordTrace_append hprefix tailTrace_5829601
  have hstable : (prefixWord ++ tailWord_5829601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829601).length < 2 ^ (prefixWord ++ tailWord_5829601).sum := by decide
  have hdescent : baseEnd_5829601 < baseStart_5829601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829602 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5829602 : Nat := 118140960795 + 5829602 * 2 ^ 59
def prefixEnd_5829602 : Nat := 4983230072969 + 3 ^ 40 * 5829602 * 2
def baseEnd_5829602 : Nat := 997795950137268629688385

theorem tailTrace_5829602 : CollatzResearch.WordTrace tailWord_5829602 prefixEnd_5829602 997795950137268629688385 := by
  unfold tailWord_5829602
  simp only [CollatzResearch.WordTrace]
  refine ⟨53155763156588761400402765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141748701750903363734407373 53155763156588761400402765)
  ·
    refine ⟨19933411183720785525151037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53155763156588761400402765 19933411183720785525151037)
    ·
      refine ⟨7475029193895294571931639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19933411183720785525151037 7475029193895294571931639)
      ·
        refine ⟨11212543790842941857897459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475029193895294571931639 11212543790842941857897459)
        ·
          refine ⟨16818815686264412786846189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11212543790842941857897459 16818815686264412786846189)
          ·
            refine ⟨6307055882349154795067321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16818815686264412786846189 6307055882349154795067321)
            ·
              refine ⟨4730291911761866096300491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6307055882349154795067321 4730291911761866096300491)
              ·
                refine ⟨7095437867642799144450737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730291911761866096300491 7095437867642799144450737)
                ·
                  refine ⟨5321578400732099358338053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7095437867642799144450737 5321578400732099358338053)
                  ·
                    refine ⟨997795950137268629688385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321578400732099358338053 997795950137268629688385)
                    ·
                      rfl

theorem cell23_5829602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5829602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829602 prefixEnd_5829602 := by exact prefixLift 5829602
  have htrace : WordTrace (prefixWord ++ tailWord_5829602) baseStart_5829602 baseEnd_5829602 := by
    simpa [prefixWord, tailWord_5829602, baseEnd_5829602] using wordTrace_append hprefix tailTrace_5829602
  have hstable : (prefixWord ++ tailWord_5829602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829602).length < 2 ^ (prefixWord ++ tailWord_5829602).sum := by decide
  have hdescent : baseEnd_5829602 < baseStart_5829602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829665 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5829665 : Nat := 118140960795 + 5829665 * 2 ^ 59
def prefixEnd_5829665 : Nat := 4983230072969 + 3 ^ 40 * 5829665 * 2
def baseEnd_5829665 : Nat := 2993420199693039142577365

theorem tailTrace_5829665 : CollatzResearch.WordTrace tailWord_5829665 prefixEnd_5829665 2993420199693039142577365 := by
  unfold tailWord_5829665
  simp only [CollatzResearch.WordTrace]
  refine ⟨212625350425126807361154449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141750233616751204907436299 212625350425126807361154449)
  ·
    refine ⟨159469012818845105520865837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212625350425126807361154449 159469012818845105520865837)
    ·
      refine ⟨59800879807066914570324689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159469012818845105520865837 59800879807066914570324689)
      ·
        refine ⟨44850659855300185927743517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59800879807066914570324689 44850659855300185927743517)
        ·
          refine ⟨16818997445737569722903819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44850659855300185927743517 16818997445737569722903819)
          ·
            refine ⟨25228496168606354584355729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16818997445737569722903819 25228496168606354584355729)
            ·
              refine ⟨18921372126454765938266797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25228496168606354584355729 18921372126454765938266797)
              ·
                refine ⟨7095514547420537226850049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18921372126454765938266797 7095514547420537226850049)
                ·
                  refine ⟨5321635910565402920137537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7095514547420537226850049 5321635910565402920137537)
                  ·
                    refine ⟨3991226932924052190103153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321635910565402920137537 3991226932924052190103153)
                    ·
                      refine ⟨2993420199693039142577365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991226932924052190103153 2993420199693039142577365)
                      ·
                        rfl

theorem cell23_5829665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5829665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829665 prefixEnd_5829665 := by exact prefixLift 5829665
  have htrace : WordTrace (prefixWord ++ tailWord_5829665) baseStart_5829665 baseEnd_5829665 := by
    simpa [prefixWord, tailWord_5829665, baseEnd_5829665] using wordTrace_append hprefix tailTrace_5829665
  have hstable : (prefixWord ++ tailWord_5829665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829665).length < 2 ^ (prefixWord ++ tailWord_5829665).sum := by decide
  have hdescent : baseEnd_5829665 < baseStart_5829665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829671 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 9]
def baseStart_5829671 : Nat := 118140960795 + 5829671 * 2 ^ 59
def prefixEnd_5829671 : Nat := 4983230072969 + 3 ^ 40 * 5829671 * 2
def baseEnd_5829671 : Nat := 332602586730774013233593

theorem tailTrace_5829671 : CollatzResearch.WordTrace tailWord_5829671 prefixEnd_5829671 332602586730774013233593 := by
  unfold tailWord_5829671
  simp only [CollatzResearch.WordTrace]
  refine ⟨212625569263105070385872867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141750379508736713590581911 212625569263105070385872867)
  ·
    refine ⟨318938353894657605578809301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212625569263105070385872867 318938353894657605578809301)
    ·
      refine ⟨7475117669406037630753343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 318938353894657605578809301 7475117669406037630753343)
      ·
        refine ⟨11212676504109056446130015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475117669406037630753343 11212676504109056446130015)
        ·
          refine ⟨16819014756163584669195023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11212676504109056446130015 16819014756163584669195023)
          ·
            refine ⟨25228522134245377003792535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16819014756163584669195023 25228522134245377003792535)
            ·
              refine ⟨37842783201368065505688803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25228522134245377003792535 37842783201368065505688803)
              ·
                refine ⟨56764174802052098258533205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37842783201368065505688803 56764174802052098258533205)
                ·
                  refine ⟨332602586730774013233593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56764174802052098258533205 332602586730774013233593)
                  ·
                    rfl

theorem cell23_5829671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 9].length) (baseStart_5829671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829671 prefixEnd_5829671 := by exact prefixLift 5829671
  have htrace : WordTrace (prefixWord ++ tailWord_5829671) baseStart_5829671 baseEnd_5829671 := by
    simpa [prefixWord, tailWord_5829671, baseEnd_5829671] using wordTrace_append hprefix tailTrace_5829671
  have hstable : (prefixWord ++ tailWord_5829671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829671).length < 2 ^ (prefixWord ++ tailWord_5829671).sum := by decide
  have hdescent : baseEnd_5829671 < baseStart_5829671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829688 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 5]
def baseStart_5829688 : Nat := 118140960795 + 5829688 * 2 ^ 59
def prefixEnd_5829688 : Nat := 4983230072969 + 3 ^ 40 * 5829688 * 2
def baseEnd_5829688 : Nat := 332603556638676950287751

theorem tailTrace_5829688 : CollatzResearch.WordTrace tailWord_5829688 prefixEnd_5829688 332603556638676950287751 := by
  unfold tailWord_5829688
  simp only [CollatzResearch.WordTrace]
  refine ⟨106313094652021741144620859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141750792869362321526161145 106313094652021741144620859)
  ·
    refine ⟨159469641978032611716931289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106313094652021741144620859 159469641978032611716931289)
    ·
      refine ⟨119602231483524458787698467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159469641978032611716931289 119602231483524458787698467)
      ·
        refine ⟨179403347225286688181547701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119602231483524458787698467 179403347225286688181547701)
        ·
          refine ⟨16819063802370627017020097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179403347225286688181547701 16819063802370627017020097)
          ·
            refine ⟨12614297851777970262765073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16819063802370627017020097 12614297851777970262765073)
            ·
              refine ⟨9460723388833477697073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12614297851777970262765073 9460723388833477697073805)
              ·
                refine ⟨3547771270812554136402677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9460723388833477697073805 3547771270812554136402677)
                ·
                  refine ⟨332603556638676950287751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3547771270812554136402677 332603556638676950287751)
                  ·
                    rfl

theorem cell23_5829688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 5].length) (baseStart_5829688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829688 prefixEnd_5829688 := by exact prefixLift 5829688
  have htrace : WordTrace (prefixWord ++ tailWord_5829688) baseStart_5829688 baseEnd_5829688 := by
    simpa [prefixWord, tailWord_5829688, baseEnd_5829688] using wordTrace_append hprefix tailTrace_5829688
  have hstable : (prefixWord ++ tailWord_5829688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829688).length < 2 ^ (prefixWord ++ tailWord_5829688).sum := by decide
  have hdescent : baseEnd_5829688 < baseStart_5829688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829721 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 6, 2]
def baseStart_5829721 : Nat := 118140960795 + 5829721 * 2 ^ 59
def prefixEnd_5829721 : Nat := 4983230072969 + 3 ^ 40 * 5829721 * 2
def baseEnd_5829721 : Nat := 2993448954609690923477107

theorem tailTrace_5829721 : CollatzResearch.WordTrace tailWord_5829721 prefixEnd_5829721 2993448954609690923477107 := by
  unfold tailWord_5829721
  simp only [CollatzResearch.WordTrace]
  refine ⟨212627392912923928925193017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141751595275282619283462011 212627392912923928925193017)
  ·
    refine ⟨159470544684692946693894763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212627392912923928925193017 159470544684692946693894763)
    ·
      refine ⟨239205817027039420040842145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159470544684692946693894763 239205817027039420040842145)
      ·
        refine ⟨179404362770279565030631609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239205817027039420040842145 179404362770279565030631609)
        ·
          refine ⟨134553272077709673772973707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179404362770279565030631609 134553272077709673772973707)
          ·
            refine ⟨201829908116564510659460561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134553272077709673772973707 201829908116564510659460561)
            ·
              refine ⟨151372431087423382994595421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201829908116564510659460561 151372431087423382994595421)
              ·
                refine ⟨56764661657783768622973283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151372431087423382994595421 56764661657783768622973283)
                ·
                  refine ⟨85146992486675652934459925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56764661657783768622973283 85146992486675652934459925)
                  ·
                    refine ⟨3991265272812921231302809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85146992486675652934459925 3991265272812921231302809)
                    ·
                      refine ⟨2993448954609690923477107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991265272812921231302809 2993448954609690923477107)
                      ·
                        rfl

theorem cell23_5829721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_5829721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829721 prefixEnd_5829721 := by exact prefixLift 5829721
  have htrace : WordTrace (prefixWord ++ tailWord_5829721) baseStart_5829721 baseEnd_5829721 := by
    simpa [prefixWord, tailWord_5829721, baseEnd_5829721] using wordTrace_append hprefix tailTrace_5829721
  have hstable : (prefixWord ++ tailWord_5829721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829721).length < 2 ^ (prefixWord ++ tailWord_5829721).sum := by decide
  have hdescent : baseEnd_5829721 < baseStart_5829721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829744 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 10]
def baseStart_5829744 : Nat := 118140960795 + 5829744 * 2 ^ 59
def prefixEnd_5829744 : Nat := 4983230072969 + 3 ^ 40 * 5829744 * 2
def baseEnd_5829744 : Nat := 332606751629416037054389

theorem tailTrace_5829744 : CollatzResearch.WordTrace tailWord_5829744 prefixEnd_5829744 332606751629416037054389 := by
  unfold tailWord_5829744
  simp only [CollatzResearch.WordTrace]
  refine ⟨106314115895920301926640143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141752154527893735902186857 106314115895920301926640143)
  ·
    refine ⟨159471173843880452889960215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106314115895920301926640143 159471173843880452889960215)
    ·
      refine ⟨239206760765820679334940323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159471173843880452889960215 239206760765820679334940323)
      ·
        refine ⟨358810141148731019002410485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239206760765820679334940323 358810141148731019002410485)
        ·
          refine ⟨33638450732693533031475983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 358810141148731019002410485 33638450732693533031475983)
          ·
            refine ⟨50457676099040299547213975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33638450732693533031475983 50457676099040299547213975)
            ·
              refine ⟨75686514148560449320820963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50457676099040299547213975 75686514148560449320820963)
              ·
                refine ⟨113529771222840673981231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75686514148560449320820963 113529771222840673981231445)
                ·
                  refine ⟨332606751629416037054389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113529771222840673981231445 332606751629416037054389)
                  ·
                    rfl

theorem cell23_5829744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_5829744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829744 prefixEnd_5829744 := by exact prefixLift 5829744
  have htrace : WordTrace (prefixWord ++ tailWord_5829744) baseStart_5829744 baseEnd_5829744 := by
    simpa [prefixWord, tailWord_5829744, baseEnd_5829744] using wordTrace_append hprefix tailTrace_5829744
  have hstable : (prefixWord ++ tailWord_5829744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829744).length < 2 ^ (prefixWord ++ tailWord_5829744).sum := by decide
  have hdescent : baseEnd_5829744 < baseStart_5829744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829761 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 8]
def baseStart_5829761 : Nat := 118140960795 + 5829761 * 2 ^ 59
def prefixEnd_5829761 : Nat := 4983230072969 + 3 ^ 40 * 5829761 * 2
def baseEnd_5829761 : Nat := 332607721537318974108547

theorem tailTrace_5829761 : CollatzResearch.WordTrace tailWord_5829761 prefixEnd_5829761 332607721537318974108547 := by
  unfold tailWord_5829761
  simp only [CollatzResearch.WordTrace]
  refine ⟨212628851832779015756649137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141752567888519343837766091 212628851832779015756649137)
  ·
    refine ⟨159471638874584261817486853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212628851832779015756649137 159471638874584261817486853)
    ·
      refine ⟨29900932288984549090778785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159471638874584261817486853 29900932288984549090778785)
      ·
        refine ⟨22425699216738411818084089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29900932288984549090778785 22425699216738411818084089)
        ·
          refine ⟨16819274412553808863563067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22425699216738411818084089 16819274412553808863563067)
          ·
            refine ⟨25228911618830713295344601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16819274412553808863563067 25228911618830713295344601)
            ·
              refine ⟨18921683714123034971508451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25228911618830713295344601 18921683714123034971508451)
              ·
                refine ⟨28382525571184552457262677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18921683714123034971508451 28382525571184552457262677)
                ·
                  refine ⟨332607721537318974108547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28382525571184552457262677 332607721537318974108547)
                  ·
                    rfl

theorem cell23_5829761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_5829761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829761 prefixEnd_5829761 := by exact prefixLift 5829761
  have htrace : WordTrace (prefixWord ++ tailWord_5829761) baseStart_5829761 baseEnd_5829761 := by
    simpa [prefixWord, tailWord_5829761, baseEnd_5829761] using wordTrace_append hprefix tailTrace_5829761
  have hstable : (prefixWord ++ tailWord_5829761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829761).length < 2 ^ (prefixWord ++ tailWord_5829761).sum := by decide
  have hdescent : baseEnd_5829761 < baseStart_5829761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829765 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_5829765 : Nat := 118140960795 + 5829765 * 2 ^ 59
def prefixEnd_5829765 : Nat := 4983230072969 + 3 ^ 40 * 5829765 * 2
def baseEnd_5829765 : Nat := 997823849252829583775635

theorem tailTrace_5829765 : CollatzResearch.WordTrace tailWord_5829765 prefixEnd_5829765 997823849252829583775635 := by
  unfold tailWord_5829765
  simp only [CollatzResearch.WordTrace]
  refine ⟨212628997724764524439794749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141752665149843016293196499 212628997724764524439794749)
  ·
    refine ⟨79735874146786696664923031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212628997724764524439794749 79735874146786696664923031)
    ·
      refine ⟨119603811220180044997384547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79735874146786696664923031 119603811220180044997384547)
      ·
        refine ⟨179405716830270067496076821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119603811220180044997384547 179405716830270067496076821)
        ·
          refine ⟨8409642976418909413878601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179405716830270067496076821 8409642976418909413878601)
          ·
            refine ⟨6307232232314182060408951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8409642976418909413878601 6307232232314182060408951)
            ·
              refine ⟨9460848348471273090613427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6307232232314182060408951 9460848348471273090613427)
              ·
                refine ⟨14191272522706909635920141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460848348471273090613427 14191272522706909635920141)
                ·
                  refine ⟨5321727196015091113470053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14191272522706909635920141 5321727196015091113470053)
                  ·
                    refine ⟨997823849252829583775635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321727196015091113470053 997823849252829583775635)
                    ·
                      rfl

theorem cell23_5829765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_5829765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829765 prefixEnd_5829765 := by exact prefixLift 5829765
  have htrace : WordTrace (prefixWord ++ tailWord_5829765) baseStart_5829765 baseEnd_5829765 := by
    simpa [prefixWord, tailWord_5829765, baseEnd_5829765] using wordTrace_append hprefix tailTrace_5829765
  have hstable : (prefixWord ++ tailWord_5829765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829765).length < 2 ^ (prefixWord ++ tailWord_5829765).sum := by decide
  have hdescent : baseEnd_5829765 < baseStart_5829765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829778 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_5829778 : Nat := 118140960795 + 5829778 * 2 ^ 59
def prefixEnd_5829778 : Nat := 4983230072969 + 3 ^ 40 * 5829778 * 2
def baseEnd_5829778 : Nat := 332608691445221911162705

theorem tailTrace_5829778 : CollatzResearch.WordTrace tailWord_5829778 prefixEnd_5829778 332608691445221911162705 := by
  unfold tailWord_5829778
  simp only [CollatzResearch.WordTrace]
  refine ⟨53157367968429356915004497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141752981249144951773345325 53157367968429356915004497)
  ·
    refine ⟨39868025976322017686253373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53157367968429356915004497 39868025976322017686253373)
    ·
      refine ⟨14950509741120756632345015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39868025976322017686253373 14950509741120756632345015)
      ·
        refine ⟨22425764611681134948517523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14950509741120756632345015 22425764611681134948517523)
        ·
          refine ⟨33638646917521702422776285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22425764611681134948517523 33638646917521702422776285)
          ·
            refine ⟨12614492594070638408541107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33638646917521702422776285 12614492594070638408541107)
            ·
              refine ⟨18921738891105957612811661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12614492594070638408541107 18921738891105957612811661)
              ·
                refine ⟨7095652084164734104804373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18921738891105957612811661 7095652084164734104804373)
                ·
                  refine ⟨332608691445221911162705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7095652084164734104804373 332608691445221911162705)
                  ·
                    rfl

theorem cell23_5829778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_5829778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829778 prefixEnd_5829778 := by exact prefixLift 5829778
  have htrace : WordTrace (prefixWord ++ tailWord_5829778) baseStart_5829778 baseEnd_5829778 := by
    simpa [prefixWord, tailWord_5829778, baseEnd_5829778] using wordTrace_append hprefix tailTrace_5829778
  have hstable : (prefixWord ++ tailWord_5829778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829778).length < 2 ^ (prefixWord ++ tailWord_5829778).sum := by decide
  have hdescent : baseEnd_5829778 < baseStart_5829778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829831 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_5829831 : Nat := 118140960795 + 5829831 * 2 ^ 59
def prefixEnd_5829831 : Nat := 4983230072969 + 3 ^ 40 * 5829831 * 2
def baseEnd_5829831 : Nat := 2993505437481685493101601

theorem tailTrace_5829831 : CollatzResearch.WordTrace tailWord_5829831 prefixEnd_5829831 2993505437481685493101601 := by
  unfold tailWord_5829831
  simp only [CollatzResearch.WordTrace]
  refine ⟨212631404942525417711697347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141754269961683611807798231 212631404942525417711697347)
  ·
    refine ⟨318947107413788126567546021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212631404942525417711697347 318947107413788126567546021)
    ·
      refine ⟨59802582640085273731414879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318947107413788126567546021 59802582640085273731414879)
      ·
        refine ⟨89703873960127910597122319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59802582640085273731414879 89703873960127910597122319)
        ·
          refine ⟨134555810940191865895683479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89703873960127910597122319 134555810940191865895683479)
          ·
            refine ⟨201833716410287798843525219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134555810940191865895683479 201833716410287798843525219)
            ·
              refine ⟨302750574615431698265287829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201833716410287798843525219 302750574615431698265287829)
              ·
                refine ⟨14191433185098360856185367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302750574615431698265287829 14191433185098360856185367)
                ·
                  refine ⟨21287149777647541284278051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14191433185098360856185367 21287149777647541284278051)
                  ·
                    refine ⟨31930724666471311926417077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21287149777647541284278051 31930724666471311926417077)
                    ·
                      refine ⟨2993505437481685493101601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31930724666471311926417077 2993505437481685493101601)
                      ·
                        rfl

theorem cell23_5829831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_5829831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829831 prefixEnd_5829831 := by exact prefixLift 5829831
  have htrace : WordTrace (prefixWord ++ tailWord_5829831) baseStart_5829831 baseEnd_5829831 := by
    simpa [prefixWord, tailWord_5829831, baseEnd_5829831] using wordTrace_append hprefix tailTrace_5829831
  have hstable : (prefixWord ++ tailWord_5829831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829831).length < 2 ^ (prefixWord ++ tailWord_5829831).sum := by decide
  have hdescent : baseEnd_5829831 < baseStart_5829831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829931 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_5829931 : Nat := 118140960795 + 5829931 * 2 ^ 59
def prefixEnd_5829931 : Nat := 4983230072969 + 3 ^ 40 * 5829931 * 2
def baseEnd_5829931 : Nat := 2993556785547135101851141

theorem tailTrace_5829931 : CollatzResearch.WordTrace tailWord_5829931 prefixEnd_5829931 2993556785547135101851141 := by
  unfold tailWord_5829931
  simp only [CollatzResearch.WordTrace]
  refine ⟨212635052242163134790337647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141756701494775423193558431 212635052242163134790337647)
  ·
    refine ⟨318952578363244702185506471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212635052242163134790337647 318952578363244702185506471)
    ·
      refine ⟨478428867544867053278259707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318952578363244702185506471 478428867544867053278259707)
      ·
        refine ⟨717643301317300579917389561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478428867544867053278259707 717643301317300579917389561)
        ·
          refine ⟨538232475987975434938042171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717643301317300579917389561 538232475987975434938042171)
          ·
            refine ⟨807348713981963152407063257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538232475987975434938042171 807348713981963152407063257)
            ·
              refine ⟨605511535486472364305297443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807348713981963152407063257 605511535486472364305297443)
              ·
                refine ⟨908267303229708546457946165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605511535486472364305297443 908267303229708546457946165)
                ·
                  refine ⟨85150059677785176230432453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 908267303229708546457946165 85150059677785176230432453)
                  ·
                    refine ⟨15965636189584720543206085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85150059677785176230432453 15965636189584720543206085)
                    ·
                      refine ⟨2993556785547135101851141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15965636189584720543206085 2993556785547135101851141)
                      ·
                        rfl

theorem cell23_5829931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_5829931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829931 prefixEnd_5829931 := by exact prefixLift 5829931
  have htrace : WordTrace (prefixWord ++ tailWord_5829931) baseStart_5829931 baseEnd_5829931 := by
    simpa [prefixWord, tailWord_5829931, baseEnd_5829931] using wordTrace_append hprefix tailTrace_5829931
  have hstable : (prefixWord ++ tailWord_5829931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829931).length < 2 ^ (prefixWord ++ tailWord_5829931).sum := by decide
  have hdescent : baseEnd_5829931 < baseStart_5829931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829952 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2]
def baseStart_5829952 : Nat := 118140960795 + 5829952 * 2 ^ 59
def prefixEnd_5829952 : Nat := 4983230072969 + 3 ^ 40 * 5829952 * 2
def baseEnd_5829952 : Nat := 2993567568640879519688545

theorem tailTrace_5829952 : CollatzResearch.WordTrace tailWord_5829952 prefixEnd_5829952 2993567568640879519688545 := by
  unfold tailWord_5829952
  simp only [CollatzResearch.WordTrace]
  refine ⟨106317909087543527688426055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141757212116724703584568073 106317909087543527688426055)
  ·
    refine ⟨159476863631315291532639083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106317909087543527688426055 159476863631315291532639083)
    ·
      refine ⟨239215295446972937298958625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159476863631315291532639083 239215295446972937298958625)
      ·
        refine ⟨179411471585229702974218969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239215295446972937298958625 179411471585229702974218969)
        ·
          refine ⟨134558603688922277230664227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179411471585229702974218969 134558603688922277230664227)
          ·
            refine ⟨201837905533383415845996341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134558603688922277230664227 201837905533383415845996341)
            ·
              refine ⟨18922303643754695235562157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201837905533383415845996341 18922303643754695235562157)
              ·
                refine ⟨7095863866408010713335809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18922303643754695235562157 7095863866408010713335809)
                ·
                  refine ⟨5321897899806008035001857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7095863866408010713335809 5321897899806008035001857)
                  ·
                    refine ⟨3991423424854506026251393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321897899806008035001857 3991423424854506026251393)
                    ·
                      refine ⟨2993567568640879519688545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991423424854506026251393 2993567568640879519688545)
                      ·
                        rfl

theorem cell23_5829952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_5829952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829952 prefixEnd_5829952 := by exact prefixLift 5829952
  have htrace : WordTrace (prefixWord ++ tailWord_5829952) baseStart_5829952 baseEnd_5829952 := by
    simpa [prefixWord, tailWord_5829952, baseEnd_5829952] using wordTrace_append hprefix tailTrace_5829952
  have hstable : (prefixWord ++ tailWord_5829952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829952).length < 2 ^ (prefixWord ++ tailWord_5829952).sum := by decide
  have hdescent : baseEnd_5829952 < baseStart_5829952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829956 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5829956 : Nat := 118140960795 + 5829956 * 2 ^ 59
def prefixEnd_5829956 : Nat := 4983230072969 + 3 ^ 40 * 5829956 * 2
def baseEnd_5829956 : Nat := 2993569622563497504038527

theorem tailTrace_5829956 : CollatzResearch.WordTrace tailWord_5829956 prefixEnd_5829956 2993569622563497504038527 := by
  unfold tailWord_5829956
  simp only [CollatzResearch.WordTrace]
  refine ⟨106317982033536282029998861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141757309378048376039998481 106317982033536282029998861)
  ·
    refine ⟨39869243262576105761249573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106317982033536282029998861 39869243262576105761249573)
    ·
      refine ⟨7475483111733019830234295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39869243262576105761249573 7475483111733019830234295)
      ·
        refine ⟨11213224667599529745351443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475483111733019830234295 11213224667599529745351443)
        ·
          refine ⟨16819837001399294618027165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11213224667599529745351443 16819837001399294618027165)
          ·
            refine ⟨6307438875524735481760187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16819837001399294618027165 6307438875524735481760187)
            ·
              refine ⟨9461158313287103222640281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6307438875524735481760187 9461158313287103222640281)
              ·
                refine ⟨7095868734965327416980211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9461158313287103222640281 7095868734965327416980211)
                ·
                  refine ⟨10643803102447991125470317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7095868734965327416980211 10643803102447991125470317)
                  ·
                    refine ⟨3991426163417996672051369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10643803102447991125470317 3991426163417996672051369)
                    ·
                      refine ⟨2993569622563497504038527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991426163417996672051369 2993569622563497504038527)
                      ·
                        rfl

theorem cell23_5829956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5829956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829956 prefixEnd_5829956 := by exact prefixLift 5829956
  have htrace : WordTrace (prefixWord ++ tailWord_5829956) baseStart_5829956 baseEnd_5829956 := by
    simpa [prefixWord, tailWord_5829956, baseEnd_5829956] using wordTrace_append hprefix tailTrace_5829956
  have hstable : (prefixWord ++ tailWord_5829956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829956).length < 2 ^ (prefixWord ++ tailWord_5829956).sum := by decide
  have hdescent : baseEnd_5829956 < baseStart_5829956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5829992 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 5]
def baseStart_5829992 : Nat := 118140960795 + 5829992 * 2 ^ 59
def prefixEnd_5829992 : Nat := 4983230072969 + 3 ^ 40 * 5829992 * 2
def baseEnd_5829992 : Nat := 332620900874117707020929

theorem tailTrace_5829992 : CollatzResearch.WordTrace tailWord_5829992 prefixEnd_5829992 332620900874117707020929 := by
  unfold tailWord_5829992
  simp only [CollatzResearch.WordTrace]
  refine ⟨106318638547471071104154115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141758184729961428138872153 106318638547471071104154115)
  ·
    refine ⟨159477957821206606656231173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106318638547471071104154115 159477957821206606656231173)
    ·
      refine ⟨29902117091476238748043345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159477957821206606656231173 29902117091476238748043345)
      ·
        refine ⟨22426587818607179061032509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29902117091476238748043345 22426587818607179061032509)
        ·
          refine ⟨8409970431977692147887191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22426587818607179061032509 8409970431977692147887191)
          ·
            refine ⟨12614955647966538221830787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8409970431977692147887191 12614955647966538221830787)
            ·
              refine ⟨18922433471949807332746181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12614955647966538221830787 18922433471949807332746181)
              ·
                refine ⟨3547956275990588874889909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18922433471949807332746181 3547956275990588874889909)
                ·
                  refine ⟨332620900874117707020929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3547956275990588874889909 332620900874117707020929)
                  ·
                    rfl

theorem cell23_5829992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 5].length) (baseStart_5829992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5829992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5829992 prefixEnd_5829992 := by exact prefixLift 5829992
  have htrace : WordTrace (prefixWord ++ tailWord_5829992) baseStart_5829992 baseEnd_5829992 := by
    simpa [prefixWord, tailWord_5829992, baseEnd_5829992] using wordTrace_append hprefix tailTrace_5829992
  have hstable : (prefixWord ++ tailWord_5829992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5829992).length < 2 ^ (prefixWord ++ tailWord_5829992).sum := by decide
  have hdescent : baseEnd_5829992 < baseStart_5829992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5829992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830025 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_5830025 : Nat := 118140960795 + 5830025 * 2 ^ 59
def prefixEnd_5830025 : Nat := 4983230072969 + 3 ^ 40 * 5830025 * 2
def baseEnd_5830025 : Nat := 2993605052728657734075709

theorem tailTrace_5830025 : CollatzResearch.WordTrace tailWord_5830025 prefixEnd_5830025 2993605052728657734075709 := by
  unfold tailWord_5830025
  simp only [CollatzResearch.WordTrace]
  refine ⟨212638480703822588844259529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141758987135881725896173019 212638480703822588844259529)
  ·
    refine ⟨159478860527866941633194647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212638480703822588844259529 159478860527866941633194647)
    ·
      refine ⟨239218290791800412449791971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159478860527866941633194647 239218290791800412449791971)
      ·
        refine ⟨358827436187700618674687957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239218290791800412449791971 358827436187700618674687957)
        ·
          refine ⟨8410018035649233250187999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 358827436187700618674687957 8410018035649233250187999)
          ·
            refine ⟨12615027053473849875281999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8410018035649233250187999 12615027053473849875281999)
            ·
              refine ⟨18922540580210774812922999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12615027053473849875281999 18922540580210774812922999)
              ·
                refine ⟨28383810870316162219384499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18922540580210774812922999 28383810870316162219384499)
                ·
                  refine ⟨42575716305474243329076749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28383810870316162219384499 42575716305474243329076749)
                  ·
                    refine ⟨15965893614552841248403781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42575716305474243329076749 15965893614552841248403781)
                    ·
                      refine ⟨2993605052728657734075709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15965893614552841248403781 2993605052728657734075709)
                      ·
                        rfl

theorem cell23_5830025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_5830025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830025 prefixEnd_5830025 := by exact prefixLift 5830025
  have htrace : WordTrace (prefixWord ++ tailWord_5830025) baseStart_5830025 baseEnd_5830025 := by
    simpa [prefixWord, tailWord_5830025, baseEnd_5830025] using wordTrace_append hprefix tailTrace_5830025
  have hstable : (prefixWord ++ tailWord_5830025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830025).length < 2 ^ (prefixWord ++ tailWord_5830025).sum := by decide
  have hdescent : baseEnd_5830025 < baseStart_5830025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830048 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 8]
def baseStart_5830048 : Nat := 118140960795 + 5830048 * 2 ^ 59
def prefixEnd_5830048 : Nat := 4983230072969 + 3 ^ 40 * 5830048 * 2
def baseEnd_5830048 : Nat := 332624095864856793787567

theorem tailTrace_5830048 : CollatzResearch.WordTrace tailWord_5830048 prefixEnd_5830048 332624095864856793787567 := by
  unfold tailWord_5830048
  simp only [CollatzResearch.WordTrace]
  refine ⟨106319659791369631886173399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141759546388492842514897865 106319659791369631886173399)
  ·
    refine ⟨159479489687054447829260099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106319659791369631886173399 159479489687054447829260099)
    ·
      refine ⟨239219234530581671743890149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159479489687054447829260099 239219234530581671743890149)
      ·
        refine ⟨44853606474484063451979403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239219234530581671743890149 44853606474484063451979403)
        ·
          refine ⟨67280409711726095177969105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44853606474484063451979403 67280409711726095177969105)
          ·
            refine ⟨50460307283794571383476829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67280409711726095177969105 50460307283794571383476829)
            ·
              refine ⟨18922615231422964268803811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50460307283794571383476829 18922615231422964268803811)
              ·
                refine ⟨28383922847134446403205717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18922615231422964268803811 28383922847134446403205717)
                ·
                  refine ⟨332624095864856793787567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28383922847134446403205717 332624095864856793787567)
                  ·
                    rfl

theorem cell23_5830048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_5830048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830048 prefixEnd_5830048 := by exact prefixLift 5830048
  have htrace : WordTrace (prefixWord ++ tailWord_5830048) baseStart_5830048 baseEnd_5830048 := by
    simpa [prefixWord, tailWord_5830048, baseEnd_5830048] using wordTrace_append hprefix tailTrace_5830048
  have hstable : (prefixWord ++ tailWord_5830048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830048).length < 2 ^ (prefixWord ++ tailWord_5830048).sum := by decide
  have hdescent : baseEnd_5830048 < baseStart_5830048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830095 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 1, 5]
def baseStart_5830095 : Nat := 118140960795 + 5830095 * 2 ^ 59
def prefixEnd_5830095 : Nat := 4983230072969 + 3 ^ 40 * 5830095 * 2
def baseEnd_5830095 : Nat := 997880332124824153400129

theorem tailTrace_5830095 : CollatzResearch.WordTrace tailWord_5830095 prefixEnd_5830095 997880332124824153400129 := by
  unfold tailWord_5830095
  simp only [CollatzResearch.WordTrace]
  refine ⟨212641033813568990799307739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141760689209045993866205159 212641033813568990799307739)
  ·
    refine ⟨318961550720353486198961609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212641033813568990799307739 318961550720353486198961609)
    ·
      refine ⟨239221163040265114649221207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318961550720353486198961609 239221163040265114649221207)
      ·
        refine ⟨358831744560397671973831811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239221163040265114649221207 358831744560397671973831811)
        ·
          refine ⟨538247616840596507960747717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358831744560397671973831811 538247616840596507960747717)
          ·
            refine ⟨100921428157611845242640197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 538247616840596507960747717 100921428157611845242640197)
            ·
              refine ⟨18922767779552220982995037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100921428157611845242640197 18922767779552220982995037)
              ·
                refine ⟨7096037917332082868623139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18922767779552220982995037 7096037917332082868623139)
                ·
                  refine ⟨10644056875998124302934709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096037917332082868623139 10644056875998124302934709)
                  ·
                    refine ⟨997880332124824153400129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10644056875998124302934709 997880332124824153400129)
                    ·
                      rfl

theorem cell23_5830095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_5830095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830095 prefixEnd_5830095 := by exact prefixLift 5830095
  have htrace : WordTrace (prefixWord ++ tailWord_5830095) baseStart_5830095 baseEnd_5830095 := by
    simpa [prefixWord, tailWord_5830095, baseEnd_5830095] using wordTrace_append hprefix tailTrace_5830095
  have hstable : (prefixWord ++ tailWord_5830095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830095).length < 2 ^ (prefixWord ++ tailWord_5830095).sum := by decide
  have hdescent : baseEnd_5830095 < baseStart_5830095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830109 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5830109 : Nat := 118140960795 + 5830109 * 2 ^ 59
def prefixEnd_5830109 : Nat := 4983230072969 + 3 ^ 40 * 5830109 * 2
def baseEnd_5830109 : Nat := 2993648185103635405425323

theorem tailTrace_5830109 : CollatzResearch.WordTrace tailWord_5830109 prefixEnd_5830109 2993648185103635405425323 := by
  unfold tailWord_5830109
  simp only [CollatzResearch.WordTrace]
  refine ⟨212641544435518271190317381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141761029623678847460211587 212641544435518271190317381)
  ·
    refine ⟨39870289581659675848184509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212641544435518271190317381 39870289581659675848184509)
    ·
      refine ⟨14951358593122378443069191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39870289581659675848184509 14951358593122378443069191)
      ·
        refine ⟨22427037889683567664603787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14951358593122378443069191 22427037889683567664603787)
        ·
          refine ⟨33640556834525351496905681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22427037889683567664603787 33640556834525351496905681)
          ·
            refine ⟨25230417625894013622679261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33640556834525351496905681 25230417625894013622679261)
            ·
              refine ⟨9461406609710255108504723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25230417625894013622679261 9461406609710255108504723)
              ·
                refine ⟨14192109914565382662757085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9461406609710255108504723 14192109914565382662757085)
                ·
                  refine ⟨5322041217962018498533907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14192109914565382662757085 5322041217962018498533907)
                  ·
                    refine ⟨7983061826943027747800861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5322041217962018498533907 7983061826943027747800861)
                    ·
                      refine ⟨2993648185103635405425323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7983061826943027747800861 2993648185103635405425323)
                      ·
                        rfl

theorem cell23_5830109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5830109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830109 prefixEnd_5830109 := by exact prefixLift 5830109
  have htrace : WordTrace (prefixWord ++ tailWord_5830109) baseStart_5830109 baseEnd_5830109 := by
    simpa [prefixWord, tailWord_5830109, baseEnd_5830109] using wordTrace_append hprefix tailTrace_5830109
  have hstable : (prefixWord ++ tailWord_5830109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830109).length < 2 ^ (prefixWord ++ tailWord_5830109).sum := by decide
  have hdescent : baseEnd_5830109 < baseStart_5830109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830138 : List Nat := [3, 1, 1, 1, 1, 2, 3, 11]
def baseStart_5830138 : Nat := 118140960795 + 5830138 * 2 ^ 59
def prefixEnd_5830138 : Nat := 4983230072969 + 3 ^ 40 * 5830138 * 2
def baseEnd_5830138 : Nat := 110876410223800584887507

theorem tailTrace_5830138 : CollatzResearch.WordTrace tailWord_5830138 prefixEnd_5830138 110876410223800584887507 := by
  unfold tailWord_5830138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53160650538103302285780767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141761734768275472762082045 53160650538103302285780767)
  ·
    refine ⟨79740975807154953428671151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53160650538103302285780767 79740975807154953428671151)
    ·
      refine ⟨119611463710732430143006727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79740975807154953428671151 119611463710732430143006727)
      ·
        refine ⟨179417195566098645214510091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119611463710732430143006727 179417195566098645214510091)
        ·
          refine ⟨269125793349147967821765137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179417195566098645214510091 269125793349147967821765137)
          ·
            refine ⟨201844345011860975866323853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269125793349147967821765137 201844345011860975866323853)
            ·
              refine ⟨75691629379447865949871445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201844345011860975866323853 75691629379447865949871445)
              ·
                refine ⟨110876410223800584887507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75691629379447865949871445 110876410223800584887507)
                ·
                  rfl

theorem cell23_5830138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_5830138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830138 prefixEnd_5830138 := by exact prefixLift 5830138
  have htrace : WordTrace (prefixWord ++ tailWord_5830138) baseStart_5830138 baseEnd_5830138 := by
    simpa [prefixWord, tailWord_5830138, baseEnd_5830138] using wordTrace_append hprefix tailTrace_5830138
  have hstable : (prefixWord ++ tailWord_5830138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830138).length < 2 ^ (prefixWord ++ tailWord_5830138).sum := by decide
  have hdescent : baseEnd_5830138 < baseStart_5830138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830146 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_5830146 : Nat := 118140960795 + 5830146 * 2 ^ 59
def prefixEnd_5830146 : Nat := 4983230072969 + 3 ^ 40 * 5830146 * 2
def baseEnd_5830146 : Nat := 997889061295950586887551

theorem tailTrace_5830146 : CollatzResearch.WordTrace tailWord_5830146 prefixEnd_5830146 997889061295950586887551 := by
  unfold tailWord_5830146
  simp only [CollatzResearch.WordTrace]
  refine ⟨53160723484096056627353573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141761929290922817672942861 53160723484096056627353573)
  ·
    refine ⟨9967635653268010617628795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53160723484096056627353573 9967635653268010617628795)
    ·
      refine ⟨14951453479902015926443193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9967635653268010617628795 14951453479902015926443193)
      ·
        refine ⟨11213590109926511944832395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14951453479902015926443193 11213590109926511944832395)
        ·
          refine ⟨16820385164889767917248593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11213590109926511944832395 16820385164889767917248593)
          ·
            refine ⟨12615288873667325937936445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16820385164889767917248593 12615288873667325937936445)
            ·
              refine ⟨4730733327625247226726167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12615288873667325937936445 4730733327625247226726167)
              ·
                refine ⟨7096099991437870840089251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730733327625247226726167 7096099991437870840089251)
                ·
                  refine ⟨10644149987156806260133877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096099991437870840089251 10644149987156806260133877)
                  ·
                    refine ⟨997889061295950586887551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10644149987156806260133877 997889061295950586887551)
                    ·
                      rfl

theorem cell23_5830146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_5830146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830146 prefixEnd_5830146 := by exact prefixLift 5830146
  have htrace : WordTrace (prefixWord ++ tailWord_5830146) baseStart_5830146 baseEnd_5830146 := by
    simpa [prefixWord, tailWord_5830146, baseEnd_5830146] using wordTrace_append hprefix tailTrace_5830146
  have hstable : (prefixWord ++ tailWord_5830146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830146).length < 2 ^ (prefixWord ++ tailWord_5830146).sum := by decide
  have hdescent : baseEnd_5830146 < baseStart_5830146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830152 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_5830152 : Nat := 118140960795 + 5830152 * 2 ^ 59
def prefixEnd_5830152 : Nat := 4983230072969 + 3 ^ 40 * 5830152 * 2
def baseEnd_5830152 : Nat := 2993670264771778737187625

theorem tailTrace_5830152 : CollatzResearch.WordTrace tailWord_5830152 prefixEnd_5830152 2993670264771778737187625 := by
  unfold tailWord_5830152
  simp only [CollatzResearch.WordTrace]
  refine ⟨106321556387181244767066355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141762075182908326356088473 106321556387181244767066355)
  ·
    refine ⟨159482334580771867150599533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106321556387181244767066355 159482334580771867150599533)
    ·
      refine ⟨59805875467789450181474825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159482334580771867150599533 59805875467789450181474825)
      ·
        refine ⟨44854406600842087636106119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59805875467789450181474825 44854406600842087636106119)
        ·
          refine ⟨67281609901263131454159179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44854406600842087636106119 67281609901263131454159179)
          ·
            refine ⟨100922414851894697181238769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67281609901263131454159179 100922414851894697181238769)
            ·
              refine ⟨75691811138921022885929077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100922414851894697181238769 75691811138921022885929077)
              ·
                refine ⟨7096107294273845895555851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75691811138921022885929077 7096107294273845895555851)
                ·
                  refine ⟨10644160941410768843333777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096107294273845895555851 10644160941410768843333777)
                  ·
                    refine ⟨7983120706058076632500333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10644160941410768843333777 7983120706058076632500333)
                    ·
                      refine ⟨2993670264771778737187625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7983120706058076632500333 2993670264771778737187625)
                      ·
                        rfl

theorem cell23_5830152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_5830152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830152 prefixEnd_5830152 := by exact prefixLift 5830152
  have htrace : WordTrace (prefixWord ++ tailWord_5830152) baseStart_5830152 baseEnd_5830152 := by
    simpa [prefixWord, tailWord_5830152, baseEnd_5830152] using wordTrace_append hprefix tailTrace_5830152
  have hstable : (prefixWord ++ tailWord_5830152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830152).length < 2 ^ (prefixWord ++ tailWord_5830152).sum := by decide
  have hdescent : baseEnd_5830152 < baseStart_5830152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830155 : List Nat := [1, 1, 1, 1, 9, 10]
def baseStart_5830155 : Nat := 118140960795 + 5830155 * 2 ^ 59
def prefixEnd_5830155 : Nat := 4983230072969 + 3 ^ 40 * 5830155 * 2
def baseEnd_5830155 : Nat := 12319637058492766359877

theorem tailTrace_5830155 : CollatzResearch.WordTrace tailWord_5830155 prefixEnd_5830155 12319637058492766359877 := by
  unfold tailWord_5830155
  simp only [CollatzResearch.WordTrace]
  refine ⟨212643222193351621046491919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141762148128901080697661279 212643222193351621046491919)
  ·
    refine ⟨318964833290027431569737879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212643222193351621046491919 318964833290027431569737879)
    ·
      refine ⟨478447249935041147354606819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318964833290027431569737879 478447249935041147354606819)
      ·
        refine ⟨717670874902561721031910229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478447249935041147354606819 717670874902561721031910229)
        ·
          refine ⟨4205102782632197584171349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 717670874902561721031910229 4205102782632197584171349)
          ·
            refine ⟨12319637058492766359877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4205102782632197584171349 12319637058492766359877)
            ·
              rfl

theorem cell23_5830155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 10].length) (baseStart_5830155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830155 prefixEnd_5830155 := by exact prefixLift 5830155
  have htrace : WordTrace (prefixWord ++ tailWord_5830155) baseStart_5830155 baseEnd_5830155 := by
    simpa [prefixWord, tailWord_5830155, baseEnd_5830155] using wordTrace_append hprefix tailTrace_5830155
  have hstable : (prefixWord ++ tailWord_5830155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830155).length < 2 ^ (prefixWord ++ tailWord_5830155).sum := by decide
  have hdescent : baseEnd_5830155 < baseStart_5830155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830230 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5830230 : Nat := 118140960795 + 5830230 * 2 ^ 59
def prefixEnd_5830230 : Nat := 4983230072969 + 3 ^ 40 * 5830230 * 2
def baseEnd_5830230 : Nat := 2993710316262829432012267

theorem tailTrace_5830230 : CollatzResearch.WordTrace tailWord_5830230 prefixEnd_5830230 2993710316262829432012267 := by
  unfold tailWord_5830230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290372354254994303467009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141763971778719939236981429 13290372354254994303467009)
  ·
    refine ⟨9967779265691245727600257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13290372354254994303467009 9967779265691245727600257)
    ·
      refine ⟨7475834449268434295700193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9967779265691245727600257 7475834449268434295700193)
      ·
        refine ⟨5606875836951325721775145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7475834449268434295700193 5606875836951325721775145)
        ·
          refine ⟨4205156877713494291331359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606875836951325721775145 4205156877713494291331359)
          ·
            refine ⟨6307735316570241436997039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205156877713494291331359 6307735316570241436997039)
            ·
              refine ⟨9461602974855362155495559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6307735316570241436997039 9461602974855362155495559)
              ·
                refine ⟨14192404462283043233243339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9461602974855362155495559 14192404462283043233243339)
                ·
                  refine ⟨21288606693424564849865009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14192404462283043233243339 21288606693424564849865009)
                  ·
                    refine ⟨15966455020068423637398757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21288606693424564849865009 15966455020068423637398757)
                    ·
                      refine ⟨2993710316262829432012267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15966455020068423637398757 2993710316262829432012267)
                      ·
                        rfl

theorem cell23_5830230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5830230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830230 prefixEnd_5830230 := by exact prefixLift 5830230
  have htrace : WordTrace (prefixWord ++ tailWord_5830230) baseStart_5830230 baseEnd_5830230 := by
    simpa [prefixWord, tailWord_5830230, baseEnd_5830230] using wordTrace_append hprefix tailTrace_5830230
  have hstable : (prefixWord ++ tailWord_5830230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830230).length < 2 ^ (prefixWord ++ tailWord_5830230).sum := by decide
  have hdescent : baseEnd_5830230 < baseStart_5830230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830326 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5830326 : Nat := 118140960795 + 5830326 * 2 ^ 59
def prefixEnd_5830326 : Nat := 4983230072969 + 3 ^ 40 * 5830326 * 2
def baseEnd_5830326 : Nat := 997919870135220352137275

theorem tailTrace_5830326 : CollatzResearch.WordTrace tailWord_5830326 prefixEnd_5830326 997919870135220352137275 := by
  unfold tailWord_5830326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290591192233257328185427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141766306050488078167311221 13290591192233257328185427)
  ·
    refine ⟨19935886788349885992278141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13290591192233257328185427 19935886788349885992278141)
    ·
      refine ⟨7475957545631207247104303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19935886788349885992278141 7475957545631207247104303)
      ·
        refine ⟨11213936318446810870656455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475957545631207247104303 11213936318446810870656455)
        ·
          refine ⟨16820904477670216305984683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11213936318446810870656455 16820904477670216305984683)
          ·
            refine ⟨25231356716505324458977025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16820904477670216305984683 25231356716505324458977025)
            ·
              refine ⟨18923517537378993344232769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25231356716505324458977025 18923517537378993344232769)
              ·
                refine ⟨14192638153034245008174577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18923517537378993344232769 14192638153034245008174577)
                ·
                  refine ⟨10644478614775683756130933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14192638153034245008174577 10644478614775683756130933)
                  ·
                    refine ⟨997919870135220352137275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10644478614775683756130933 997919870135220352137275)
                    ·
                      rfl

theorem cell23_5830326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5830326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830326 prefixEnd_5830326 := by exact prefixLift 5830326
  have htrace : WordTrace (prefixWord ++ tailWord_5830326) baseStart_5830326 baseEnd_5830326 := by
    simpa [prefixWord, tailWord_5830326, baseEnd_5830326] using wordTrace_append hprefix tailTrace_5830326
  have hstable : (prefixWord ++ tailWord_5830326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830326).length < 2 ^ (prefixWord ++ tailWord_5830326).sum := by decide
  have hdescent : baseEnd_5830326 < baseStart_5830326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830346 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_5830346 : Nat := 118140960795 + 5830346 * 2 ^ 59
def prefixEnd_5830346 : Nat := 4983230072969 + 3 ^ 40 * 5830346 * 2
def baseEnd_5830346 : Nat := 2993769880018750978161733

theorem tailTrace_5830346 : CollatzResearch.WordTrace tailWord_5830346 prefixEnd_5830346 2993769880018750978161733 := by
  unfold tailWord_5830346
  simp only [CollatzResearch.WordTrace]
  refine ⟨53162547133914915166673723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141766792357106440444463261 53162547133914915166673723)
  ·
    refine ⟨79743820700872372750010585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53162547133914915166673723 79743820700872372750010585)
    ·
      refine ⟨59807865525654279562507939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79743820700872372750010585 59807865525654279562507939)
      ·
        refine ⟨89711798288481419343761909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59807865525654279562507939 89711798288481419343761909)
        ·
          refine ⟨8410481089545133063477679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89711798288481419343761909 8410481089545133063477679)
          ·
            refine ⟨12615721634317699595216519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8410481089545133063477679 12615721634317699595216519)
            ·
              refine ⟨18923582451476549392824779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12615721634317699595216519 18923582451476549392824779)
              ·
                refine ⟨28385373677214824089237169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18923582451476549392824779 28385373677214824089237169)
                ·
                  refine ⟨21289030257911118066927877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28385373677214824089237169 21289030257911118066927877)
                  ·
                    refine ⟨3991693173358334637548977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21289030257911118066927877 3991693173358334637548977)
                    ·
                      refine ⟨2993769880018750978161733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991693173358334637548977 2993769880018750978161733)
                      ·
                        rfl

theorem cell23_5830346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_5830346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830346 prefixEnd_5830346 := by exact prefixLift 5830346
  have htrace : WordTrace (prefixWord ++ tailWord_5830346) baseStart_5830346 baseEnd_5830346 := by
    simpa [prefixWord, tailWord_5830346, baseEnd_5830346] using wordTrace_append hprefix tailTrace_5830346
  have hstable : (prefixWord ++ tailWord_5830346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830346).length < 2 ^ (prefixWord ++ tailWord_5830346).sum := by decide
  have hdescent : baseEnd_5830346 < baseStart_5830346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830356 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5830356 : Nat := 118140960795 + 5830356 * 2 ^ 59
def prefixEnd_5830356 : Nat := 4983230072969 + 3 ^ 40 * 5830356 * 2
def baseEnd_5830356 : Nat := 997925004941765313012229

theorem tailTrace_5830356 : CollatzResearch.WordTrace tailWord_5830356 prefixEnd_5830356 997925004941765313012229 := by
  unfold tailWord_5830356
  simp only [CollatzResearch.WordTrace]
  refine ⟨106325276632811716187279461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141767035510415621583039281 106325276632811716187279461)
  ·
    refine ⟨19935989368652196785114899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106325276632811716187279461 19935989368652196785114899)
    ·
      refine ⟨29903984052978295177672349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19935989368652196785114899 29903984052978295177672349)
      ·
        refine ⟨11213994019866860691627131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29903984052978295177672349 11213994019866860691627131)
        ·
          refine ⟨16820991029800291037440697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11213994019866860691627131 16820991029800291037440697)
          ·
            refine ⟨12615743272350218278080523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16820991029800291037440697 12615743272350218278080523)
            ·
              refine ⟨18923614908525327417120785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12615743272350218278080523 18923614908525327417120785)
              ·
                refine ⟨14192711181393995562840589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18923614908525327417120785 14192711181393995562840589)
                ·
                  refine ⟨5322266693022748336065221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14192711181393995562840589 5322266693022748336065221)
                  ·
                    refine ⟨997925004941765313012229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322266693022748336065221 997925004941765313012229)
                    ·
                      rfl

theorem cell23_5830356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5830356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830356 prefixEnd_5830356 := by exact prefixLift 5830356
  have htrace : WordTrace (prefixWord ++ tailWord_5830356) baseStart_5830356 baseEnd_5830356 := by
    simpa [prefixWord, tailWord_5830356, baseEnd_5830356] using wordTrace_append hprefix tailTrace_5830356
  have hstable : (prefixWord ++ tailWord_5830356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830356).length < 2 ^ (prefixWord ++ tailWord_5830356).sum := by decide
  have hdescent : baseEnd_5830356 < baseStart_5830356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830396 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_5830396 : Nat := 118140960795 + 5830396 * 2 ^ 59
def prefixEnd_5830396 : Nat := 4983230072969 + 3 ^ 40 * 5830396 * 2
def baseEnd_5830396 : Nat := 2993795554051475782536503

theorem tailTrace_5830396 : CollatzResearch.WordTrace tailWord_5830396 prefixEnd_5830396 2993795554051475782536503 := by
  unfold tailWord_5830396
  simp only [CollatzResearch.WordTrace]
  refine ⟨106326006092739259603007521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141768008123652346137343361 106326006092739259603007521)
  ·
    refine ⟨79744504569554444702255641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106326006092739259603007521 79744504569554444702255641)
    ·
      refine ⟨59808378427165833526691731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79744504569554444702255641 59808378427165833526691731)
      ·
        refine ⟨89712567640748750290037597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59808378427165833526691731 89712567640748750290037597)
        ·
          refine ⟨33642212865280781358764099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89712567640748750290037597 33642212865280781358764099)
          ·
            refine ⟨50463319297921172038146149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33642212865280781358764099 50463319297921172038146149)
            ·
              refine ⟨9461872368360219757152403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50463319297921172038146149 9461872368360219757152403)
              ·
                refine ⟨14192808552540329635728605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9461872368360219757152403 14192808552540329635728605)
                ·
                  refine ⟨5322303207202623613398227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14192808552540329635728605 5322303207202623613398227)
                  ·
                    refine ⟨7983454810803935420097341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5322303207202623613398227 7983454810803935420097341)
                    ·
                      refine ⟨2993795554051475782536503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7983454810803935420097341 2993795554051475782536503)
                      ·
                        rfl

theorem cell23_5830396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_5830396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830396 prefixEnd_5830396 := by exact prefixLift 5830396
  have htrace : WordTrace (prefixWord ++ tailWord_5830396) baseStart_5830396 baseEnd_5830396 := by
    simpa [prefixWord, tailWord_5830396, baseEnd_5830396] using wordTrace_append hprefix tailTrace_5830396
  have hstable : (prefixWord ++ tailWord_5830396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830396).length < 2 ^ (prefixWord ++ tailWord_5830396).sum := by decide
  have hdescent : baseEnd_5830396 < baseStart_5830396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830436 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_5830436 : Nat := 118140960795 + 5830436 * 2 ^ 59
def prefixEnd_5830436 : Nat := 4983230072969 + 3 ^ 40 * 5830436 * 2
def baseEnd_5830436 : Nat := 2993816093277655626036319

theorem tailTrace_5830436 : CollatzResearch.WordTrace tailWord_5830436 prefixEnd_5830436 2993816093277655626036319 := by
  unfold tailWord_5830436
  simp only [CollatzResearch.WordTrace]
  refine ⟨106326735552666803018735581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141768980736889070691647441 106326735552666803018735581)
  ·
    refine ⟨39872525832250051132025843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106326735552666803018735581 39872525832250051132025843)
    ·
      refine ⟨59808788748375076698038765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39872525832250051132025843 59808788748375076698038765)
      ·
        refine ⟨22428295780640653761764537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59808788748375076698038765 22428295780640653761764537)
        ·
          refine ⟨16821221835480490321323403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22428295780640653761764537 16821221835480490321323403)
          ·
            refine ⟨25231832753220735481985105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821221835480490321323403 25231832753220735481985105)
            ·
              refine ⟨18923874564915551611488829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25231832753220735481985105 18923874564915551611488829)
              ·
                refine ⟨7096452961843331854308311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18923874564915551611488829 7096452961843331854308311)
                ·
                  refine ⟨10644679442764997781462467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096452961843331854308311 10644679442764997781462467)
                  ·
                    refine ⟨15967019164147496672193701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10644679442764997781462467 15967019164147496672193701)
                    ·
                      refine ⟨2993816093277655626036319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15967019164147496672193701 2993816093277655626036319)
                      ·
                        rfl

theorem cell23_5830436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_5830436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830436 prefixEnd_5830436 := by exact prefixLift 5830436
  have htrace : WordTrace (prefixWord ++ tailWord_5830436) baseStart_5830436 baseEnd_5830436 := by
    simpa [prefixWord, tailWord_5830436, baseEnd_5830436] using wordTrace_append hprefix tailTrace_5830436
  have hstable : (prefixWord ++ tailWord_5830436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830436).length < 2 ^ (prefixWord ++ tailWord_5830436).sum := by decide
  have hdescent : baseEnd_5830436 < baseStart_5830436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830469 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_5830469 : Nat := 118140960795 + 5830469 * 2 ^ 59
def prefixEnd_5830469 : Nat := 4983230072969 + 3 ^ 40 * 5830469 * 2
def baseEnd_5830469 : Nat := 2993833038139253996923667

theorem tailTrace_5830469 : CollatzResearch.WordTrace tailWord_5830469 prefixEnd_5830469 2993833038139253996923667 := by
  unfold tailWord_5830469
  simp only [CollatzResearch.WordTrace]
  refine ⟨212654674714214052673422461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141769783142809368448948307 212654674714214052673422461)
  ·
    refine ⟨79745503017830269752533423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212654674714214052673422461 79745503017830269752533423)
    ·
      refine ⟨119618254526745404628800135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79745503017830269752533423 119618254526745404628800135)
      ·
        refine ⟨179427381790118106943200203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119618254526745404628800135 179427381790118106943200203)
        ·
          refine ⟨269141072685177160414800305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179427381790118106943200203 269141072685177160414800305)
          ·
            refine ⟨201855804513882870311100229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269141072685177160414800305 201855804513882870311100229)
            ·
              refine ⟨37847963346353038183331293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201855804513882870311100229 37847963346353038183331293)
              ·
                refine ⟨14192986254882389318749235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37847963346353038183331293 14192986254882389318749235)
                ·
                  refine ⟨21289479382323583978123853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14192986254882389318749235 21289479382323583978123853)
                  ·
                    refine ⟨7983554768371343991796445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21289479382323583978123853 7983554768371343991796445)
                    ·
                      refine ⟨2993833038139253996923667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7983554768371343991796445 2993833038139253996923667)
                      ·
                        rfl

theorem cell23_5830469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_5830469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830469 prefixEnd_5830469 := by exact prefixLift 5830469
  have htrace : WordTrace (prefixWord ++ tailWord_5830469) baseStart_5830469 baseEnd_5830469 := by
    simpa [prefixWord, tailWord_5830469, baseEnd_5830469] using wordTrace_append hprefix tailTrace_5830469
  have hstable : (prefixWord ++ tailWord_5830469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830469).length < 2 ^ (prefixWord ++ tailWord_5830469).sum := by decide
  have hdescent : baseEnd_5830469 < baseStart_5830469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830470 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5830470 : Nat := 118140960795 + 5830470 * 2 ^ 59
def prefixEnd_5830470 : Nat := 4983230072969 + 3 ^ 40 * 5830470 * 2
def baseEnd_5830470 : Nat := 2993833551619908493011163

theorem tailTrace_5830470 : CollatzResearch.WordTrace tailWord_5830470 prefixEnd_5830470 2993833551619908493011163 := by
  unfold tailWord_5830470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645459724600325932631527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141769807458140286562805909 6645459724600325932631527)
  ·
    refine ⟨9968189586900488898947291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6645459724600325932631527 9968189586900488898947291)
    ·
      refine ⟨14952284380350733348420937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968189586900488898947291 14952284380350733348420937)
      ·
        refine ⟨11214213285263050011315703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14952284380350733348420937 11214213285263050011315703)
        ·
          refine ⟨16821319927894575016973555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11214213285263050011315703 16821319927894575016973555)
          ·
            refine ⟨25231979891841862525460333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821319927894575016973555 25231979891841862525460333)
            ·
              refine ⟨9461992459440698447047625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25231979891841862525460333 9461992459440698447047625)
              ·
                refine ⟨7096494344580523835285719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9461992459440698447047625 7096494344580523835285719)
                ·
                  refine ⟨10644741516870785752928579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096494344580523835285719 10644741516870785752928579)
                  ·
                    refine ⟨15967112275306178629392869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10644741516870785752928579 15967112275306178629392869)
                    ·
                      refine ⟨2993833551619908493011163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15967112275306178629392869 2993833551619908493011163)
                      ·
                        rfl

theorem cell23_5830470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5830470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830470 prefixEnd_5830470 := by exact prefixLift 5830470
  have htrace : WordTrace (prefixWord ++ tailWord_5830470) baseStart_5830470 baseEnd_5830470 := by
    simpa [prefixWord, tailWord_5830470, baseEnd_5830470] using wordTrace_append hprefix tailTrace_5830470
  have hstable : (prefixWord ++ tailWord_5830470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830470).length < 2 ^ (prefixWord ++ tailWord_5830470).sum := by decide
  have hdescent : baseEnd_5830470 < baseStart_5830470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830503 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_5830503 : Nat := 118140960795 + 5830503 * 2 ^ 59
def prefixEnd_5830503 : Nat := 4983230072969 + 3 ^ 40 * 5830503 * 2
def baseEnd_5830503 : Nat := 2993850496481506863898511

theorem tailTrace_5830503 : CollatzResearch.WordTrace tailWord_5830503 prefixEnd_5830503 2993850496481506863898511 := by
  unfold tailWord_5830503
  simp only [CollatzResearch.WordTrace]
  refine ⟨212655914796090876480160163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141770609864060584320106775 212655914796090876480160163)
  ·
    refine ⟨318983872194136314720240245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212655914796090876480160163 318983872194136314720240245)
    ·
      refine ⟨29904738018200279505022523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 318983872194136314720240245 29904738018200279505022523)
      ·
        refine ⟨44857107027300419257533785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29904738018200279505022523 44857107027300419257533785)
        ·
          refine ⟨33642830270475314443150339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44857107027300419257533785 33642830270475314443150339)
          ·
            refine ⟨50464245405712971664725509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33642830270475314443150339 50464245405712971664725509)
            ·
              refine ⟨9462046013571182187136033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50464245405712971664725509 9462046013571182187136033)
              ·
                refine ⟨7096534510178386640352025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462046013571182187136033 7096534510178386640352025)
                ·
                  refine ⟨5322400882633789980264019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096534510178386640352025 5322400882633789980264019)
                  ·
                    refine ⟨7983601323950684970396029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5322400882633789980264019 7983601323950684970396029)
                    ·
                      refine ⟨2993850496481506863898511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7983601323950684970396029 2993850496481506863898511)
                      ·
                        rfl

theorem cell23_5830503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_5830503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830503 prefixEnd_5830503 := by exact prefixLift 5830503
  have htrace : WordTrace (prefixWord ++ tailWord_5830503) baseStart_5830503 baseEnd_5830503 := by
    simpa [prefixWord, tailWord_5830503, baseEnd_5830503] using wordTrace_append hprefix tailTrace_5830503
  have hstable : (prefixWord ++ tailWord_5830503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830503).length < 2 ^ (prefixWord ++ tailWord_5830503).sum := by decide
  have hdescent : baseEnd_5830503 < baseStart_5830503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830509 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5830509 : Nat := 118140960795 + 5830509 * 2 ^ 59
def prefixEnd_5830509 : Nat := 4983230072969 + 3 ^ 40 * 5830509 * 2
def baseEnd_5830509 : Nat := 2993853577365433840423483

theorem tailTrace_5830509 : CollatzResearch.WordTrace tailWord_5830509 prefixEnd_5830509 2993853577365433840423483 := by
  unfold tailWord_5830509
  simp only [CollatzResearch.WordTrace]
  refine ⟨212656133634069139504878581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141770755756046093003252387 212656133634069139504878581)
  ·
    refine ⟨19936512528193981828582367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212656133634069139504878581 19936512528193981828582367)
    ·
      refine ⟨29904768792290972742873551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19936512528193981828582367 29904768792290972742873551)
      ·
        refine ⟨44857153188436459114310327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29904768792290972742873551 44857153188436459114310327)
        ·
          refine ⟨67285729782654688671465491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44857153188436459114310327 67285729782654688671465491)
          ·
            refine ⟨100928594673982033007198237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67285729782654688671465491 100928594673982033007198237)
            ·
              refine ⟨37848223002743262377699339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100928594673982033007198237 37848223002743262377699339)
              ·
                refine ⟨56772334504114893566549009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37848223002743262377699339 56772334504114893566549009)
                ·
                  refine ⟨42579250878086170174911757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56772334504114893566549009 42579250878086170174911757)
                  ·
                    refine ⟨15967219079282313815591909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42579250878086170174911757 15967219079282313815591909)
                    ·
                      refine ⟨2993853577365433840423483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15967219079282313815591909 2993853577365433840423483)
                      ·
                        rfl

theorem cell23_5830509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5830509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830509 prefixEnd_5830509 := by exact prefixLift 5830509
  have htrace : WordTrace (prefixWord ++ tailWord_5830509) baseStart_5830509 baseEnd_5830509 := by
    simpa [prefixWord, tailWord_5830509, baseEnd_5830509] using wordTrace_append hprefix tailTrace_5830509
  have hstable : (prefixWord ++ tailWord_5830509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830509).length < 2 ^ (prefixWord ++ tailWord_5830509).sum := by decide
  have hdescent : baseEnd_5830509 < baseStart_5830509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830556 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5830556 : Nat := 118140960795 + 5830556 * 2 ^ 59
def prefixEnd_5830556 : Nat := 4983230072969 + 3 ^ 40 * 5830556 * 2
def baseEnd_5830556 : Nat := 2993877710956195156535767

theorem tailTrace_5830556 : CollatzResearch.WordTrace tailWord_5830556 prefixEnd_5830556 2993877710956195156535767 := by
  unfold tailWord_5830556
  simp only [CollatzResearch.WordTrace]
  refine ⟨106328923932449433265919761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141771898576599244354559681 106328923932449433265919761)
  ·
    refine ⟨79746692949337074949439821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106328923932449433265919761 79746692949337074949439821)
    ·
      refine ⟨29905009856001403106039933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79746692949337074949439821 29905009856001403106039933)
      ·
        refine ⟨11214378696000526164764975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29905009856001403106039933 11214378696000526164764975)
        ·
          refine ⟨16821568044000789247147463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11214378696000526164764975 16821568044000789247147463)
          ·
            refine ⟨25232352066001183870721195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821568044000789247147463 25232352066001183870721195)
            ·
              refine ⟨37848528099001775806081793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25232352066001183870721195 37848528099001775806081793)
              ·
                refine ⟨28386396074251331854561345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37848528099001775806081793 28386396074251331854561345)
                ·
                  refine ⟨21289797055688498890921009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28386396074251331854561345 21289797055688498890921009)
                  ·
                    refine ⟨15967347791766374168190757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21289797055688498890921009 15967347791766374168190757)
                    ·
                      refine ⟨2993877710956195156535767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15967347791766374168190757 2993877710956195156535767)
                      ·
                        rfl

theorem cell23_5830556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5830556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830556 prefixEnd_5830556 := by exact prefixLift 5830556
  have htrace : WordTrace (prefixWord ++ tailWord_5830556) baseStart_5830556 baseEnd_5830556 := by
    simpa [prefixWord, tailWord_5830556, baseEnd_5830556] using wordTrace_append hprefix tailTrace_5830556
  have hstable : (prefixWord ++ tailWord_5830556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830556).length < 2 ^ (prefixWord ++ tailWord_5830556).sum := by decide
  have hdescent : baseEnd_5830556 < baseStart_5830556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830577 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_5830577 : Nat := 118140960795 + 5830577 * 2 ^ 59
def prefixEnd_5830577 : Nat := 4983230072969 + 3 ^ 40 * 5830577 * 2
def baseEnd_5830577 : Nat := 2993888494049939574373171

theorem tailTrace_5830577 : CollatzResearch.WordTrace tailWord_5830577 prefixEnd_5830577 2993888494049939574373171 := by
  unfold tailWord_5830577
  simp only [CollatzResearch.WordTrace]
  refine ⟨212658613797822787118353985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141772409198548524745569323 212658613797822787118353985)
  ·
    refine ⟨159493960348367090338765489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212658613797822787118353985 159493960348367090338765489)
    ·
      refine ⟨119620470261275317754074117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159493960348367090338765489 119620470261275317754074117)
      ·
        refine ⟨22428838173989122078888897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119620470261275317754074117 22428838173989122078888897)
        ·
          refine ⟨16821628630491841559166673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22428838173989122078888897 16821628630491841559166673)
          ·
            refine ⟨12616221472868881169375005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16821628630491841559166673 12616221472868881169375005)
            ·
              refine ⟨4731083052325830438515627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12616221472868881169375005 4731083052325830438515627)
              ·
                refine ⟨7096624578488745657773441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731083052325830438515627 7096624578488745657773441)
                ·
                  refine ⟨5322468433866559243330081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096624578488745657773441 5322468433866559243330081)
                  ·
                    refine ⟨3991851325399919432497561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5322468433866559243330081 3991851325399919432497561)
                    ·
                      refine ⟨2993888494049939574373171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991851325399919432497561 2993888494049939574373171)
                      ·
                        rfl

theorem cell23_5830577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_5830577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830577 prefixEnd_5830577 := by exact prefixLift 5830577
  have htrace : WordTrace (prefixWord ++ tailWord_5830577) baseStart_5830577 baseEnd_5830577 := by
    simpa [prefixWord, tailWord_5830577, baseEnd_5830577] using wordTrace_append hprefix tailTrace_5830577
  have hstable : (prefixWord ++ tailWord_5830577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830577).length < 2 ^ (prefixWord ++ tailWord_5830577).sum := by decide
  have hdescent : baseEnd_5830577 < baseStart_5830577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830616 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_5830616 : Nat := 118140960795 + 5830616 * 2 ^ 59
def prefixEnd_5830616 : Nat := 4983230072969 + 3 ^ 40 * 5830616 * 2
def baseEnd_5830616 : Nat := 2993908519795464921785491

theorem tailTrace_5830616 : CollatzResearch.WordTrace tailWord_5830616 prefixEnd_5830616 2993908519795464921785491 := by
  unfold tailWord_5830616
  simp only [CollatzResearch.WordTrace]
  refine ⟨106330018122340748389511851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141773357496454331186015801 106330018122340748389511851)
  ·
    refine ⟨159495027183511122584267777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106330018122340748389511851 159495027183511122584267777)
    ·
      refine ⟨119621270387633341938200833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159495027183511122584267777 119621270387633341938200833)
      ·
        refine ⟨89715952790725006453650625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119621270387633341938200833 89715952790725006453650625)
        ·
          refine ⟨67286964593043754840237969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89715952790725006453650625 67286964593043754840237969)
          ·
            refine ⟨50465223444782816130178477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67286964593043754840237969 50465223444782816130178477)
            ·
              refine ⟨18924458791793556048816929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50465223444782816130178477 18924458791793556048816929)
              ·
                refine ⟨14193344093845167036612697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18924458791793556048816929 14193344093845167036612697)
                ·
                  refine ⟨10645008070383875277459523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14193344093845167036612697 10645008070383875277459523)
                  ·
                    refine ⟨15967512105575812916189285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10645008070383875277459523 15967512105575812916189285)
                    ·
                      refine ⟨2993908519795464921785491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15967512105575812916189285 2993908519795464921785491)
                      ·
                        rfl

theorem cell23_5830616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_5830616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830616 prefixEnd_5830616 := by exact prefixLift 5830616
  have htrace : WordTrace (prefixWord ++ tailWord_5830616) baseStart_5830616 baseEnd_5830616 := by
    simpa [prefixWord, tailWord_5830616, baseEnd_5830616] using wordTrace_append hprefix tailTrace_5830616
  have hstable : (prefixWord ++ tailWord_5830616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830616).length < 2 ^ (prefixWord ++ tailWord_5830616).sum := by decide
  have hdescent : baseEnd_5830616 < baseStart_5830616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830710 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_5830710 : Nat := 118140960795 + 5830710 * 2 ^ 59
def prefixEnd_5830710 : Nat := 4983230072969 + 3 ^ 40 * 5830710 * 2
def baseEnd_5830710 : Nat := 2993956786976987554010059

theorem tailTrace_5830710 : CollatzResearch.WordTrace tailWord_5830710 prefixEnd_5830710 2993956786976987554010059 := by
  unfold tailWord_5830710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291466544146309427059099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141775643137560633888630389 13291466544146309427059099)
  ·
    refine ⟨19937199816219464140588649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13291466544146309427059099 19937199816219464140588649)
    ·
      refine ⟨14952899862164598105441487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19937199816219464140588649 14952899862164598105441487)
      ·
        refine ⟨22429349793246897158162231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14952899862164598105441487 22429349793246897158162231)
        ·
          refine ⟨33644024689870345737243347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429349793246897158162231 33644024689870345737243347)
          ·
            refine ⟨50466037034805518605865021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33644024689870345737243347 50466037034805518605865021)
            ·
              refine ⟨18924763888052069477199383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50466037034805518605865021 18924763888052069477199383)
              ·
                refine ⟨28387145832078104215799075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18924763888052069477199383 28387145832078104215799075)
                ·
                  refine ⟨42580718748117156323698613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28387145832078104215799075 42580718748117156323698613)
                  ·
                    refine ⟨3991942382635983405346745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42580718748117156323698613 3991942382635983405346745)
                    ·
                      refine ⟨2993956786976987554010059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3991942382635983405346745 2993956786976987554010059)
                      ·
                        rfl

theorem cell23_5830710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_5830710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830710 prefixEnd_5830710 := by exact prefixLift 5830710
  have htrace : WordTrace (prefixWord ++ tailWord_5830710) baseStart_5830710 baseEnd_5830710 := by
    simpa [prefixWord, tailWord_5830710, baseEnd_5830710] using wordTrace_append hprefix tailTrace_5830710
  have hstable : (prefixWord ++ tailWord_5830710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830710).length < 2 ^ (prefixWord ++ tailWord_5830710).sum := by decide
  have hdescent : baseEnd_5830710 < baseStart_5830710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830716 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_5830716 : Nat := 118140960795 + 5830716 * 2 ^ 59
def prefixEnd_5830716 : Nat := 4983230072969 + 3 ^ 40 * 5830716 * 2
def baseEnd_5830716 : Nat := 997986622620304843511677

theorem tailTrace_5830716 : CollatzResearch.WordTrace tailWord_5830716 prefixEnd_5830716 997986622620304843511677 := by
  unfold tailWord_5830716
  simp only [CollatzResearch.WordTrace]
  refine ⟨106331841772159606928832001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141775789029546142571776001 106331841772159606928832001)
  ·
    refine ⟨79748881329119705196624001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106331841772159606928832001 79748881329119705196624001)
    ·
      refine ⟨59811660996839778897468001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79748881329119705196624001 59811660996839778897468001)
      ·
        refine ⟨44858745747629834173101001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59811660996839778897468001 44858745747629834173101001)
        ·
          refine ⟨33644059310722375629825751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44858745747629834173101001 33644059310722375629825751)
          ·
            refine ⟨50466088966083563444738627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33644059310722375629825751 50466088966083563444738627)
            ·
              refine ⟨75699133449125345167107941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50466088966083563444738627 75699133449125345167107941)
              ·
                refine ⟨14193587521711002218832739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75699133449125345167107941 14193587521711002218832739)
                ·
                  refine ⟨21290381282566503328249109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14193587521711002218832739 21290381282566503328249109)
                  ·
                    refine ⟨997986622620304843511677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21290381282566503328249109 997986622620304843511677)
                    ·
                      rfl

theorem cell23_5830716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_5830716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830716 prefixEnd_5830716 := by exact prefixLift 5830716
  have htrace : WordTrace (prefixWord ++ tailWord_5830716) baseStart_5830716 baseEnd_5830716 := by
    simpa [prefixWord, tailWord_5830716, baseEnd_5830716] using wordTrace_append hprefix tailTrace_5830716
  have hstable : (prefixWord ++ tailWord_5830716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830716).length < 2 ^ (prefixWord ++ tailWord_5830716).sum := by decide
  have hdescent : baseEnd_5830716 < baseStart_5830716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830717 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5830717 : Nat := 118140960795 + 5830717 * 2 ^ 59
def prefixEnd_5830717 : Nat := 4983230072969 + 3 ^ 40 * 5830717 * 2
def baseEnd_5830717 : Nat := 2993960381341569026622527

theorem tailTrace_5830717 : CollatzResearch.WordTrace tailWord_5830717 prefixEnd_5830717 2993960381341569026622527 := by
  unfold tailWord_5830717
  simp only [CollatzResearch.WordTrace]
  refine ⟨212663720017315591028450405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141775813344877060685633603 212663720017315591028450405)
  ·
    refine ⟨39874447503246673317834451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212663720017315591028450405 39874447503246673317834451)
    ·
      refine ⟨59811671254870009976751677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39874447503246673317834451 59811671254870009976751677)
      ·
        refine ⟨22429376720576253741281879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59811671254870009976751677 22429376720576253741281879)
        ·
          refine ⟨33644065080864380611922819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429376720576253741281879 33644065080864380611922819)
          ·
            refine ⟨50466097621296570917884229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33644065080864380611922819 50466097621296570917884229)
            ·
              refine ⟨9462393303993107047103293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50466097621296570917884229 9462393303993107047103293)
              ·
                refine ⟨3548397488997415142663735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9462393303993107047103293 3548397488997415142663735)
                ·
                  refine ⟨5322596233496122713995603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548397488997415142663735 5322596233496122713995603)
                  ·
                    refine ⟨7983894350244184070993405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5322596233496122713995603 7983894350244184070993405)
                    ·
                      refine ⟨2993960381341569026622527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7983894350244184070993405 2993960381341569026622527)
                      ·
                        rfl

theorem cell23_5830717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5830717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830717 prefixEnd_5830717 := by exact prefixLift 5830717
  have htrace : WordTrace (prefixWord ++ tailWord_5830717) baseStart_5830717 baseEnd_5830717 := by
    simpa [prefixWord, tailWord_5830717, baseEnd_5830717] using wordTrace_append hprefix tailTrace_5830717
  have hstable : (prefixWord ++ tailWord_5830717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830717).length < 2 ^ (prefixWord ++ tailWord_5830717).sum := by decide
  have hdescent : baseEnd_5830717 < baseStart_5830717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830720 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 1, 5]
def baseStart_5830720 : Nat := 118140960795 + 5830720 * 2 ^ 59
def prefixEnd_5830720 : Nat := 4983230072969 + 3 ^ 40 * 5830720 * 2
def baseEnd_5830720 : Nat := 997987307261177504961671

theorem tailTrace_5830720 : CollatzResearch.WordTrace tailWord_5830720 prefixEnd_5830720 997987307261177504961671 := by
  unfold tailWord_5830720
  simp only [CollatzResearch.WordTrace]
  refine ⟨106331914718152361270404807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141775886290869815027206409 106331914718152361270404807)
  ·
    refine ⟨159497872077228541905607211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106331914718152361270404807 159497872077228541905607211)
    ·
      refine ⟨239246808115842812858410817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159497872077228541905607211 239246808115842812858410817)
      ·
        refine ⟨179435106086882109643808113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239246808115842812858410817 179435106086882109643808113)
        ·
          refine ⟨134576329565161582232856085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179435106086882109643808113 134576329565161582232856085)
          ·
            refine ⟨6308265448366949167165129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134576329565161582232856085 6308265448366949167165129)
            ·
              refine ⟨4731199086275211875373847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6308265448366949167165129 4731199086275211875373847)
              ·
                refine ⟨7096798629412817813060771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731199086275211875373847 7096798629412817813060771)
                ·
                  refine ⟨10645197944119226719591157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096798629412817813060771 10645197944119226719591157)
                  ·
                    refine ⟨997987307261177504961671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10645197944119226719591157 997987307261177504961671)
                    ·
                      rfl

theorem cell23_5830720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_5830720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830720 prefixEnd_5830720 := by exact prefixLift 5830720
  have htrace : WordTrace (prefixWord ++ tailWord_5830720) baseStart_5830720 baseEnd_5830720 := by
    simpa [prefixWord, tailWord_5830720, baseEnd_5830720] using wordTrace_append hprefix tailTrace_5830720
  have hstable : (prefixWord ++ tailWord_5830720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830720).length < 2 ^ (prefixWord ++ tailWord_5830720).sum := by decide
  have hdescent : baseEnd_5830720 < baseStart_5830720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830729 : List Nat := [1, 2, 1, 1, 2, 2, 14]
def baseStart_5830729 : Nat := 118140960795 + 5830729 * 2 ^ 59
def prefixEnd_5830729 : Nat := 4983230072969 + 3 ^ 40 * 5830729 * 2
def baseEnd_5830729 : Nat := 36962549914931147897191

theorem tailTrace_5830729 : CollatzResearch.WordTrace tailWord_5830729 prefixEnd_5830729 36962549914931147897191 := by
  unfold tailWord_5830729
  simp only [CollatzResearch.WordTrace]
  refine ⟨212664157693272117077887241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141776105128848078051924827 212664157693272117077887241)
  ·
    refine ⟨159498118269954087808415431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212664157693272117077887241 159498118269954087808415431)
    ·
      refine ⟨239247177404931131712623147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159498118269954087808415431 239247177404931131712623147)
      ·
        refine ⟨358870766107396697568934721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239247177404931131712623147 358870766107396697568934721)
        ·
          refine ⟨269153074580547523176701041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358870766107396697568934721 269153074580547523176701041)
          ·
            refine ⟨201864805935410642382525781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269153074580547523176701041 201864805935410642382525781)
            ·
              refine ⟨36962549914931147897191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 201864805935410642382525781 36962549914931147897191)
              ·
                rfl

theorem cell23_5830729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 14].length) (baseStart_5830729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830729 prefixEnd_5830729 := by exact prefixLift 5830729
  have htrace : WordTrace (prefixWord ++ tailWord_5830729) baseStart_5830729 baseEnd_5830729 := by
    simpa [prefixWord, tailWord_5830729, baseEnd_5830729] using wordTrace_append hprefix tailTrace_5830729
  have hstable : (prefixWord ++ tailWord_5830729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830729).length < 2 ^ (prefixWord ++ tailWord_5830729).sum := by decide
  have hdescent : baseEnd_5830729 < baseStart_5830729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830807 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_5830807 : Nat := 118140960795 + 5830807 * 2 ^ 59
def prefixEnd_5830807 : Nat := 4983230072969 + 3 ^ 40 * 5830807 * 2
def baseEnd_5830807 : Nat := 2994006594600473674497113

theorem tailTrace_5830807 : CollatzResearch.WordTrace tailWord_5830807 prefixEnd_5830807 2994006594600473674497113 := by
  unfold tailWord_5830807
  simp only [CollatzResearch.WordTrace]
  refine ⟨212667002586989536399226675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141778001724659690932817783 212667002586989536399226675)
  ·
    refine ⟨319000503880484304598840013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212667002586989536399226675 319000503880484304598840013)
    ·
      refine ⟨119625188955181614224565005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319000503880484304598840013 119625188955181614224565005)
      ·
        refine ⟨44859445858193105334211877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119625188955181614224565005 44859445858193105334211877)
        ·
          refine ⟨8411146098411207250164727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44859445858193105334211877 8411146098411207250164727)
          ·
            refine ⟨12616719147616810875247091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411146098411207250164727 12616719147616810875247091)
            ·
              refine ⟨18925078721425216312870637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12616719147616810875247091 18925078721425216312870637)
              ·
                refine ⟨7096904520534456117326489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18925078721425216312870637 7096904520534456117326489)
                ·
                  refine ⟨5322678390400842087994867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096904520534456117326489 5322678390400842087994867)
                  ·
                    refine ⟨7984017585601263131992301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5322678390400842087994867 7984017585601263131992301)
                    ·
                      refine ⟨2994006594600473674497113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984017585601263131992301 2994006594600473674497113)
                      ·
                        rfl

theorem cell23_5830807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_5830807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830807 prefixEnd_5830807 := by exact prefixLift 5830807
  have htrace : WordTrace (prefixWord ++ tailWord_5830807) baseStart_5830807 baseEnd_5830807 := by
    simpa [prefixWord, tailWord_5830807, baseEnd_5830807] using wordTrace_append hprefix tailTrace_5830807
  have hstable : (prefixWord ++ tailWord_5830807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830807).length < 2 ^ (prefixWord ++ tailWord_5830807).sum := by decide
  have hdescent : baseEnd_5830807 < baseStart_5830807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830817 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5830817 : Nat := 118140960795 + 5830817 * 2 ^ 59
def prefixEnd_5830817 : Nat := 4983230072969 + 3 ^ 40 * 5830817 * 2
def baseEnd_5830817 : Nat := 2994011729407018635372067

theorem tailTrace_5830817 : CollatzResearch.WordTrace tailWord_5830817 prefixEnd_5830817 2994011729407018635372067 := by
  unfold tailWord_5830817
  simp only [CollatzResearch.WordTrace]
  refine ⟨212667367316953308107090705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141778244877968872071393803 212667367316953308107090705)
  ·
    refine ⟨159500525487714981080318029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212667367316953308107090705 159500525487714981080318029)
    ·
      refine ⟨59812697057893117905119261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159500525487714981080318029 59812697057893117905119261)
      ·
        refine ⟨22429761396709919214419723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59812697057893117905119261 22429761396709919214419723)
        ·
          refine ⟨33644642095064878821629585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429761396709919214419723 33644642095064878821629585)
          ·
            refine ⟨25233481571298659116222189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33644642095064878821629585 25233481571298659116222189)
            ·
              refine ⟨9462555589236997168583321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25233481571298659116222189 9462555589236997168583321)
              ·
                refine ⟨7096916691927747876437491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462555589236997168583321 7096916691927747876437491)
                ·
                  refine ⟨10645375037891621814656237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7096916691927747876437491 10645375037891621814656237)
                  ·
                    refine ⟨3992015639209358180496089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10645375037891621814656237 3992015639209358180496089)
                    ·
                      refine ⟨2994011729407018635372067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992015639209358180496089 2994011729407018635372067)
                      ·
                        rfl

theorem cell23_5830817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5830817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830817 prefixEnd_5830817 := by exact prefixLift 5830817
  have htrace : WordTrace (prefixWord ++ tailWord_5830817) baseStart_5830817 baseEnd_5830817 := by
    simpa [prefixWord, tailWord_5830817, baseEnd_5830817] using wordTrace_append hprefix tailTrace_5830817
  have hstable : (prefixWord ++ tailWord_5830817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830817).length < 2 ^ (prefixWord ++ tailWord_5830817).sum := by decide
  have hdescent : baseEnd_5830817 < baseStart_5830817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830856 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_5830856 : Nat := 118140960795 + 5830856 * 2 ^ 59
def prefixEnd_5830856 : Nat := 4983230072969 + 3 ^ 40 * 5830856 * 2
def baseEnd_5830856 : Nat := 2994031755152543982784387

theorem tailTrace_5830856 : CollatzResearch.WordTrace tailWord_5830856 prefixEnd_5830856 2994031755152543982784387 := by
  unfold tailWord_5830856
  simp only [CollatzResearch.WordTrace]
  refine ⟨106334394881906008883880211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141779193175874678511840281 106334394881906008883880211)
  ·
    refine ⟨159501592322859013325820317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106334394881906008883880211 159501592322859013325820317)
    ·
      refine ⟨59813097121072129997182619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159501592322859013325820317 59813097121072129997182619)
      ·
        refine ⟨89719645681608194995773929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59813097121072129997182619 89719645681608194995773929)
        ·
          refine ⟨67289734261206146246830447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89719645681608194995773929 67289734261206146246830447)
          ·
            refine ⟨100934601391809219370245671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67289734261206146246830447 100934601391809219370245671)
            ·
              refine ⟨151401902087713829055368507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100934601391809219370245671 151401902087713829055368507)
              ·
                refine ⟨227102853131570743583052761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151401902087713829055368507 227102853131570743583052761)
                ·
                  refine ⟨170327139848678057687289571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227102853131570743583052761 170327139848678057687289571)
                  ·
                    refine ⟨255490709773017086530934357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170327139848678057687289571 255490709773017086530934357)
                    ·
                      refine ⟨2994031755152543982784387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255490709773017086530934357 2994031755152543982784387)
                      ·
                        rfl

theorem cell23_5830856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_5830856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830856 prefixEnd_5830856 := by exact prefixLift 5830856
  have htrace : WordTrace (prefixWord ++ tailWord_5830856) baseStart_5830856 baseEnd_5830856 := by
    simpa [prefixWord, tailWord_5830856, baseEnd_5830856] using wordTrace_append hprefix tailTrace_5830856
  have hstable : (prefixWord ++ tailWord_5830856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830856).length < 2 ^ (prefixWord ++ tailWord_5830856).sum := by decide
  have hdescent : baseEnd_5830856 < baseStart_5830856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830863 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_5830863 : Nat := 118140960795 + 5830863 * 2 ^ 59
def prefixEnd_5830863 : Nat := 4983230072969 + 3 ^ 40 * 5830863 * 2
def baseEnd_5830863 : Nat := 2994035349517125455396855

theorem tailTrace_5830863 : CollatzResearch.WordTrace tailWord_5830863 prefixEnd_5830863 2994035349517125455396855 := by
  unfold tailWord_5830863
  simp only [CollatzResearch.WordTrace]
  refine ⟨212669045074786657963265243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141779363383191105308843495 212669045074786657963265243)
  ·
    refine ⟨319003567612179986944897865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212669045074786657963265243 319003567612179986944897865)
    ·
      refine ⟨239252675709134990208673399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319003567612179986944897865 239252675709134990208673399)
      ·
        refine ⟨358879013563702485313010099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239252675709134990208673399 358879013563702485313010099)
        ·
          refine ⟨538318520345553727969515149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358879013563702485313010099 538318520345553727969515149)
          ·
            refine ⟨201869445129582647988568181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538318520345553727969515149 201869445129582647988568181)
            ·
              refine ⟨18925260480898373248928267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201869445129582647988568181 18925260480898373248928267)
              ·
                refine ⟨28387890721347559873392401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18925260480898373248928267 28387890721347559873392401)
                ·
                  refine ⟨21290918041010669905044301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28387890721347559873392401 21290918041010669905044301)
                  ·
                    refine ⟨7984094265379001214391613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21290918041010669905044301 7984094265379001214391613)
                    ·
                      refine ⟨2994035349517125455396855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984094265379001214391613 2994035349517125455396855)
                      ·
                        rfl

theorem cell23_5830863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_5830863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830863 prefixEnd_5830863 := by exact prefixLift 5830863
  have htrace : WordTrace (prefixWord ++ tailWord_5830863) baseStart_5830863 baseEnd_5830863 := by
    simpa [prefixWord, tailWord_5830863, baseEnd_5830863] using wordTrace_append hprefix tailTrace_5830863
  have hstable : (prefixWord ++ tailWord_5830863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830863).length < 2 ^ (prefixWord ++ tailWord_5830863).sum := by decide
  have hdescent : baseEnd_5830863 < baseStart_5830863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830870 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_5830870 : Nat := 118140960795 + 5830870 * 2 ^ 59
def prefixEnd_5830870 : Nat := 4983230072969 + 3 ^ 40 * 5830870 * 2
def baseEnd_5830870 : Nat := 332670993764634103112147

theorem tailTrace_5830870 : CollatzResearch.WordTrace tailWord_5830870 prefixEnd_5830870 332670993764634103112147 := by
  unfold tailWord_5830870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291831274110081134923129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141779533590507532105846709 13291831274110081134923129)
  ·
    refine ⟨9968873455582560851192347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13291831274110081134923129 9968873455582560851192347)
    ·
      refine ⟨14953310183373841276788521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968873455582560851192347 14953310183373841276788521)
      ·
        refine ⟨11214982637530380957591391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14953310183373841276788521 11214982637530380957591391)
        ·
          refine ⟨16822473956295571436387087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11214982637530380957591391 16822473956295571436387087)
          ·
            refine ⟨25233710934443357154580631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16822473956295571436387087 25233710934443357154580631)
            ·
              refine ⟨37850566401665035731870947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25233710934443357154580631 37850566401665035731870947)
              ·
                refine ⟨56775849602497553597806421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37850566401665035731870947 56775849602497553597806421)
                ·
                  refine ⟨332670993764634103112147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56775849602497553597806421 332670993764634103112147)
                  ·
                    rfl

theorem cell23_5830870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_5830870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830870 prefixEnd_5830870 := by exact prefixLift 5830870
  have htrace : WordTrace (prefixWord ++ tailWord_5830870) baseStart_5830870 baseEnd_5830870 := by
    simpa [prefixWord, tailWord_5830870, baseEnd_5830870] using wordTrace_append hprefix tailTrace_5830870
  have hstable : (prefixWord ++ tailWord_5830870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830870).length < 2 ^ (prefixWord ++ tailWord_5830870).sum := by decide
  have hdescent : baseEnd_5830870 < baseStart_5830870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830887 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 5]
def baseStart_5830887 : Nat := 118140960795 + 5830887 * 2 ^ 59
def prefixEnd_5830887 : Nat := 4983230072969 + 3 ^ 40 * 5830887 * 2
def baseEnd_5830887 : Nat := 332671963672537040166305

theorem tailTrace_5830887 : CollatzResearch.WordTrace tailWord_5830887 prefixEnd_5830887 332671963672537040166305 := by
  unfold tailWord_5830887
  simp only [CollatzResearch.WordTrace]
  refine ⟨212669920426699710062138915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141779946951133140041425943 212669920426699710062138915)
  ·
    refine ⟨319004880640049565093208373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212669920426699710062138915 319004880640049565093208373)
    ·
      refine ⟨29906707560004646727488285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319004880640049565093208373 29906707560004646727488285)
      ·
        refine ⟨11215015335001742522808107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29906707560004646727488285 11215015335001742522808107)
        ·
          refine ⟨16822523002502613784212161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11215015335001742522808107 16822523002502613784212161)
          ·
            refine ⟨12616892251876960338159121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16822523002502613784212161 12616892251876960338159121)
            ·
              refine ⟨9462669188907720253619341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12616892251876960338159121 9462669188907720253619341)
              ·
                refine ⟨3548500945840395095107253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9462669188907720253619341 3548500945840395095107253)
                ·
                  refine ⟨332671963672537040166305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3548500945840395095107253 332671963672537040166305)
                  ·
                    rfl

theorem cell23_5830887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 5].length) (baseStart_5830887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830887 prefixEnd_5830887 := by exact prefixLift 5830887
  have htrace : WordTrace (prefixWord ++ tailWord_5830887) baseStart_5830887 baseEnd_5830887 := by
    simpa [prefixWord, tailWord_5830887, baseEnd_5830887] using wordTrace_append hprefix tailTrace_5830887
  have hstable : (prefixWord ++ tailWord_5830887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830887).length < 2 ^ (prefixWord ++ tailWord_5830887).sum := by decide
  have hdescent : baseEnd_5830887 < baseStart_5830887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830896 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_5830896 : Nat := 118140960795 + 5830896 * 2 ^ 59
def prefixEnd_5830896 : Nat := 4983230072969 + 3 ^ 40 * 5830896 * 2
def baseEnd_5830896 : Nat := 998017431459574608761401

theorem tailTrace_5830896 : CollatzResearch.WordTrace tailWord_5830896 prefixEnd_5830896 998017431459574608761401 := by
  unfold tailWord_5830896
  simp only [CollatzResearch.WordTrace]
  refine ⟨106335124341833552299608271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141780165789111403066144361 106335124341833552299608271)
  ·
    refine ⟨159502686512750328449412407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106335124341833552299608271 159502686512750328449412407)
    ·
      refine ⟨239254029769125492674118611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159502686512750328449412407 239254029769125492674118611)
      ·
        refine ⟨358881044653688239011177917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239254029769125492674118611 358881044653688239011177917)
        ·
          refine ⟨134580391745133089629191719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358881044653688239011177917 134580391745133089629191719)
          ·
            refine ⟨201870587617699634443787579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134580391745133089629191719 201870587617699634443787579)
            ·
              refine ⟨302805881426549451665681369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201870587617699634443787579 302805881426549451665681369)
              ·
                refine ⟨227104411069912088749261027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302805881426549451665681369 227104411069912088749261027)
                ·
                  refine ⟨340656616604868133123891541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227104411069912088749261027 340656616604868133123891541)
                  ·
                    refine ⟨998017431459574608761401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 340656616604868133123891541 998017431459574608761401)
                    ·
                      rfl

theorem cell23_5830896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_5830896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830896 prefixEnd_5830896 := by exact prefixLift 5830896
  have htrace : WordTrace (prefixWord ++ tailWord_5830896) baseStart_5830896 baseEnd_5830896 := by
    simpa [prefixWord, tailWord_5830896, baseEnd_5830896] using wordTrace_append hprefix tailTrace_5830896
  have hstable : (prefixWord ++ tailWord_5830896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830896).length < 2 ^ (prefixWord ++ tailWord_5830896).sum := by decide
  have hdescent : baseEnd_5830896 < baseStart_5830896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830923 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3]
def baseStart_5830923 : Nat := 118140960795 + 5830923 * 2 ^ 59
def prefixEnd_5830923 : Nat := 4983230072969 + 3 ^ 40 * 5830923 * 2
def baseEnd_5830923 : Nat := 2994066158356395220646579

theorem tailTrace_5830923 : CollatzResearch.WordTrace tailWord_5830923 prefixEnd_5830923 2994066158356395220646579 := by
  unfold tailWord_5830923
  simp only [CollatzResearch.WordTrace]
  refine ⟨212671233454569288210449423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141780822303046192140299615 212671233454569288210449423)
  ·
    refine ⟨319006850181853932315674135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212671233454569288210449423 319006850181853932315674135)
    ·
      refine ⟨478510275272780898473511203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319006850181853932315674135 478510275272780898473511203)
      ·
        refine ⟨717765412909171347710266805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478510275272780898473511203 717765412909171347710266805)
        ·
          refine ⟨67290507460234813847837513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 717765412909171347710266805 67290507460234813847837513)
          ·
            refine ⟨50467880595176110385878135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67290507460234813847837513 50467880595176110385878135)
            ·
              refine ⟨75701820892764165578817203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50467880595176110385878135 75701820892764165578817203)
              ·
                refine ⟨113552731339146248368225805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75701820892764165578817203 113552731339146248368225805)
                ·
                  refine ⟨42582274252179843138084677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113552731339146248368225805 42582274252179843138084677)
                  ·
                    refine ⟨7984176422283720588390877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42582274252179843138084677 7984176422283720588390877)
                    ·
                      refine ⟨2994066158356395220646579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984176422283720588390877 2994066158356395220646579)
                      ·
                        rfl

theorem cell23_5830923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3].length) (baseStart_5830923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830923 prefixEnd_5830923 := by exact prefixLift 5830923
  have htrace : WordTrace (prefixWord ++ tailWord_5830923) baseStart_5830923 baseEnd_5830923 := by
    simpa [prefixWord, tailWord_5830923, baseEnd_5830923] using wordTrace_append hprefix tailTrace_5830923
  have hstable : (prefixWord ++ tailWord_5830923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830923).length < 2 ^ (prefixWord ++ tailWord_5830923).sum := by decide
  have hdescent : baseEnd_5830923 < baseStart_5830923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830940 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5830940 : Nat := 118140960795 + 5830940 * 2 ^ 59
def prefixEnd_5830940 : Nat := 4983230072969 + 3 ^ 40 * 5830940 * 2
def baseEnd_5830940 : Nat := 2994074887527521654134001

theorem tailTrace_5830940 : CollatzResearch.WordTrace tailWord_5830940 prefixEnd_5830940 2994074887527521654134001 := by
  unfold tailWord_5830940
  simp only [CollatzResearch.WordTrace]
  refine ⟨106335926747753850056909137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141781235663671800075878849 106335926747753850056909137)
  ·
    refine ⟨79751945060815387542681853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106335926747753850056909137 79751945060815387542681853)
    ·
      refine ⟨29906979397805770328505695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79751945060815387542681853 29906979397805770328505695)
      ·
        refine ⟨44860469096708655492758543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29906979397805770328505695 44860469096708655492758543)
        ·
          refine ⟨67290703645062983239137815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44860469096708655492758543 67290703645062983239137815)
          ·
            refine ⟨100936055467594474858706723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67290703645062983239137815 100936055467594474858706723)
            ·
              refine ⟨151404083201391712288060085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100936055467594474858706723 151404083201391712288060085)
              ·
                refine ⟨14194132800130473027005633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151404083201391712288060085 14194132800130473027005633)
                ·
                  refine ⟨10645599600097854770254225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14194132800130473027005633 10645599600097854770254225)
                  ·
                    refine ⟨7984199700073391077690669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10645599600097854770254225 7984199700073391077690669)
                    ·
                      refine ⟨2994074887527521654134001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984199700073391077690669 2994074887527521654134001)
                      ·
                        rfl

theorem cell23_5830940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5830940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830940 prefixEnd_5830940 := by exact prefixLift 5830940
  have htrace : WordTrace (prefixWord ++ tailWord_5830940) baseStart_5830940 baseEnd_5830940 := by
    simpa [prefixWord, tailWord_5830940, baseEnd_5830940] using wordTrace_append hprefix tailTrace_5830940
  have hstable : (prefixWord ++ tailWord_5830940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830940).length < 2 ^ (prefixWord ++ tailWord_5830940).sum := by decide
  have hdescent : baseEnd_5830940 < baseStart_5830940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830943 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 8]
def baseStart_5830943 : Nat := 118140960795 + 5830943 * 2 ^ 59
def prefixEnd_5830943 : Nat := 4983230072969 + 3 ^ 40 * 5830943 * 2
def baseEnd_5830943 : Nat := 332675158663276126932943

theorem tailTrace_5830943 : CollatzResearch.WordTrace tailWord_5830943 prefixEnd_5830943 332675158663276126932943 := by
  unfold tailWord_5830943
  simp only [CollatzResearch.WordTrace]
  refine ⟨212671962914496831626177483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141781308609664554417451655 212671962914496831626177483)
  ·
    refine ⟨319007944371745247439266225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212671962914496831626177483 319007944371745247439266225)
    ·
      refine ⟨239255958278808935579449669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319007944371745247439266225 239255958278808935579449669)
      ·
        refine ⟨44860492177276675421146813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239255958278808935579449669 44860492177276675421146813)
        ·
          refine ⟨16822684566478753282930055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44860492177276675421146813 16822684566478753282930055)
          ·
            refine ⟨25234026849718129924395083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16822684566478753282930055 25234026849718129924395083)
            ·
              refine ⟨37851040274577194886592625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25234026849718129924395083 37851040274577194886592625)
              ·
                refine ⟨28388280205932896164944469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37851040274577194886592625 28388280205932896164944469)
                ·
                  refine ⟨332675158663276126932943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28388280205932896164944469 332675158663276126932943)
                  ·
                    rfl

theorem cell23_5830943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 8].length) (baseStart_5830943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830943 prefixEnd_5830943 := by exact prefixLift 5830943
  have htrace : WordTrace (prefixWord ++ tailWord_5830943) baseStart_5830943 baseEnd_5830943 := by
    simpa [prefixWord, tailWord_5830943, baseEnd_5830943] using wordTrace_append hprefix tailTrace_5830943
  have hstable : (prefixWord ++ tailWord_5830943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830943).length < 2 ^ (prefixWord ++ tailWord_5830943).sum := by decide
  have hdescent : baseEnd_5830943 < baseStart_5830943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830964 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5830964 : Nat := 118140960795 + 5830964 * 2 ^ 59
def prefixEnd_5830964 : Nat := 4983230072969 + 3 ^ 40 * 5830964 * 2
def baseEnd_5830964 : Nat := 998029070354409853411297

theorem tailTrace_5830964 : CollatzResearch.WordTrace tailWord_5830964 prefixEnd_5830964 998029070354409853411297 := by
  unfold tailWord_5830964
  simp only [CollatzResearch.WordTrace]
  refine ⟨106336364423710376106345973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141781819231613834808461297 106336364423710376106345973)
  ·
    refine ⟨9969034164722847759969935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106336364423710376106345973 9969034164722847759969935)
    ·
      refine ⟨14953551247084271639954903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9969034164722847759969935 14953551247084271639954903)
      ·
        refine ⟨22430326870626407459932355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14953551247084271639954903 22430326870626407459932355)
        ·
          refine ⟨33645490305939611189898533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22430326870626407459932355 33645490305939611189898533)
          ·
            refine ⟨6308529432363677098105975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33645490305939611189898533 6308529432363677098105975)
            ·
              refine ⟨9462794148545515647158963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308529432363677098105975 9462794148545515647158963)
              ·
                refine ⟨14194191222818273470738445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9462794148545515647158963 14194191222818273470738445)
                ·
                  refine ⟨5322821708556852551526917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14194191222818273470738445 5322821708556852551526917)
                  ·
                    refine ⟨998029070354409853411297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322821708556852551526917 998029070354409853411297)
                    ·
                      rfl

theorem cell23_5830964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5830964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830964 prefixEnd_5830964 := by exact prefixLift 5830964
  have htrace : WordTrace (prefixWord ++ tailWord_5830964) baseStart_5830964 baseEnd_5830964 := by
    simpa [prefixWord, tailWord_5830964, baseEnd_5830964] using wordTrace_append hprefix tailTrace_5830964
  have hstable : (prefixWord ++ tailWord_5830964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830964).length < 2 ^ (prefixWord ++ tailWord_5830964).sum := by decide
  have hdescent : baseEnd_5830964 < baseStart_5830964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830977 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 6]
def baseStart_5830977 : Nat := 118140960795 + 5830977 * 2 ^ 59
def prefixEnd_5830977 : Nat := 4983230072969 + 3 ^ 40 * 5830977 * 2
def baseEnd_5830977 : Nat := 332677098479082001041259

theorem tailTrace_5830977 : CollatzResearch.WordTrace tailWord_5830977 prefixEnd_5830977 332677098479082001041259 := by
  unfold tailWord_5830977
  simp only [CollatzResearch.WordTrace]
  refine ⟨212673202996373655432915185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141782135330915770288610123 212673202996373655432915185)
  ·
    refine ⟨159504902247280241574686389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212673202996373655432915185 159504902247280241574686389)
    ·
      refine ⟨14953584585682522647626849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159504902247280241574686389 14953584585682522647626849)
      ·
        refine ⟨11215188439261891985720137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14953584585682522647626849 11215188439261891985720137)
        ·
          refine ⟨8411391329446418989290103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11215188439261891985720137 8411391329446418989290103)
          ·
            refine ⟨12617086994169628483935155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411391329446418989290103 12617086994169628483935155)
            ·
              refine ⟨18925630491254442725902733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617086994169628483935155 18925630491254442725902733)
              ·
                refine ⟨7097111434220416022213525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18925630491254442725902733 7097111434220416022213525)
                ·
                  refine ⟨332677098479082001041259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7097111434220416022213525 332677098479082001041259)
                  ·
                    rfl

theorem cell23_5830977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_5830977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830977 prefixEnd_5830977 := by exact prefixLift 5830977
  have htrace : WordTrace (prefixWord ++ tailWord_5830977) baseStart_5830977 baseEnd_5830977 := by
    simpa [prefixWord, tailWord_5830977, baseEnd_5830977] using wordTrace_append hprefix tailTrace_5830977
  have hstable : (prefixWord ++ tailWord_5830977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830977).length < 2 ^ (prefixWord ++ tailWord_5830977).sum := by decide
  have hdescent : baseEnd_5830977 < baseStart_5830977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5830990 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_5830990 : Nat := 118140960795 + 5830990 * 2 ^ 59
def prefixEnd_5830990 : Nat := 4983230072969 + 3 ^ 40 * 5830990 * 2
def baseEnd_5830990 : Nat := 998033520520082152836257

theorem tailTrace_5830990 : CollatzResearch.WordTrace tailWord_5830990 prefixEnd_5830990 998033520520082152836257 := by
  unfold tailWord_5830990
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584209643165819831642303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141782451430217705768758949 26584209643165819831642303)
  ·
    refine ⟨39876314464748729747463455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26584209643165819831642303 39876314464748729747463455)
    ·
      refine ⟨59814471697123094621195183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39876314464748729747463455 59814471697123094621195183)
      ·
        refine ⟨89721707545684641931792775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59814471697123094621195183 89721707545684641931792775)
        ·
          refine ⟨134582561318526962897689163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89721707545684641931792775 134582561318526962897689163)
          ·
            refine ⟨201873841977790444346533745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134582561318526962897689163 201873841977790444346533745)
            ·
              refine ⟨151405381483342833259900309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201873841977790444346533745 151405381483342833259900309)
              ·
                refine ⟨7097127257031695309057827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151405381483342833259900309 7097127257031695309057827)
                ·
                  refine ⟨10645690885547542963586741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097127257031695309057827 10645690885547542963586741)
                  ·
                    refine ⟨998033520520082152836257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10645690885547542963586741 998033520520082152836257)
                    ·
                      rfl

theorem cell23_5830990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_5830990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5830990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5830990 prefixEnd_5830990 := by exact prefixLift 5830990
  have htrace : WordTrace (prefixWord ++ tailWord_5830990) baseStart_5830990 baseEnd_5830990 := by
    simpa [prefixWord, tailWord_5830990, baseEnd_5830990] using wordTrace_append hprefix tailTrace_5830990
  have hstable : (prefixWord ++ tailWord_5830990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5830990).length < 2 ^ (prefixWord ++ tailWord_5830990).sum := by decide
  have hdescent : baseEnd_5830990 < baseStart_5830990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5830990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831023 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_5831023 : Nat := 118140960795 + 5831023 * 2 ^ 59
def prefixEnd_5831023 : Nat := 4983230072969 + 3 ^ 40 * 5831023 * 2
def baseEnd_5831023 : Nat := 2994117506421844829396119

theorem tailTrace_5831023 : CollatzResearch.WordTrace tailWord_5831023 prefixEnd_5831023 2994117506421844829396119 := by
  unfold tailWord_5831023
  simp only [CollatzResearch.WordTrace]
  refine ⟨212674880754207005289089723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141783253836138003526059815 212674880754207005289089723)
  ·
    refine ⟨319012321131310507933634585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212674880754207005289089723 319012321131310507933634585)
    ·
      refine ⟨239259240848482880950225939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319012321131310507933634585 239259240848482880950225939)
      ·
        refine ⟨358888861272724321425338909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239259240848482880950225939 358888861272724321425338909)
        ·
          refine ⟨134583322977271620534502091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358888861272724321425338909 134583322977271620534502091)
          ·
            refine ⟨201874984465907430801753137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134583322977271620534502091 201874984465907430801753137)
            ·
              refine ⟨151406238349430573101314853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201874984465907430801753137 151406238349430573101314853)
              ·
                refine ⟨28388669690518232456496535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151406238349430573101314853 28388669690518232456496535)
                ·
                  refine ⟨42583004535777348684744803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28388669690518232456496535 42583004535777348684744803)
                  ·
                    refine ⟨63874506803666023027117205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42583004535777348684744803 63874506803666023027117205)
                    ·
                      refine ⟨2994117506421844829396119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63874506803666023027117205 2994117506421844829396119)
                      ·
                        rfl

theorem cell23_5831023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_5831023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831023 prefixEnd_5831023 := by exact prefixLift 5831023
  have htrace : WordTrace (prefixWord ++ tailWord_5831023) baseStart_5831023 baseEnd_5831023 := by
    simpa [prefixWord, tailWord_5831023, baseEnd_5831023] using wordTrace_append hprefix tailTrace_5831023
  have hstable : (prefixWord ++ tailWord_5831023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831023).length < 2 ^ (prefixWord ++ tailWord_5831023).sum := by decide
  have hdescent : baseEnd_5831023 < baseStart_5831023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831037 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_5831037 : Nat := 118140960795 + 5831037 * 2 ^ 59
def prefixEnd_5831037 : Nat := 4983230072969 + 3 ^ 40 * 5831037 * 2
def baseEnd_5831037 : Nat := 998041565050335924873685

theorem tailTrace_5831037 : CollatzResearch.WordTrace tailWord_5831037 prefixEnd_5831037 998041565050335924873685 := by
  unfold tailWord_5831037
  simp only [CollatzResearch.WordTrace]
  refine ⟨212675391376156285680099365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141783594250770857120066243 212675391376156285680099365)
  ·
    refine ⟨39876635883029303565018631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212675391376156285680099365 39876635883029303565018631)
    ·
      refine ⟨59814953824543955347527947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39876635883029303565018631 59814953824543955347527947)
      ·
        refine ⟨89722430736815933021291921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59814953824543955347527947 89722430736815933021291921)
        ·
          refine ⟨67291823052611949765968941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89722430736815933021291921 67291823052611949765968941)
          ·
            refine ⟨25234433644729481162238353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67291823052611949765968941 25234433644729481162238353)
            ·
              refine ⟨18925825233547110871678765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25234433644729481162238353 18925825233547110871678765)
              ·
                refine ⟨7097184462580166576879537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18925825233547110871678765 7097184462580166576879537)
                ·
                  refine ⟨5322888346935124932659653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7097184462580166576879537 5322888346935124932659653)
                  ·
                    refine ⟨998041565050335924873685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322888346935124932659653 998041565050335924873685)
                    ·
                      rfl

theorem cell23_5831037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_5831037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831037 prefixEnd_5831037 := by exact prefixLift 5831037
  have htrace : WordTrace (prefixWord ++ tailWord_5831037) baseStart_5831037 baseEnd_5831037 := by
    simpa [prefixWord, tailWord_5831037, baseEnd_5831037] using wordTrace_append hprefix tailTrace_5831037
  have hstable : (prefixWord ++ tailWord_5831037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831037).length < 2 ^ (prefixWord ++ tailWord_5831037).sum := by decide
  have hdescent : baseEnd_5831037 < baseStart_5831037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831044 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5831044 : Nat := 118140960795 + 5831044 * 2 ^ 59
def prefixEnd_5831044 : Nat := 4983230072969 + 3 ^ 40 * 5831044 * 2
def baseEnd_5831044 : Nat := 2994128289515589247233523

theorem tailTrace_5831044 : CollatzResearch.WordTrace tailWord_5831044 prefixEnd_5831044 2994128289515589247233523 := by
  unfold tailWord_5831044
  simp only [CollatzResearch.WordTrace]
  refine ⟨106337823343565462937802093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141783764458087283917069457 106337823343565462937802093)
  ·
    refine ⟨39876683753837048601675785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106337823343565462937802093 39876683753837048601675785)
    ·
      refine ⟨29907512815377786451256839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39876683753837048601675785 29907512815377786451256839)
      ·
        refine ⟨44861269223066679676885259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29907512815377786451256839 44861269223066679676885259)
        ·
          refine ⟨67291903834600019515327889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44861269223066679676885259 67291903834600019515327889)
          ·
            refine ⟨50468927875950014636495917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67291903834600019515327889 50468927875950014636495917)
            ·
              refine ⟨18925847953481255488685969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50468927875950014636495917 18925847953481255488685969)
              ·
                refine ⟨14194385965110941616514477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18925847953481255488685969 14194385965110941616514477)
                ·
                  refine ⟨5322894736916603106192929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14194385965110941616514477 5322894736916603106192929)
                  ·
                    refine ⟨3992171052687452329644697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5322894736916603106192929 3992171052687452329644697)
                    ·
                      refine ⟨2994128289515589247233523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992171052687452329644697 2994128289515589247233523)
                      ·
                        rfl

theorem cell23_5831044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5831044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831044 prefixEnd_5831044 := by exact prefixLift 5831044
  have htrace : WordTrace (prefixWord ++ tailWord_5831044) baseStart_5831044 baseEnd_5831044 := by
    simpa [prefixWord, tailWord_5831044, baseEnd_5831044] using wordTrace_append hprefix tailTrace_5831044
  have hstable : (prefixWord ++ tailWord_5831044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831044).length < 2 ^ (prefixWord ++ tailWord_5831044).sum := by decide
  have hdescent : baseEnd_5831044 < baseStart_5831044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831047 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_5831047 : Nat := 118140960795 + 5831047 * 2 ^ 59
def prefixEnd_5831047 : Nat := 4983230072969 + 3 ^ 40 * 5831047 * 2
def baseEnd_5831047 : Nat := 2994129829957552735496009

theorem tailTrace_5831047 : CollatzResearch.WordTrace tailWord_5831047 prefixEnd_5831047 2994129829957552735496009 := by
  unfold tailWord_5831047
  simp only [CollatzResearch.WordTrace]
  refine ⟨212675756106120057387963395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141783837404080038258642263 212675756106120057387963395)
  ·
    refine ⟨319013634159180086081945093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212675756106120057387963395 319013634159180086081945093)
    ·
      refine ⟨59815056404846266140364705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319013634159180086081945093 59815056404846266140364705)
      ·
        refine ⟨44861292303634699605273529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59815056404846266140364705 44861292303634699605273529)
        ·
          refine ⟨33645969227726024703955147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44861292303634699605273529 33645969227726024703955147)
          ·
            refine ⟨50468953841589037055932721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33645969227726024703955147 50468953841589037055932721)
            ·
              refine ⟨37851715381191777791949541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50468953841589037055932721 37851715381191777791949541)
              ·
                refine ⟨7097196633973458335990539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37851715381191777791949541 7097196633973458335990539)
                ·
                  refine ⟨10645794950960187503985809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097196633973458335990539 10645794950960187503985809)
                  ·
                    refine ⟨7984346213220140627989357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10645794950960187503985809 7984346213220140627989357)
                    ·
                      refine ⟨2994129829957552735496009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984346213220140627989357 2994129829957552735496009)
                      ·
                        rfl

theorem cell23_5831047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_5831047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831047 prefixEnd_5831047 := by exact prefixLift 5831047
  have htrace : WordTrace (prefixWord ++ tailWord_5831047) baseStart_5831047 baseEnd_5831047 := by
    simpa [prefixWord, tailWord_5831047, baseEnd_5831047] using wordTrace_append hprefix tailTrace_5831047
  have hstable : (prefixWord ++ tailWord_5831047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831047).length < 2 ^ (prefixWord ++ tailWord_5831047).sum := by decide
  have hdescent : baseEnd_5831047 < baseStart_5831047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831064 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5831064 : Nat := 118140960795 + 5831064 * 2 ^ 59
def prefixEnd_5831064 : Nat := 4983230072969 + 3 ^ 40 * 5831064 * 2
def baseEnd_5831064 : Nat := 2994138559128679168983431

theorem tailTrace_5831064 : CollatzResearch.WordTrace tailWord_5831064 prefixEnd_5831064 2994138559128679168983431 := by
  unfold tailWord_5831064
  simp only [CollatzResearch.WordTrace]
  refine ⟨106338188073529234645666123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141784250764705646194221497 106338188073529234645666123)
  ·
    refine ⟨159507282110293851968499185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106338188073529234645666123 159507282110293851968499185)
    ·
      refine ⟨119630461582720388976374389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159507282110293851968499185 119630461582720388976374389)
      ·
        refine ⟨11215355773380036466535099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119630461582720388976374389 11215355773380036466535099)
        ·
          refine ⟨16823033660070054699802649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11215355773380036466535099 16823033660070054699802649)
          ·
            refine ⟨12617275245052541024851987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16823033660070054699802649 12617275245052541024851987)
            ·
              refine ⟨18925912867578811537277981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617275245052541024851987 18925912867578811537277981)
              ·
                refine ⟨7097217325342054326479243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18925912867578811537277981 7097217325342054326479243)
                ·
                  refine ⟨10645825988013081489718865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097217325342054326479243 10645825988013081489718865)
                  ·
                    refine ⟨7984369491009811117289149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10645825988013081489718865 7984369491009811117289149)
                    ·
                      refine ⟨2994138559128679168983431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984369491009811117289149 2994138559128679168983431)
                      ·
                        rfl

theorem cell23_5831064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5831064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831064 prefixEnd_5831064 := by exact prefixLift 5831064
  have htrace : WordTrace (prefixWord ++ tailWord_5831064) baseStart_5831064 baseEnd_5831064 := by
    simpa [prefixWord, tailWord_5831064, baseEnd_5831064] using wordTrace_append hprefix tailTrace_5831064
  have hstable : (prefixWord ++ tailWord_5831064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831064).length < 2 ^ (prefixWord ++ tailWord_5831064).sum := by decide
  have hdescent : baseEnd_5831064 < baseStart_5831064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831077 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_5831077 : Nat := 118140960795 + 5831077 * 2 ^ 59
def prefixEnd_5831077 : Nat := 4983230072969 + 3 ^ 40 * 5831077 * 2
def baseEnd_5831077 : Nat := 2994145234377187618120871

theorem tailTrace_5831077 : CollatzResearch.WordTrace tailWord_5831077 prefixEnd_5831077 2994145234377187618120871 := by
  unfold tailWord_5831077
  simp only [CollatzResearch.WordTrace]
  refine ⟨212676850296011372511555485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141784566864007581674370323 212676850296011372511555485)
  ·
    refine ⟨79753818861004264691833307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212676850296011372511555485 79753818861004264691833307)
    ·
      refine ⟨119630728291506397037749961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79753818861004264691833307 119630728291506397037749961)
      ·
        refine ⟨89723046218629797778312471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119630728291506397037749961 89723046218629797778312471)
        ·
          refine ⟨134584569327944696667468707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89723046218629797778312471 134584569327944696667468707)
          ·
            refine ⟨201876853991917045001203061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134584569327944696667468707 201876853991917045001203061)
            ·
              refine ⟨18925955061742222968862787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201876853991917045001203061 18925955061742222968862787)
              ·
                refine ⟨28388932592613334453294181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18925955061742222968862787 28388932592613334453294181)
                ·
                  refine ⟨5322924861115000209992659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28388932592613334453294181 5322924861115000209992659)
                  ·
                    refine ⟨7984387291672500314988989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5322924861115000209992659 7984387291672500314988989)
                    ·
                      refine ⟨2994145234377187618120871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984387291672500314988989 2994145234377187618120871)
                      ·
                        rfl

theorem cell23_5831077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_5831077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831077 prefixEnd_5831077 := by exact prefixLift 5831077
  have htrace : WordTrace (prefixWord ++ tailWord_5831077) baseStart_5831077 baseEnd_5831077 := by
    simpa [prefixWord, tailWord_5831077, baseEnd_5831077] using wordTrace_append hprefix tailTrace_5831077
  have hstable : (prefixWord ++ tailWord_5831077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831077).length < 2 ^ (prefixWord ++ tailWord_5831077).sum := by decide
  have hdescent : baseEnd_5831077 < baseStart_5831077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831191 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 5]
def baseStart_5831191 : Nat := 118140960795 + 5831191 * 2 ^ 59
def prefixEnd_5831191 : Nat := 4983230072969 + 3 ^ 40 * 5831191 * 2
def baseEnd_5831191 : Nat := 332689307907977796899483

theorem tailTrace_5831191 : CollatzResearch.WordTrace tailWord_5831191 prefixEnd_5831191 332689307907977796899483 := by
  unfold tailWord_5831191
  simp only [CollatzResearch.WordTrace]
  refine ⟨212681008217598369981205427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141787338811732246654136951 212681008217598369981205427)
  ·
    refine ⟨319021512326397554971808141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212681008217598369981205427 319021512326397554971808141)
    ·
      refine ⟨119633067122399083114428053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319021512326397554971808141 119633067122399083114428053)
      ·
        refine ⟨5607800021362457020988815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119633067122399083114428053 5607800021362457020988815)
        ·
          refine ⟨8411700032043685531483223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607800021362457020988815 8411700032043685531483223)
          ·
            refine ⟨12617550048065528297224835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411700032043685531483223 12617550048065528297224835)
            ·
              refine ⟨18926325072098292445837253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617550048065528297224835 18926325072098292445837253)
              ·
                refine ⟨3548685951018429833594485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18926325072098292445837253 3548685951018429833594485)
                ·
                  refine ⟨332689307907977796899483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3548685951018429833594485 332689307907977796899483)
                  ·
                    rfl

theorem cell23_5831191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 5].length) (baseStart_5831191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831191 prefixEnd_5831191 := by exact prefixLift 5831191
  have htrace : WordTrace (prefixWord ++ tailWord_5831191) baseStart_5831191 baseEnd_5831191 := by
    simpa [prefixWord, tailWord_5831191, baseEnd_5831191] using wordTrace_append hprefix tailTrace_5831191
  have hstable : (prefixWord ++ tailWord_5831191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831191).length < 2 ^ (prefixWord ++ tailWord_5831191).sum := by decide
  have hdescent : baseEnd_5831191 < baseStart_5831191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831197 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5831197 : Nat := 118140960795 + 5831197 * 2 ^ 59
def prefixEnd_5831197 : Nat := 4983230072969 + 3 ^ 40 * 5831197 * 2
def baseEnd_5831197 : Nat := 2994206852055727148620319

theorem tailTrace_5831197 : CollatzResearch.WordTrace tailWord_5831197 prefixEnd_5831197 2994206852055727148620319 := by
  unfold tailWord_5831197
  simp only [CollatzResearch.WordTrace]
  refine ⟨212681227055576633005923845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141787484703717755337282563 212681227055576633005923845)
  ·
    refine ⟨39877730072920618688610721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212681227055576633005923845 39877730072920618688610721)
    ·
      refine ⟨29908297554690464016458041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39877730072920618688610721 29908297554690464016458041)
      ·
        refine ⟨22431223166017848012343531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29908297554690464016458041 22431223166017848012343531)
        ·
          refine ⟨33646834749026772018515297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22431223166017848012343531 33646834749026772018515297)
          ·
            refine ⟨25235126061770079013886473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33646834749026772018515297 25235126061770079013886473)
            ·
              refine ⟨18926344546327559260414855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25235126061770079013886473 18926344546327559260414855)
              ·
                refine ⟨28389516819491338890622283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18926344546327559260414855 28389516819491338890622283)
                ·
                  refine ⟨42584275229237008335933425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28389516819491338890622283 42584275229237008335933425)
                  ·
                    refine ⟨31938206421927756251950069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42584275229237008335933425 31938206421927756251950069)
                    ·
                      refine ⟨2994206852055727148620319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31938206421927756251950069 2994206852055727148620319)
                      ·
                        rfl

theorem cell23_5831197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5831197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831197 prefixEnd_5831197 := by exact prefixLift 5831197
  have htrace : WordTrace (prefixWord ++ tailWord_5831197) baseStart_5831197 baseEnd_5831197 := by
    simpa [prefixWord, tailWord_5831197, baseEnd_5831197] using wordTrace_append hprefix tailTrace_5831197
  have hstable : (prefixWord ++ tailWord_5831197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831197).length < 2 ^ (prefixWord ++ tailWord_5831197).sum := by decide
  have hdescent : baseEnd_5831197 < baseStart_5831197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831217 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_5831217 : Nat := 118140960795 + 5831217 * 2 ^ 59
def prefixEnd_5831217 : Nat := 4983230072969 + 3 ^ 40 * 5831217 * 2
def baseEnd_5831217 : Nat := 998072373889605690123409

theorem tailTrace_5831217 : CollatzResearch.WordTrace tailWord_5831217 prefixEnd_5831217 998072373889605690123409 := by
  unfold tailWord_5831217
  simp only [CollatzResearch.WordTrace]
  refine ⟨212681956515504176421651905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141787971010336117614434603 212681956515504176421651905)
  ·
    refine ⟨159511467386628132316238929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212681956515504176421651905 159511467386628132316238929)
    ·
      refine ⟨119633600539971099237179197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159511467386628132316238929 119633600539971099237179197)
      ·
        refine ⟨44862600202489162213942199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119633600539971099237179197 44862600202489162213942199)
        ·
          refine ⟨67293900303733743320913299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44862600202489162213942199 67293900303733743320913299)
          ·
            refine ⟨100940850455600614981369949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67293900303733743320913299 100940850455600614981369949)
            ·
              refine ⟨37852818920850230618013731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100940850455600614981369949 37852818920850230618013731)
              ·
                refine ⟨56779228381275345927020597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37852818920850230618013731 56779228381275345927020597)
                ·
                  refine ⟨5323052660744563680658181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56779228381275345927020597 5323052660744563680658181)
                  ·
                    refine ⟨998072373889605690123409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323052660744563680658181 998072373889605690123409)
                    ·
                      rfl

theorem cell23_5831217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_5831217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831217 prefixEnd_5831217 := by exact prefixLift 5831217
  have htrace : WordTrace (prefixWord ++ tailWord_5831217) baseStart_5831217 baseEnd_5831217 := by
    simpa [prefixWord, tailWord_5831217, baseEnd_5831217] using wordTrace_append hprefix tailTrace_5831217
  have hstable : (prefixWord ++ tailWord_5831217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831217).length < 2 ^ (prefixWord ++ tailWord_5831217).sum := by decide
  have hdescent : baseEnd_5831217 < baseStart_5831217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831247 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 6]
def baseStart_5831247 : Nat := 118140960795 + 5831247 * 2 ^ 59
def prefixEnd_5831247 : Nat := 4983230072969 + 3 ^ 40 * 5831247 * 2
def baseEnd_5831247 : Nat := 332692502898716883666121

theorem tailTrace_5831247 : CollatzResearch.WordTrace tailWord_5831247 prefixEnd_5831247 332692502898716883666121 := by
  unfold tailWord_5831247
  simp only [CollatzResearch.WordTrace]
  refine ⟨212683050705395491545243995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141788700470263661030162663 212683050705395491545243995)
  ·
    refine ⟨319024576058093237317865993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212683050705395491545243995 319024576058093237317865993)
    ·
      refine ⟨239268432043569927988399495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319024576058093237317865993 239268432043569927988399495)
      ·
        refine ⟨358902648065354891982599243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239268432043569927988399495 358902648065354891982599243)
        ·
          refine ⟨538353972098032337973898865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358902648065354891982599243 538353972098032337973898865)
          ·
            refine ⟨403765479073524253480424149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538353972098032337973898865 403765479073524253480424149)
            ·
              refine ⟨9463253415785724690947441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 403765479073524253480424149 9463253415785724690947441)
              ·
                refine ⟨7097440061839293518210581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463253415785724690947441 7097440061839293518210581)
                ·
                  refine ⟨332692502898716883666121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7097440061839293518210581 332692502898716883666121)
                  ·
                    rfl

theorem cell23_5831247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 6].length) (baseStart_5831247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831247 prefixEnd_5831247 := by exact prefixLift 5831247
  have htrace : WordTrace (prefixWord ++ tailWord_5831247) baseStart_5831247 baseEnd_5831247 := by
    simpa [prefixWord, tailWord_5831247, baseEnd_5831247] using wordTrace_append hprefix tailTrace_5831247
  have hstable : (prefixWord ++ tailWord_5831247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831247).length < 2 ^ (prefixWord ++ tailWord_5831247).sum := by decide
  have hdescent : baseEnd_5831247 < baseStart_5831247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831285 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5831285 : Nat := 118140960795 + 5831285 * 2 ^ 59
def prefixEnd_5831285 : Nat := 4983230072969 + 3 ^ 40 * 5831285 * 2
def baseEnd_5831285 : Nat := 998084012784440934773305

theorem tailTrace_5831285 : CollatzResearch.WordTrace tailWord_5831285 prefixEnd_5831285 998084012784440934773305 := by
  unfold tailWord_5831285
  simp only [CollatzResearch.WordTrace]
  refine ⟨212684436679257824035127309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141789624452838549356751539 212684436679257824035127309)
  ·
    refine ⟨79756663754721684013172741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212684436679257824035127309 79756663754721684013172741)
    ·
      refine ⟨14954374454010315752469889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79756663754721684013172741 14954374454010315752469889)
      ·
        refine ⟨11215780840507736814352417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14954374454010315752469889 11215780840507736814352417)
        ·
          refine ⟨8411835630380802610764313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11215780840507736814352417 8411835630380802610764313)
          ·
            refine ⟨6308876722785601958073235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8411835630380802610764313 6308876722785601958073235)
            ·
              refine ⟨9463315084178402937109853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308876722785601958073235 9463315084178402937109853)
              ·
                refine ⟨3548743156566901101416195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9463315084178402937109853 3548743156566901101416195)
                ·
                  refine ⟨5323114734850351652124293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548743156566901101416195 5323114734850351652124293)
                  ·
                    refine ⟨998084012784440934773305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323114734850351652124293 998084012784440934773305)
                    ·
                      rfl

theorem cell23_5831285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5831285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831285 prefixEnd_5831285 := by exact prefixLift 5831285
  have htrace : WordTrace (prefixWord ++ tailWord_5831285) baseStart_5831285 baseEnd_5831285 := by
    simpa [prefixWord, tailWord_5831285, baseEnd_5831285] using wordTrace_append hprefix tailTrace_5831285
  have hstable : (prefixWord ++ tailWord_5831285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831285).length < 2 ^ (prefixWord ++ tailWord_5831285).sum := by decide
  have hdescent : baseEnd_5831285 < baseStart_5831285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 1, 1, 3]
def baseStart_5831291 : Nat := 118140960795 + 5831291 * 2 ^ 59
def prefixEnd_5831291 : Nat := 4983230072969 + 3 ^ 40 * 5831291 * 2
def baseEnd_5831291 : Nat := 2994255119237249780844887

theorem tailTrace_5831291 : CollatzResearch.WordTrace tailWord_5831291 prefixEnd_5831291 2994255119237249780844887 := by
  unfold tailWord_5831291
  simp only [CollatzResearch.WordTrace]
  refine ⟨212684655517236087059845727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141789770344824058039897151 212684655517236087059845727)
  ·
    refine ⟨319026983275854130589768591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212684655517236087059845727 319026983275854130589768591)
    ·
      refine ⟨478540474913781195884652887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319026983275854130589768591 478540474913781195884652887)
      ·
        refine ⟨717810712370671793826979331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478540474913781195884652887 717810712370671793826979331)
        ·
          refine ⟨1076716068556007690740468997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717810712370671793826979331 1076716068556007690740468997)
          ·
            refine ⟨201884262854251442013837937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1076716068556007690740468997 201884262854251442013837937)
            ·
              refine ⟨151413197140688581510378453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201884262854251442013837937 151413197140688581510378453)
              ·
                refine ⟨3548746807984888629149495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151413197140688581510378453 3548746807984888629149495)
                ·
                  refine ⟨5323120211977332943724243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548746807984888629149495 5323120211977332943724243)
                  ·
                    refine ⟨7984680317965999415586365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5323120211977332943724243 7984680317965999415586365)
                    ·
                      refine ⟨2994255119237249780844887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984680317965999415586365 2994255119237249780844887)
                      ·
                        rfl

theorem cell23_5831291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 1, 3].length) (baseStart_5831291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831291 prefixEnd_5831291 := by exact prefixLift 5831291
  have htrace : WordTrace (prefixWord ++ tailWord_5831291) baseStart_5831291 baseEnd_5831291 := by
    simpa [prefixWord, tailWord_5831291, baseEnd_5831291] using wordTrace_append hprefix tailTrace_5831291
  have hstable : (prefixWord ++ tailWord_5831291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831291).length < 2 ^ (prefixWord ++ tailWord_5831291).sum := by decide
  have hdescent : baseEnd_5831291 < baseStart_5831291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831301 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_5831301 : Nat := 118140960795 + 5831301 * 2 ^ 59
def prefixEnd_5831301 : Nat := 4983230072969 + 3 ^ 40 * 5831301 * 2
def baseEnd_5831301 : Nat := 2994260254043794741719841

theorem tailTrace_5831301 : CollatzResearch.WordTrace tailWord_5831301 prefixEnd_5831301 2994260254043794741719841 := by
  unfold tailWord_5831301
  simp only [CollatzResearch.WordTrace]
  refine ⟨212685020247199858767709757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141790013498133239178473171 212685020247199858767709757)
  ·
    refine ⟨79756882592699947037891159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212685020247199858767709757 79756882592699947037891159)
    ·
      refine ⟨119635323889049920556836739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79756882592699947037891159 119635323889049920556836739)
      ·
        refine ⟨179452985833574880835255109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119635323889049920556836739 179452985833574880835255109)
        ·
          refine ⟨33647434843795290156610333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179452985833574880835255109 33647434843795290156610333)
          ·
            refine ⟨12617788066423233808728875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33647434843795290156610333 12617788066423233808728875)
            ·
              refine ⟨18926682099634850713093313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617788066423233808728875 18926682099634850713093313)
              ·
                refine ⟨14195011574726138034819985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18926682099634850713093313 14195011574726138034819985)
                ·
                  refine ⟨10646258681044603526114989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14195011574726138034819985 10646258681044603526114989)
                  ·
                    refine ⟨3992347005391726322293121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10646258681044603526114989 3992347005391726322293121)
                    ·
                      refine ⟨2994260254043794741719841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992347005391726322293121 2994260254043794741719841)
                      ·
                        rfl

theorem cell23_5831301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_5831301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831301 prefixEnd_5831301 := by exact prefixLift 5831301
  have htrace : WordTrace (prefixWord ++ tailWord_5831301) baseStart_5831301 baseEnd_5831301 := by
    simpa [prefixWord, tailWord_5831301, baseEnd_5831301] using wordTrace_append hprefix tailTrace_5831301
  have hstable : (prefixWord ++ tailWord_5831301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831301).length < 2 ^ (prefixWord ++ tailWord_5831301).sum := by decide
  have hdescent : baseEnd_5831301 < baseStart_5831301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831317 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_5831317 : Nat := 118140960795 + 5831317 * 2 ^ 59
def prefixEnd_5831317 : Nat := 4983230072969 + 3 ^ 40 * 5831317 * 2
def baseEnd_5831317 : Nat := 2994268469734266679119767

theorem tailTrace_5831317 : CollatzResearch.WordTrace tailWord_5831317 prefixEnd_5831317 2994268469734266679119767 := by
  unfold tailWord_5831317
  simp only [CollatzResearch.WordTrace]
  refine ⟨212685603815141893500292205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141790402543427929000194803 212685603815141893500292205)
  ·
    refine ⟨79757101430678210062609577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212685603815141893500292205 79757101430678210062609577)
    ·
      refine ⟨59817826073008657546957183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79757101430678210062609577 59817826073008657546957183)
      ·
        refine ⟨89726739109512986320435775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59817826073008657546957183 89726739109512986320435775)
        ·
          refine ⟨134590108664269479480653663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89726739109512986320435775 134590108664269479480653663)
          ·
            refine ⟨201885162996404219220980495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134590108664269479480653663 201885162996404219220980495)
            ·
              refine ⟨302827744494606328831470743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201885162996404219220980495 302827744494606328831470743)
              ·
                refine ⟨454241616741909493247206115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302827744494606328831470743 454241616741909493247206115)
                ·
                  refine ⟨681362425112864239870809173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454241616741909493247206115 681362425112864239870809173)
                  ·
                    refine ⟨7984715919291377810986045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 681362425112864239870809173 7984715919291377810986045)
                    ·
                      refine ⟨2994268469734266679119767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7984715919291377810986045 2994268469734266679119767)
                      ·
                        rfl

theorem cell23_5831317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_5831317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831317 prefixEnd_5831317 := by exact prefixLift 5831317
  have htrace : WordTrace (prefixWord ++ tailWord_5831317) baseStart_5831317 baseEnd_5831317 := by
    simpa [prefixWord, tailWord_5831317, baseEnd_5831317] using wordTrace_append hprefix tailTrace_5831317
  have hstable : (prefixWord ++ tailWord_5831317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831317).length < 2 ^ (prefixWord ++ tailWord_5831317).sum := by decide
  have hdescent : baseEnd_5831317 < baseStart_5831317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831328 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 1, 5]
def baseStart_5831328 : Nat := 118140960795 + 5831328 * 2 ^ 59
def prefixEnd_5831328 : Nat := 4983230072969 + 3 ^ 40 * 5831328 * 2
def baseEnd_5831328 : Nat := 998091372673822045360739

theorem tailTrace_5831328 : CollatzResearch.WordTrace tailWord_5831328 prefixEnd_5831328 998091372673822045360739 := by
  unfold tailWord_5831328
  simp only [CollatzResearch.WordTrace]
  refine ⟨106343002509051021189471319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141790670012068028252628425 106343002509051021189471319)
  ·
    refine ⟨159514503763576531784206979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106343002509051021189471319 159514503763576531784206979)
    ·
      refine ⟨239271755645364797676310469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159514503763576531784206979 239271755645364797676310469)
      ·
        refine ⟨44863454183505899564308213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239271755645364797676310469 44863454183505899564308213)
        ·
          refine ⟨4205948829703678084153895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44863454183505899564308213 4205948829703678084153895)
          ·
            refine ⟨6308923244555517126230843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205948829703678084153895 6308923244555517126230843)
            ·
              refine ⟨9463384866833275689346265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308923244555517126230843 9463384866833275689346265)
              ·
                refine ⟨7097538650124956767009699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463384866833275689346265 7097538650124956767009699)
                ·
                  refine ⟨10646307975187435150514549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097538650124956767009699 10646307975187435150514549)
                  ·
                    refine ⟨998091372673822045360739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10646307975187435150514549 998091372673822045360739)
                    ·
                      rfl

theorem cell23_5831328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_5831328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831328 prefixEnd_5831328 := by exact prefixLift 5831328
  have htrace : WordTrace (prefixWord ++ tailWord_5831328) baseStart_5831328 baseEnd_5831328 := by
    simpa [prefixWord, tailWord_5831328, baseEnd_5831328] using wordTrace_append hprefix tailTrace_5831328
  have hstable : (prefixWord ++ tailWord_5831328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831328).length < 2 ^ (prefixWord ++ tailWord_5831328).sum := by decide
  have hdescent : baseEnd_5831328 < baseStart_5831328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831335 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5831335 : Nat := 118140960795 + 5831335 * 2 ^ 59
def prefixEnd_5831335 : Nat := 4983230072969 + 3 ^ 40 * 5831335 * 2
def baseEnd_5831335 : Nat := 2994277712386047608694685

theorem tailTrace_5831335 : CollatzResearch.WordTrace tailWord_5831335 prefixEnd_5831335 2994277712386047608694685 := by
  unfold tailWord_5831335
  simp only [CollatzResearch.WordTrace]
  refine ⟨212686260329076682574447459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141790840219384455049631639 212686260329076682574447459)
  ·
    refine ⟨319029390493615023861671189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212686260329076682574447459 319029390493615023861671189)
    ·
      refine ⟨14954502679388204243515837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 319029390493615023861671189 14954502679388204243515837)
      ·
        refine ⟨5607938504770576591318439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14954502679388204243515837 5607938504770576591318439)
        ·
          refine ⟨8411907757155864886977659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607938504770576591318439 8411907757155864886977659)
          ·
            refine ⟨12617861635733797330466489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411907757155864886977659 12617861635733797330466489)
            ·
              refine ⟨9463396226800347997849867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12617861635733797330466489 9463396226800347997849867)
              ·
                refine ⟨14195094340200521996774801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463396226800347997849867 14195094340200521996774801)
                ·
                  refine ⟨10646320755150391497581101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14195094340200521996774801 10646320755150391497581101)
                  ·
                    refine ⟨3992370283181396811592913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10646320755150391497581101 3992370283181396811592913)
                    ·
                      refine ⟨2994277712386047608694685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992370283181396811592913 2994277712386047608694685)
                      ·
                        rfl

theorem cell23_5831335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5831335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831335 prefixEnd_5831335 := by exact prefixLift 5831335
  have htrace : WordTrace (prefixWord ++ tailWord_5831335) baseStart_5831335 baseEnd_5831335 := by
    simpa [prefixWord, tailWord_5831335, baseEnd_5831335] using wordTrace_append hprefix tailTrace_5831335
  have hstable : (prefixWord ++ tailWord_5831335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831335).length < 2 ^ (prefixWord ++ tailWord_5831335).sum := by decide
  have hdescent : baseEnd_5831335 < baseStart_5831335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831351 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_5831351 : Nat := 118140960795 + 5831351 * 2 ^ 59
def prefixEnd_5831351 : Nat := 4983230072969 + 3 ^ 40 * 5831351 * 2
def baseEnd_5831351 : Nat := 2994285928076519546094611

theorem tailTrace_5831351 : CollatzResearch.WordTrace tailWord_5831351 prefixEnd_5831351 2994285928076519546094611 := by
  unfold tailWord_5831351
  simp only [CollatzResearch.WordTrace]
  refine ⟨212686843897018717307029907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141791229264679144871353271 212686843897018717307029907)
  ·
    refine ⟨319030265845528075960544861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212686843897018717307029907 319030265845528075960544861)
    ·
      refine ⟨119636349692073028485204323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319030265845528075960544861 119636349692073028485204323)
      ·
        refine ⟨179454524538109542727806485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119636349692073028485204323 179454524538109542727806485)
        ·
          refine ⟨8411930837723884815365929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179454524538109542727806485 8411930837723884815365929)
          ·
            refine ⟨6308948128292913611524447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8411930837723884815365929 6308948128292913611524447)
            ·
              refine ⟨9463422192439370417286671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308948128292913611524447 9463422192439370417286671)
              ·
                refine ⟨14195133288659055625930007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463422192439370417286671 14195133288659055625930007)
                ·
                  refine ⟨21292699932988583438895011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14195133288659055625930007 21292699932988583438895011)
                  ·
                    refine ⟨31939049899482875158342517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21292699932988583438895011 31939049899482875158342517)
                    ·
                      refine ⟨2994285928076519546094611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31939049899482875158342517 2994285928076519546094611)
                      ·
                        rfl

theorem cell23_5831351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_5831351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831351 prefixEnd_5831351 := by exact prefixLift 5831351
  have htrace : WordTrace (prefixWord ++ tailWord_5831351) baseStart_5831351 baseEnd_5831351 := by
    simpa [prefixWord, tailWord_5831351, baseEnd_5831351] using wordTrace_append hprefix tailTrace_5831351
  have hstable : (prefixWord ++ tailWord_5831351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831351).length < 2 ^ (prefixWord ++ tailWord_5831351).sum := by decide
  have hdescent : baseEnd_5831351 < baseStart_5831351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831391 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 3, 3, 2]
def baseStart_5831391 : Nat := 118140960795 + 5831391 * 2 ^ 59
def prefixEnd_5831391 : Nat := 4983230072969 + 3 ^ 40 * 5831391 * 2
def baseEnd_5831391 : Nat := 2994306467302699389594427

theorem tailTrace_5831391 : CollatzResearch.WordTrace tailWord_5831391 prefixEnd_5831391 2994306467302699389594427 := by
  unfold tailWord_5831391
  simp only [CollatzResearch.WordTrace]
  refine ⟨212688302816873804138486027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141792201877915869425657351 212688302816873804138486027)
  ·
    refine ⟨319032454225310706207729041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212688302816873804138486027 319032454225310706207729041)
    ·
      refine ⟨239274340668983029655796781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319032454225310706207729041 239274340668983029655796781)
      ·
        refine ⟨89727877750868636120923793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239274340668983029655796781 89727877750868636120923793)
        ·
          refine ⟨67295908313151477090692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89727877750868636120923793 67295908313151477090692845)
          ·
            refine ⟨25235965617431803909009817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67295908313151477090692845 25235965617431803909009817)
            ·
              refine ⟨18926974213073852931757363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25235965617431803909009817 18926974213073852931757363)
              ·
                refine ⟨28390461319610779397636045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18926974213073852931757363 28390461319610779397636045)
                ·
                  refine ⟨10646422994854042274113517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28390461319610779397636045 10646422994854042274113517)
                  ·
                    refine ⟨3992408623070265852792569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10646422994854042274113517 3992408623070265852792569)
                    ·
                      refine ⟨2994306467302699389594427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992408623070265852792569 2994306467302699389594427)
                      ·
                        rfl

theorem cell23_5831391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_5831391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831391 prefixEnd_5831391 := by exact prefixLift 5831391
  have htrace : WordTrace (prefixWord ++ tailWord_5831391) baseStart_5831391 baseEnd_5831391 := by
    simpa [prefixWord, tailWord_5831391, baseEnd_5831391] using wordTrace_append hprefix tailTrace_5831391
  have hstable : (prefixWord ++ tailWord_5831391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831391).length < 2 ^ (prefixWord ++ tailWord_5831391).sum := by decide
  have hdescent : baseEnd_5831391 < baseStart_5831391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831414 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5831414 : Nat := 118140960795 + 5831414 * 2 ^ 59
def prefixEnd_5831414 : Nat := 4983230072969 + 3 ^ 40 * 5831414 * 2
def baseEnd_5831414 : Nat := 998106092452584266535607

theorem tailTrace_5831414 : CollatzResearch.WordTrace tailWord_5831414 prefixEnd_5831414 998106092452584266535607 := by
  unfold tailWord_5831414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13293071355986904941660831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141792761130526986044382197 13293071355986904941660831)
  ·
    refine ⟨19939607033980357412491247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13293071355986904941660831 19939607033980357412491247)
    ·
      refine ⟨29909410550970536118736871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19939607033980357412491247 29909410550970536118736871)
      ·
        refine ⟨44864115826455804178105307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29909410550970536118736871 44864115826455804178105307)
        ·
          refine ⟨67296173739683706267157961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44864115826455804178105307 67296173739683706267157961)
          ·
            refine ⟨50472130304762779700368471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67296173739683706267157961 50472130304762779700368471)
            ·
              refine ⟨75708195457144169550552707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50472130304762779700368471 75708195457144169550552707)
              ·
                refine ⟨113562293185716254325829061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75708195457144169550552707 113562293185716254325829061)
                ·
                  refine ⟨21292929972321797686092949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113562293185716254325829061 21292929972321797686092949)
                  ·
                    refine ⟨998106092452584266535607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21292929972321797686092949 998106092452584266535607)
                    ·
                      rfl

theorem cell23_5831414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5831414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831414 prefixEnd_5831414 := by exact prefixLift 5831414
  have htrace : WordTrace (prefixWord ++ tailWord_5831414) baseStart_5831414 baseEnd_5831414 := by
    simpa [prefixWord, tailWord_5831414, baseEnd_5831414] using wordTrace_append hprefix tailTrace_5831414
  have hstable : (prefixWord ++ tailWord_5831414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831414).length < 2 ^ (prefixWord ++ tailWord_5831414).sum := by decide
  have hdescent : baseEnd_5831414 < baseStart_5831414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831434 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5831434 : Nat := 118140960795 + 5831434 * 2 ^ 59
def prefixEnd_5831434 : Nat := 4983230072969 + 3 ^ 40 * 5831434 * 2
def baseEnd_5831434 : Nat := 2994328546970842721356729

theorem tailTrace_5831434 : CollatzResearch.WordTrace tailWord_5831434 prefixEnd_5831434 2994328546970842721356729 := by
  unfold tailWord_5831434
  simp only [CollatzResearch.WordTrace]
  refine ⟨53172467788929505620575339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141793247437145348321534237 53172467788929505620575339)
  ·
    refine ⟨79758701683394258430863009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53172467788929505620575339 79758701683394258430863009)
    ·
      refine ⟨59819026262545693823147257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79758701683394258430863009 59819026262545693823147257)
      ·
        refine ⟨44864269696909270367360443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59819026262545693823147257 44864269696909270367360443)
        ·
          refine ⟨67296404545363905551040665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44864269696909270367360443 67296404545363905551040665)
          ·
            refine ⟨50472303409022929163280499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67296404545363905551040665 50472303409022929163280499)
            ·
              refine ⟨75708455113534393744920749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50472303409022929163280499 75708455113534393744920749)
              ·
                refine ⟨28390670667575397654345281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75708455113534393744920749 28390670667575397654345281)
                ·
                  refine ⟨21293003000681548240758961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28390670667575397654345281 21293003000681548240758961)
                  ·
                    refine ⟨15969752250511161180569221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21293003000681548240758961 15969752250511161180569221)
                    ·
                      refine ⟨2994328546970842721356729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15969752250511161180569221 2994328546970842721356729)
                      ·
                        rfl

theorem cell23_5831434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5831434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831434 prefixEnd_5831434 := by exact prefixLift 5831434
  have htrace : WordTrace (prefixWord ++ tailWord_5831434) baseStart_5831434 baseEnd_5831434 := by
    simpa [prefixWord, tailWord_5831434, baseEnd_5831434] using wordTrace_append hprefix tailTrace_5831434
  have hstable : (prefixWord ++ tailWord_5831434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831434).length < 2 ^ (prefixWord ++ tailWord_5831434).sum := by decide
  have hdescent : baseEnd_5831434 < baseStart_5831434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831442 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5831442 : Nat := 118140960795 + 5831442 * 2 ^ 59
def prefixEnd_5831442 : Nat := 4983230072969 + 3 ^ 40 * 5831442 * 2
def baseEnd_5831442 : Nat := 2994332654816078690056693

theorem tailTrace_5831442 : CollatzResearch.WordTrace tailWord_5831442 prefixEnd_5831442 2994332654816078690056693 := by
  unfold tailWord_5831442
  simp only [CollatzResearch.WordTrace]
  refine ⟨53172540734922259962148145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141793441959792693232395053 53172540734922259962148145)
  ·
    refine ⟨39879405551191694971611109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53172540734922259962148145 39879405551191694971611109)
    ·
      refine ⟨7477388540848442807177083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39879405551191694971611109 7477388540848442807177083)
      ·
        refine ⟨11216082811272664210765625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477388540848442807177083 11216082811272664210765625)
        ·
          refine ⟨8412062108454498158074219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11216082811272664210765625 8412062108454498158074219)
          ·
            refine ⟨12618093162681747237111329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412062108454498158074219 12618093162681747237111329)
            ·
              refine ⟨9463569872011310427833497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12618093162681747237111329 9463569872011310427833497)
              ·
                refine ⟨7097677404008482820875123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463569872011310427833497 7097677404008482820875123)
                ·
                  refine ⟨10646516106012724231312685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097677404008482820875123 10646516106012724231312685)
                  ·
                    refine ⟨3992443539754771586742257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10646516106012724231312685 3992443539754771586742257)
                    ·
                      refine ⟨2994332654816078690056693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992443539754771586742257 2994332654816078690056693)
                      ·
                        rfl

theorem cell23_5831442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5831442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831442 prefixEnd_5831442 := by exact prefixLift 5831442
  have htrace : WordTrace (prefixWord ++ tailWord_5831442) baseStart_5831442 baseEnd_5831442 := by
    simpa [prefixWord, tailWord_5831442, baseEnd_5831442] using wordTrace_append hprefix tailTrace_5831442
  have hstable : (prefixWord ++ tailWord_5831442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831442).length < 2 ^ (prefixWord ++ tailWord_5831442).sum := by decide
  have hdescent : baseEnd_5831442 < baseStart_5831442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831508 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5831508 : Nat := 118140960795 + 5831508 * 2 ^ 59
def prefixEnd_5831508 : Nat := 4983230072969 + 3 ^ 40 * 5831508 * 2
def baseEnd_5831508 : Nat := 998122181513091810610463

theorem tailTrace_5831508 : CollatzResearch.WordTrace tailWord_5831508 prefixEnd_5831508 998122181513091810610463 := by
  unfold tailWord_5831508
  simp only [CollatzResearch.WordTrace]
  refine ⟨106346285078724966560247589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141795046771633288746996785 106346285078724966560247589)
  ·
    refine ⟨19939928452260931230046423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106346285078724966560247589 19939928452260931230046423)
    ·
      refine ⟨29909892678391396845069635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19939928452260931230046423 29909892678391396845069635)
      ·
        refine ⟨44864839017587095267604453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29909892678391396845069635 44864839017587095267604453)
        ·
          refine ⟨8412157315797580362675835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44864839017587095267604453 8412157315797580362675835)
          ·
            refine ⟨12618235973696370544013753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412157315797580362675835 12618235973696370544013753)
            ·
              refine ⟨9463676980272277908010315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12618235973696370544013753 9463676980272277908010315)
              ·
                refine ⟨14195515470408416862015473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463676980272277908010315 14195515470408416862015473)
                ·
                  refine ⟨10646636602806312646511605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14195515470408416862015473 10646636602806312646511605)
                  ·
                    refine ⟨998122181513091810610463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10646636602806312646511605 998122181513091810610463)
                    ·
                      rfl

theorem cell23_5831508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5831508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831508 prefixEnd_5831508 := by exact prefixLift 5831508
  have htrace : WordTrace (prefixWord ++ tailWord_5831508) baseStart_5831508 baseEnd_5831508 := by
    simpa [prefixWord, tailWord_5831508, baseEnd_5831508] using wordTrace_append hprefix tailTrace_5831508
  have hstable : (prefixWord ++ tailWord_5831508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831508).length < 2 ^ (prefixWord ++ tailWord_5831508).sum := by decide
  have hdescent : baseEnd_5831508 < baseStart_5831508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831511 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_5831511 : Nat := 118140960795 + 5831511 * 2 ^ 59
def prefixEnd_5831511 : Nat := 4983230072969 + 3 ^ 40 * 5831511 * 2
def baseEnd_5831511 : Nat := 2994368084981238920093875

theorem tailTrace_5831511 : CollatzResearch.WordTrace tailWord_5831511 prefixEnd_5831511 2994368084981238920093875 := by
  unfold tailWord_5831511
  simp only [CollatzResearch.WordTrace]
  refine ⟨212692679576439064632854387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141795119717626043088569591 212692679576439064632854387)
  ·
    refine ⟨319039019364658596949281581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212692679576439064632854387 319039019364658596949281581)
    ·
      refine ⟨119639632261746973855980593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319039019364658596949281581 119639632261746973855980593)
      ·
        refine ⟨89729724196310230391985445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119639632261746973855980593 89729724196310230391985445)
        ·
          refine ⟨16824323286808168198497271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89729724196310230391985445 16824323286808168198497271)
          ·
            refine ⟨25236484930212252297745907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16824323286808168198497271 25236484930212252297745907)
            ·
              refine ⟨37854727395318378446618861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25236484930212252297745907 37854727395318378446618861)
              ·
                refine ⟨14195522773244391917482073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37854727395318378446618861 14195522773244391917482073)
                ·
                  refine ⟨10646642079933293938111555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14195522773244391917482073 10646642079933293938111555)
                  ·
                    refine ⟨15969963119899940907167333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10646642079933293938111555 15969963119899940907167333)
                    ·
                      refine ⟨2994368084981238920093875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15969963119899940907167333 2994368084981238920093875)
                      ·
                        rfl

theorem cell23_5831511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_5831511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831511 prefixEnd_5831511 := by exact prefixLift 5831511
  have htrace : WordTrace (prefixWord ++ tailWord_5831511) baseStart_5831511 baseEnd_5831511 := by
    simpa [prefixWord, tailWord_5831511, baseEnd_5831511] using wordTrace_append hprefix tailTrace_5831511
  have hstable : (prefixWord ++ tailWord_5831511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831511).length < 2 ^ (prefixWord ++ tailWord_5831511).sum := by decide
  have hdescent : baseEnd_5831511 < baseStart_5831511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831531 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3]
def baseStart_5831531 : Nat := 118140960795 + 5831531 * 2 ^ 59
def prefixEnd_5831531 : Nat := 4983230072969 + 3 ^ 40 * 5831531 * 2
def baseEnd_5831531 : Nat := 2994378354594328841843783

theorem tailTrace_5831531 : CollatzResearch.WordTrace tailWord_5831531 prefixEnd_5831531 2994378354594328841843783 := by
  unfold tailWord_5831531
  simp only [CollatzResearch.WordTrace]
  refine ⟨212693409036366608048582447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141795606024244405365721631 212693409036366608048582447)
  ·
    refine ⟨319040113554549912072873671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212693409036366608048582447 319040113554549912072873671)
    ·
      refine ⟨478560170331824868109310507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319040113554549912072873671 478560170331824868109310507)
      ·
        refine ⟨717840255497737302163965761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478560170331824868109310507 717840255497737302163965761)
        ·
          refine ⟨538380191623302976622974321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717840255497737302163965761 538380191623302976622974321)
          ·
            refine ⟨403785143717477232467230741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538380191623302976622974321 403785143717477232467230741)
            ·
              refine ⟨18927428611756745271901441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403785143717477232467230741 18927428611756745271901441)
              ·
                refine ⟨14195571458817558953926081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18927428611756745271901441 14195571458817558953926081)
                ·
                  refine ⟨10646678594113169215444561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14195571458817558953926081 10646678594113169215444561)
                  ·
                    refine ⟨7985008945584876911583421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10646678594113169215444561 7985008945584876911583421)
                    ·
                      refine ⟨2994378354594328841843783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7985008945584876911583421 2994378354594328841843783)
                      ·
                        rfl

theorem cell23_5831531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3].length) (baseStart_5831531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831531 prefixEnd_5831531 := by exact prefixLift 5831531
  have htrace : WordTrace (prefixWord ++ tailWord_5831531) baseStart_5831531 baseEnd_5831531 := by
    simpa [prefixWord, tailWord_5831531, baseEnd_5831531] using wordTrace_append hprefix tailTrace_5831531
  have hstable : (prefixWord ++ tailWord_5831531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831531).length < 2 ^ (prefixWord ++ tailWord_5831531).sum := by decide
  have hdescent : baseEnd_5831531 < baseStart_5831531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
