import V185TrunkScan22Chunk082

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_745239 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 2, 3]
def baseStart_745239 : Nat := 118140960795 + 745239 * 2 ^ 59
def prefixEnd_745239 : Nat := 4983230072969 + 3 ^ 40 * 745239 * 2
def baseEnd_745239 : Nat := 255110539650743321790143

theorem tailTrace_745239 : CollatzResearch.WordTrace tailWord_745239 prefixEnd_745239 255110539650743321790143 := by
  unfold tailWord_745239
  simp only [CollatzResearch.WordTrace]
  refine ⟨27181099347133854533294771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18120732898089236355529847 27181099347133854533294771)
  ·
    refine ⟨40771649020700781799942157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27181099347133854533294771 40771649020700781799942157)
    ·
      refine ⟨15289368382762793174978309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40771649020700781799942157 15289368382762793174978309)
      ·
        refine ⟨2866756571768023720308433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15289368382762793174978309 2866756571768023720308433)
        ·
          refine ⟨2150067428826017790231325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866756571768023720308433 2150067428826017790231325)
          ·
            refine ⟨806275285809756671336747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2150067428826017790231325 806275285809756671336747)
            ·
              refine ⟨1209412928714635007005121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806275285809756671336747 1209412928714635007005121)
              ·
                refine ⟨907059696535976255253841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209412928714635007005121 907059696535976255253841)
                ·
                  refine ⟨680294772401982191440381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907059696535976255253841 680294772401982191440381)
                  ·
                    refine ⟨255110539650743321790143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680294772401982191440381 255110539650743321790143)
                    ·
                      rfl

theorem cell22_745239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_745239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745239 prefixEnd_745239 := by exact prefixLift 745239
  have htrace : WordTrace (prefixWord ++ tailWord_745239) baseStart_745239 baseEnd_745239 := by
    simpa [prefixWord, tailWord_745239, baseEnd_745239] using wordTrace_append hprefix tailTrace_745239
  have hstable : (prefixWord ++ tailWord_745239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745239).length < 2 ^ (prefixWord ++ tailWord_745239).sum := by decide
  have hdescent : baseEnd_745239 < baseStart_745239 := by decide
  rcases family_descends (prefixWord ++ tailWord_745239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745269 : List Nat := [1, 3, 3, 1, 5, 1, 2, 6]
def baseStart_745269 : Nat := 118140960795 + 745269 * 2 ^ 59
def prefixEnd_745269 : Nat := 4983230072969 + 3 ^ 40 * 745269 * 2
def baseEnd_745269 : Nat := 28346756584870360393339

theorem tailTrace_745269 : CollatzResearch.WordTrace tailWord_745269 prefixEnd_745269 28346756584870360393339 := by
  unfold tailWord_745269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27182193537025169656886861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18121462358016779771257907 27182193537025169656886861)
  ·
    refine ⟨10193322576384438621332573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27182193537025169656886861 10193322576384438621332573)
    ·
      refine ⟨3822495966144164482999715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10193322576384438621332573 3822495966144164482999715)
      ·
        refine ⟨5733743949216246724499573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822495966144164482999715 5733743949216246724499573)
        ·
          refine ⟨537538495239023130421835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5733743949216246724499573 537538495239023130421835)
          ·
            refine ⟨806307742858534695632753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537538495239023130421835 806307742858534695632753)
            ·
              refine ⟨604730807143901021724565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806307742858534695632753 604730807143901021724565)
              ·
                refine ⟨28346756584870360393339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 604730807143901021724565 28346756584870360393339)
                ·
                  rfl

theorem cell22_745269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 6].length) (baseStart_745269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745269 prefixEnd_745269 := by exact prefixLift 745269
  have htrace : WordTrace (prefixWord ++ tailWord_745269) baseStart_745269 baseEnd_745269 := by
    simpa [prefixWord, tailWord_745269, baseEnd_745269] using wordTrace_append hprefix tailTrace_745269
  have hstable : (prefixWord ++ tailWord_745269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745269).length < 2 ^ (prefixWord ++ tailWord_745269).sum := by decide
  have hdescent : baseEnd_745269 < baseStart_745269 := by decide
  rcases family_descends (prefixWord ++ tailWord_745269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745301 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_745301 : Nat := 118140960795 + 745301 * 2 ^ 59
def prefixEnd_745301 : Nat := 4983230072969 + 3 ^ 40 * 745301 * 2
def baseEnd_745301 : Nat := 255131763517795826739953

theorem tailTrace_745301 : CollatzResearch.WordTrace tailWord_745301 prefixEnd_745301 255131763517795826739953 := by
  unfold tailWord_745301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27183360672909239122051757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18122240448606159414701171 27183360672909239122051757)
  ·
    refine ⟨10193760252340964670769409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27183360672909239122051757 10193760252340964670769409)
    ·
      refine ⟨7645320189255723503077057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10193760252340964670769409 7645320189255723503077057)
      ·
        refine ⟨5733990141941792627307793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7645320189255723503077057 5733990141941792627307793)
        ·
          refine ⟨4300492606456344470480845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733990141941792627307793 4300492606456344470480845)
          ·
            refine ⟨1612684727421129176430317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4300492606456344470480845 1612684727421129176430317)
            ·
              refine ⟨604756772782923441161369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1612684727421129176430317 604756772782923441161369)
              ·
                refine ⟨453567579587192580871027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604756772782923441161369 453567579587192580871027)
                ·
                  refine ⟨680351369380788871306541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453567579587192580871027 680351369380788871306541)
                  ·
                    refine ⟨255131763517795826739953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680351369380788871306541 255131763517795826739953)
                    ·
                      rfl

theorem cell22_745301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_745301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745301 prefixEnd_745301 := by exact prefixLift 745301
  have htrace : WordTrace (prefixWord ++ tailWord_745301) baseStart_745301 baseEnd_745301 := by
    simpa [prefixWord, tailWord_745301, baseEnd_745301] using wordTrace_append hprefix tailTrace_745301
  have hstable : (prefixWord ++ tailWord_745301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745301).length < 2 ^ (prefixWord ++ tailWord_745301).sum := by decide
  have hdescent : baseEnd_745301 < baseStart_745301 := by decide
  rcases family_descends (prefixWord ++ tailWord_745301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745314 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_745314 : Nat := 118140960795 + 745314 * 2 ^ 59
def prefixEnd_745314 : Nat := 4983230072969 + 3 ^ 40 * 745314 * 2
def baseEnd_745314 : Nat := 85045404561156042054971

theorem tailTrace_745314 : CollatzResearch.WordTrace tailWord_745314 prefixEnd_745314 85045404561156042054971 := by
  unfold tailWord_745314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795958705465535585568749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18122556547908094894849997 6795958705465535585568749)
  ·
    refine ⟨2548484514549575844588281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6795958705465535585568749 2548484514549575844588281)
    ·
      refine ⟨1911363385912181883441211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2548484514549575844588281 1911363385912181883441211)
      ·
        refine ⟨2867045078868272825161817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1911363385912181883441211 2867045078868272825161817)
        ·
          refine ⟨2150283809151204618871363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867045078868272825161817 2150283809151204618871363)
          ·
            refine ⟨3225425713726806928307045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150283809151204618871363 3225425713726806928307045)
            ·
              refine ⟨604767321323776299057571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3225425713726806928307045 604767321323776299057571)
              ·
                refine ⟨907150981985664448586357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604767321323776299057571 907150981985664448586357)
                ·
                  refine ⟨85045404561156042054971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 907150981985664448586357 85045404561156042054971)
                  ·
                    rfl

theorem cell22_745314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_745314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745314 prefixEnd_745314 := by exact prefixLift 745314
  have htrace : WordTrace (prefixWord ++ tailWord_745314) baseStart_745314 baseEnd_745314 := by
    simpa [prefixWord, tailWord_745314, baseEnd_745314] using wordTrace_append hprefix tailTrace_745314
  have hstable : (prefixWord ++ tailWord_745314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745314).length < 2 ^ (prefixWord ++ tailWord_745314).sum := by decide
  have hdescent : baseEnd_745314 < baseStart_745314 := by decide
  rcases family_descends (prefixWord ++ tailWord_745314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745325 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 6]
def baseStart_745325 : Nat := 118140960795 + 745325 * 2 ^ 59
def prefixEnd_745325 : Nat := 4983230072969 + 3 ^ 40 * 745325 * 2
def baseEnd_745325 : Nat := 85046659736089254713293

theorem tailTrace_745325 : CollatzResearch.WordTrace tailWord_745325 prefixEnd_745325 85046659736089254713293 := by
  unfold tailWord_745325
  simp only [CollatzResearch.WordTrace]
  refine ⟨27184236024822291220925429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18122824016548194147283619 27184236024822291220925429)
  ·
    refine ⟨2548522127327089801961759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27184236024822291220925429 2548522127327089801961759)
    ·
      refine ⟨3822783190990634702942639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548522127327089801961759 3822783190990634702942639)
      ·
        refine ⟨5734174786485952054413959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822783190990634702942639 5734174786485952054413959)
        ·
          refine ⟨8601262179728928081620939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5734174786485952054413959 8601262179728928081620939)
          ·
            refine ⟨12901893269593392122431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8601262179728928081620939 12901893269593392122431409)
            ·
              refine ⟨9676419952195044091823557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12901893269593392122431409 9676419952195044091823557)
              ·
                refine ⟨1814328741036570767216917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9676419952195044091823557 1814328741036570767216917)
                ·
                  refine ⟨85046659736089254713293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1814328741036570767216917 85046659736089254713293)
                  ·
                    rfl

theorem cell22_745325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_745325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745325 prefixEnd_745325 := by exact prefixLift 745325
  have htrace : WordTrace (prefixWord ++ tailWord_745325) baseStart_745325 baseEnd_745325 := by
    simpa [prefixWord, tailWord_745325, baseEnd_745325] using wordTrace_append hprefix tailTrace_745325
  have hstable : (prefixWord ++ tailWord_745325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745325).length < 2 ^ (prefixWord ++ tailWord_745325).sum := by decide
  have hdescent : baseEnd_745325 < baseStart_745325 := by decide
  rcases family_descends (prefixWord ++ tailWord_745325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745419 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 1, 3]
def baseStart_745419 : Nat := 118140960795 + 745419 * 2 ^ 59
def prefixEnd_745419 : Nat := 4983230072969 + 3 ^ 40 * 745419 * 2
def baseEnd_745419 : Nat := 255172157329282852289591

theorem tailTrace_745419 : CollatzResearch.WordTrace tailWord_745419 prefixEnd_745419 255172157329282852289591 := by
  unfold tailWord_745419
  simp only [CollatzResearch.WordTrace]
  refine ⟨27187664486481745274847311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18125109657654496849898207 27187664486481745274847311)
  ·
    refine ⟨40781496729722617912270967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27187664486481745274847311 40781496729722617912270967)
    ·
      refine ⟨61172245094583926868406451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40781496729722617912270967 61172245094583926868406451)
      ·
        refine ⟨91758367641875890302609677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61172245094583926868406451 91758367641875890302609677)
        ·
          refine ⟨34409387865703458863478629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91758367641875890302609677 34409387865703458863478629)
          ·
            refine ⟨6451760224819398536902243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34409387865703458863478629 6451760224819398536902243)
            ·
              refine ⟨9677640337229097805353365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451760224819398536902243 9677640337229097805353365)
              ·
                refine ⟨453639390807613959625939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9677640337229097805353365 453639390807613959625939)
                ·
                  refine ⟨680459086211420939438909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453639390807613959625939 680459086211420939438909)
                  ·
                    refine ⟨255172157329282852289591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680459086211420939438909 255172157329282852289591)
                    ·
                      rfl

theorem cell22_745419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 3].length) (baseStart_745419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745419 prefixEnd_745419 := by exact prefixLift 745419
  have htrace : WordTrace (prefixWord ++ tailWord_745419) baseStart_745419 baseEnd_745419 := by
    simpa [prefixWord, tailWord_745419, baseEnd_745419] using wordTrace_append hprefix tailTrace_745419
  have hstable : (prefixWord ++ tailWord_745419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745419).length < 2 ^ (prefixWord ++ tailWord_745419).sum := by decide
  have hdescent : baseEnd_745419 < baseStart_745419 := by decide
  rcases family_descends (prefixWord ++ tailWord_745419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745470 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_745470 : Nat := 118140960795 + 745470 * 2 ^ 59
def prefixEnd_745470 : Nat := 4983230072969 + 3 ^ 40 * 745470 * 2
def baseEnd_745470 : Nat := 255189615671535719264435

theorem tailTrace_745470 : CollatzResearch.WordTrace tailWord_745470 prefixEnd_745470 255189615671535719264435 := by
  unfold tailWord_745470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398690576162122623119233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18126349739531320656635909 3398690576162122623119233)
  ·
    refine ⟨2549017932121591967339425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3398690576162122623119233 2549017932121591967339425)
    ·
      refine ⟨1911763449091193975504569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2549017932121591967339425 1911763449091193975504569)
      ·
        refine ⟨1433822586818395481628427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1911763449091193975504569 1433822586818395481628427)
        ·
          refine ⟨2150733880227593222442641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433822586818395481628427 2150733880227593222442641)
          ·
            refine ⟨1613050410170694916831981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2150733880227593222442641 1613050410170694916831981)
            ·
              refine ⟨604893903814010593811993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1613050410170694916831981 604893903814010593811993)
              ·
                refine ⟨453670427860507945358995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604893903814010593811993 453670427860507945358995)
                ·
                  refine ⟨680505641790761918038493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453670427860507945358995 680505641790761918038493)
                  ·
                    refine ⟨255189615671535719264435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680505641790761918038493 255189615671535719264435)
                    ·
                      rfl

theorem cell22_745470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_745470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745470 prefixEnd_745470 := by exact prefixLift 745470
  have htrace : WordTrace (prefixWord ++ tailWord_745470) baseStart_745470 baseEnd_745470 := by
    simpa [prefixWord, tailWord_745470, baseEnd_745470] using wordTrace_append hprefix tailTrace_745470
  have hstable : (prefixWord ++ tailWord_745470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745470).length < 2 ^ (prefixWord ++ tailWord_745470).sum := by decide
  have hdescent : baseEnd_745470 < baseStart_745470 := by decide
  rcases family_descends (prefixWord ++ tailWord_745470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745477 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 6]
def baseStart_745477 : Nat := 118140960795 + 745477 * 2 ^ 59
def prefixEnd_745477 : Nat := 4983230072969 + 3 ^ 40 * 745477 * 2
def baseEnd_745477 : Nat := 85064003971530011446471

theorem tailTrace_745477 : CollatzResearch.WordTrace tailWord_745477 prefixEnd_745477 85064003971530011446471 := by
  unfold tailWord_745477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189779920271621180458685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18126519946847747453639123 27189779920271621180458685)
  ·
    refine ⟨10196167470101857942672007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27189779920271621180458685 10196167470101857942672007)
    ·
      refine ⟨15294251205152786914008011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10196167470101857942672007 15294251205152786914008011)
      ·
        refine ⟨22941376807729180371012017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15294251205152786914008011 22941376807729180371012017)
        ·
          refine ⟨17206032605796885278259013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22941376807729180371012017 17206032605796885278259013)
          ·
            refine ⟨3226131113586915989673565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17206032605796885278259013 3226131113586915989673565)
            ·
              refine ⟨1209799167595093496127587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226131113586915989673565 1209799167595093496127587)
              ·
                refine ⟨1814698751392640244191381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209799167595093496127587 1814698751392640244191381)
                ·
                  refine ⟨85064003971530011446471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1814698751392640244191381 85064003971530011446471)
                  ·
                    rfl

theorem cell22_745477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_745477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745477 prefixEnd_745477 := by exact prefixLift 745477
  have htrace : WordTrace (prefixWord ++ tailWord_745477) baseStart_745477 baseEnd_745477 := by
    simpa [prefixWord, tailWord_745477, baseEnd_745477] using wordTrace_append hprefix tailTrace_745477
  have hstable : (prefixWord ++ tailWord_745477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745477).length < 2 ^ (prefixWord ++ tailWord_745477).sum := by decide
  have hdescent : baseEnd_745477 < baseStart_745477 := by decide
  rcases family_descends (prefixWord ++ tailWord_745477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745528 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_745528 : Nat := 118140960795 + 745528 * 2 ^ 59
def prefixEnd_745528 : Nat := 4983230072969 + 3 ^ 40 * 745528 * 2
def baseEnd_745528 : Nat := 85069823418947633771419

theorem tailTrace_745528 : CollatzResearch.WordTrace tailWord_745528 prefixEnd_745528 85069823418947633771419 := by
  unfold tailWord_745528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595820021543428445282619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18127760028724571260376825 13595820021543428445282619)
  ·
    refine ⟨20393730032315142667923929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13595820021543428445282619 20393730032315142667923929)
    ·
      refine ⟨15295297524236357000942947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20393730032315142667923929 15295297524236357000942947)
      ·
        refine ⟨22942946286354535501414421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15295297524236357000942947 22942946286354535501414421)
        ·
          refine ⟨1075450607172868851628801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22942946286354535501414421 1075450607172868851628801)
          ·
            refine ⟨806587955379651638721601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075450607172868851628801 806587955379651638721601)
            ·
              refine ⟨604940966534738729041201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806587955379651638721601 604940966534738729041201)
              ·
                refine ⟨453705724901054046780901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604940966534738729041201 453705724901054046780901)
                ·
                  refine ⟨85069823418947633771419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453705724901054046780901 85069823418947633771419)
                  ·
                    rfl

theorem cell22_745528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_745528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745528 prefixEnd_745528 := by exact prefixLift 745528
  have htrace : WordTrace (prefixWord ++ tailWord_745528) baseStart_745528 baseEnd_745528 := by
    simpa [prefixWord, tailWord_745528, baseEnd_745528] using wordTrace_append hprefix tailTrace_745528
  have hstable : (prefixWord ++ tailWord_745528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745528).length < 2 ^ (prefixWord ++ tailWord_745528).sum := by decide
  have hdescent : baseEnd_745528 < baseStart_745528 := by decide
  rcases family_descends (prefixWord ++ tailWord_745528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745558 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_745558 : Nat := 118140960795 + 745558 * 2 ^ 59
def prefixEnd_745558 : Nat := 4983230072969 + 3 ^ 40 * 745558 * 2
def baseEnd_745558 : Nat := 255219739869932823064165

theorem tailTrace_745558 : CollatzResearch.WordTrace tailWord_745558 prefixEnd_745558 255219739869932823064165 := by
  unfold tailWord_745558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699545889561135750884833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18128489488652114676104885 1699545889561135750884833)
  ·
    refine ⟨1274659417170851813163625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1699545889561135750884833 1274659417170851813163625)
    ·
      refine ⟨955994562878138859872719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274659417170851813163625 955994562878138859872719)
      ·
        refine ⟨1433991844317208289809079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955994562878138859872719 1433991844317208289809079)
        ·
          refine ⟨2150987766475812434713619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433991844317208289809079 2150987766475812434713619)
          ·
            refine ⟨3226481649713718652070429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150987766475812434713619 3226481649713718652070429)
            ·
              refine ⟨1209930618642644494526411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226481649713718652070429 1209930618642644494526411)
              ·
                refine ⟨1814895927963966741789617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209930618642644494526411 1814895927963966741789617)
                ·
                  refine ⟨1361171945972975056342213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1814895927963966741789617 1361171945972975056342213)
                  ·
                    refine ⟨255219739869932823064165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1361171945972975056342213 255219739869932823064165)
                    ·
                      rfl

theorem cell22_745558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_745558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745558 prefixEnd_745558 := by exact prefixLift 745558
  have htrace : WordTrace (prefixWord ++ tailWord_745558) baseStart_745558 baseEnd_745558 := by
    simpa [prefixWord, tailWord_745558, baseEnd_745558] using wordTrace_append hprefix tailTrace_745558
  have hstable : (prefixWord ++ tailWord_745558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745558).length < 2 ^ (prefixWord ++ tailWord_745558).sum := by decide
  have hdescent : baseEnd_745558 < baseStart_745558 := by decide
  rcases family_descends (prefixWord ++ tailWord_745558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745571 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 1, 3]
def baseStart_745571 : Nat := 118140960795 + 745571 * 2 ^ 59
def prefixEnd_745571 : Nat := 4983230072969 + 3 ^ 40 * 745571 * 2
def baseEnd_745571 : Nat := 255224190035605122489125

theorem tailTrace_745571 : CollatzResearch.WordTrace tailWord_745571 prefixEnd_745571 255224190035605122489125 := by
  unfold tailWord_745571
  simp only [CollatzResearch.WordTrace]
  refine ⟨27193208381931075234380567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18128805587954050156253711 27193208381931075234380567)
  ·
    refine ⟨40789812572896612851570851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27193208381931075234380567 40789812572896612851570851)
    ·
      refine ⟨61184718859344919277356277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40789812572896612851570851 61184718859344919277356277)
      ·
        refine ⟨5736067393063586182252151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61184718859344919277356277 5736067393063586182252151)
        ·
          refine ⟨8604101089595379273378227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736067393063586182252151 8604101089595379273378227)
          ·
            refine ⟨12906151634393068910067341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604101089595379273378227 12906151634393068910067341)
            ·
              refine ⟨4839806862897400841275253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12906151634393068910067341 4839806862897400841275253)
              ·
                refine ⟨453731893396631328869555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4839806862897400841275253 453731893396631328869555)
                ·
                  refine ⟨680597840094946993304333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453731893396631328869555 680597840094946993304333)
                  ·
                    refine ⟨255224190035605122489125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680597840094946993304333 255224190035605122489125)
                    ·
                      rfl

theorem cell22_745571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 3].length) (baseStart_745571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745571 prefixEnd_745571 := by exact prefixLift 745571
  have htrace : WordTrace (prefixWord ++ tailWord_745571) baseStart_745571 baseEnd_745571 := by
    simpa [prefixWord, tailWord_745571, baseEnd_745571] using wordTrace_append hprefix tailTrace_745571
  have hstable : (prefixWord ++ tailWord_745571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745571).length < 2 ^ (prefixWord ++ tailWord_745571).sum := by decide
  have hdescent : baseEnd_745571 < baseStart_745571 := by decide
  rcases family_descends (prefixWord ++ tailWord_745571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745584 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_745584 : Nat := 118140960795 + 745584 * 2 ^ 59
def prefixEnd_745584 : Nat := 4983230072969 + 3 ^ 40 * 745584 * 2
def baseEnd_745584 : Nat := 85076213400425807304695

theorem tailTrace_745584 : CollatzResearch.WordTrace tailWord_745584 prefixEnd_745584 85076213400425807304695 := by
  unfold tailWord_745584
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596841265441989227301903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18129121687255985636402537 13596841265441989227301903)
  ·
    refine ⟨20395261898162983840952855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13596841265441989227301903 20395261898162983840952855)
    ·
      refine ⟨30592892847244475761429283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20395261898162983840952855 30592892847244475761429283)
      ·
        refine ⟨45889339270866713642143925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30592892847244475761429283 45889339270866713642143925)
        ·
          refine ⟨4302125556643754403950993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45889339270866713642143925 4302125556643754403950993)
          ·
            refine ⟨3226594167482815802963245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4302125556643754403950993 3226594167482815802963245)
            ·
              refine ⟨1209972812806055926111217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226594167482815802963245 1209972812806055926111217)
              ·
                refine ⟨907479609604541944583413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209972812806055926111217 907479609604541944583413)
                ·
                  refine ⟨85076213400425807304695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 907479609604541944583413 85076213400425807304695)
                  ·
                    rfl

theorem cell22_745584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_745584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745584 prefixEnd_745584 := by exact prefixLift 745584
  have htrace : WordTrace (prefixWord ++ tailWord_745584) baseStart_745584 baseEnd_745584 := by
    simpa [prefixWord, tailWord_745584, baseEnd_745584] using wordTrace_append hprefix tailTrace_745584
  have hstable : (prefixWord ++ tailWord_745584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745584).length < 2 ^ (prefixWord ++ tailWord_745584).sum := by decide
  have hdescent : baseEnd_745584 < baseStart_745584 := by decide
  rcases family_descends (prefixWord ++ tailWord_745584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745631 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 1, 4]
def baseStart_745631 : Nat := 118140960795 + 745631 * 2 ^ 59
def prefixEnd_745631 : Nat := 4983230072969 + 3 ^ 40 * 745631 * 2
def baseEnd_745631 : Nat := 255244729261784965988941

theorem tailTrace_745631 : CollatzResearch.WordTrace tailWord_745631 prefixEnd_745631 255244729261784965988941 := by
  unfold tailWord_745631
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195396761713705481564747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18130264507809136987709831 27195396761713705481564747)
  ·
    refine ⟨40793095142570558222347121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27195396761713705481564747 40793095142570558222347121)
    ·
      refine ⟨30594821356927918666760341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40793095142570558222347121 30594821356927918666760341)
      ·
        refine ⟨1434132251105996187504391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30594821356927918666760341 1434132251105996187504391)
        ·
          refine ⟨2151198376658994281256587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434132251105996187504391 2151198376658994281256587)
          ·
            refine ⟨3226797564988491421884881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151198376658994281256587 3226797564988491421884881)
            ·
              refine ⟨2420098173741368566413661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226797564988491421884881 2420098173741368566413661)
              ·
                refine ⟨907536815153013212405123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2420098173741368566413661 907536815153013212405123)
                ·
                  refine ⟨1361305222729519818607685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907536815153013212405123 1361305222729519818607685)
                  ·
                    refine ⟨255244729261784965988941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1361305222729519818607685 255244729261784965988941)
                    ·
                      rfl

theorem cell22_745631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_745631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745631 prefixEnd_745631 := by exact prefixLift 745631
  have htrace : WordTrace (prefixWord ++ tailWord_745631) baseStart_745631 baseEnd_745631 := by
    simpa [prefixWord, tailWord_745631, baseEnd_745631] using wordTrace_append hprefix tailTrace_745631
  have hstable : (prefixWord ++ tailWord_745631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745631).length < 2 ^ (prefixWord ++ tailWord_745631).sum := by decide
  have hdescent : baseEnd_745631 < baseStart_745631 := by decide
  rcases family_descends (prefixWord ++ tailWord_745631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745665 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_745665 : Nat := 118140960795 + 745665 * 2 ^ 59
def prefixEnd_745665 : Nat := 4983230072969 + 3 ^ 40 * 745665 * 2
def baseEnd_745665 : Nat := 255256368156620210638837

theorem tailTrace_745665 : CollatzResearch.WordTrace tailWord_745665 prefixEnd_745665 255256368156620210638837 := by
  unfold tailWord_745665
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196636843590529288302449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18131091229060352858868299 27196636843590529288302449)
  ·
    refine ⟨20397477632692896966226837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27196636843590529288302449 20397477632692896966226837)
    ·
      refine ⟨956131764032479545291883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20397477632692896966226837 956131764032479545291883)
      ·
        refine ⟨1434197646048719317937825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956131764032479545291883 1434197646048719317937825)
        ·
          refine ⟨1075648234536539488453369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434197646048719317937825 1075648234536539488453369)
          ·
            refine ⟨806736175902404616340027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075648234536539488453369 806736175902404616340027)
            ·
              refine ⟨1210104263853606924510041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806736175902404616340027 1210104263853606924510041)
              ·
                refine ⟨907578197890205193382531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210104263853606924510041 907578197890205193382531)
                ·
                  refine ⟨1361367296835307790073797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907578197890205193382531 1361367296835307790073797)
                  ·
                    refine ⟨255256368156620210638837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1361367296835307790073797 255256368156620210638837)
                    ·
                      rfl

theorem cell22_745665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_745665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745665 prefixEnd_745665 := by exact prefixLift 745665
  have htrace : WordTrace (prefixWord ++ tailWord_745665) baseStart_745665 baseEnd_745665 := by
    simpa [prefixWord, tailWord_745665, baseEnd_745665] using wordTrace_append hprefix tailTrace_745665
  have hstable : (prefixWord ++ tailWord_745665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745665).length < 2 ^ (prefixWord ++ tailWord_745665).sum := by decide
  have hdescent : baseEnd_745665 < baseStart_745665 := by decide
  rcases family_descends (prefixWord ++ tailWord_745665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745704 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_745704 : Nat := 118140960795 + 745704 * 2 ^ 59
def prefixEnd_745704 : Nat := 4983230072969 + 3 ^ 40 * 745704 * 2
def baseEnd_745704 : Nat := 255269718653637108913717

theorem tailTrace_745704 : CollatzResearch.WordTrace tailWord_745704 prefixEnd_745704 255269718653637108913717 := by
  unfold tailWord_745704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599029645224619474486083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18132039526966159299314777 13599029645224619474486083)
  ·
    refine ⟨20398544467836929211729125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13599029645224619474486083 20398544467836929211729125)
    ·
      refine ⟨3824727087719424227199211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20398544467836929211729125 3824727087719424227199211)
      ·
        refine ⟨5737090631579136340798817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824727087719424227199211 5737090631579136340798817)
        ·
          refine ⟨4302817973684352255599113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5737090631579136340798817 4302817973684352255599113)
          ·
            refine ⟨3227113480263264191699335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4302817973684352255599113 3227113480263264191699335)
            ·
              refine ⟨4840670220394896287549003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227113480263264191699335 4840670220394896287549003)
              ·
                refine ⟨7261005330592344431323505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840670220394896287549003 7261005330592344431323505)
                ·
                  refine ⟨5445753997944258323492629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261005330592344431323505 5445753997944258323492629)
                  ·
                    refine ⟨255269718653637108913717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5445753997944258323492629 255269718653637108913717)
                    ·
                      rfl

theorem cell22_745704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_745704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745704 prefixEnd_745704 := by exact prefixLift 745704
  have htrace : WordTrace (prefixWord ++ tailWord_745704) baseStart_745704 baseEnd_745704 := by
    simpa [prefixWord, tailWord_745704, baseEnd_745704] using wordTrace_append hprefix tailTrace_745704
  have hstable : (prefixWord ++ tailWord_745704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745704).length < 2 ^ (prefixWord ++ tailWord_745704).sum := by decide
  have hdescent : baseEnd_745704 < baseStart_745704 := by decide
  rcases family_descends (prefixWord ++ tailWord_745704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745706 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_745706 : Nat := 118140960795 + 745706 * 2 ^ 59
def prefixEnd_745706 : Nat := 4983230072969 + 3 ^ 40 * 745706 * 2
def baseEnd_745706 : Nat := 255270403294509770363711

theorem tailTrace_745706 : CollatzResearch.WordTrace tailWord_745706 prefixEnd_745706 255270403294509770363711 := by
  unfold tailWord_745706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799533059110498322636243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18132088157627995527029981 6799533059110498322636243)
  ·
    refine ⟨10199299588665747483954365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6799533059110498322636243 10199299588665747483954365)
    ·
      refine ⟨3824737345749655306482887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10199299588665747483954365 3824737345749655306482887)
      ·
        refine ⟨5737106018624482959724331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824737345749655306482887 5737106018624482959724331)
        ·
          refine ⟨8605659027936724439586497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737106018624482959724331 8605659027936724439586497)
          ·
            refine ⟨6454244270952543329689873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8605659027936724439586497 6454244270952543329689873)
            ·
              refine ⟨4840683203214407497267405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454244270952543329689873 4840683203214407497267405)
              ·
                refine ⟨1815256201205402811475277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4840683203214407497267405 1815256201205402811475277)
                ·
                  refine ⟨680721075452026054303229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1815256201205402811475277 680721075452026054303229)
                  ·
                    refine ⟨255270403294509770363711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680721075452026054303229 255270403294509770363711)
                    ·
                      rfl

theorem cell22_745706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_745706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745706 prefixEnd_745706 := by exact prefixLift 745706
  have htrace : WordTrace (prefixWord ++ tailWord_745706) baseStart_745706 baseEnd_745706 := by
    simpa [prefixWord, tailWord_745706, baseEnd_745706] using wordTrace_append hprefix tailTrace_745706
  have hstable : (prefixWord ++ tailWord_745706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745706).length < 2 ^ (prefixWord ++ tailWord_745706).sum := by decide
  have hdescent : baseEnd_745706 < baseStart_745706 := by decide
  rcases family_descends (prefixWord ++ tailWord_745706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745770 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_745770 : Nat := 118140960795 + 745770 * 2 ^ 59
def prefixEnd_745770 : Nat := 4983230072969 + 3 ^ 40 * 745770 * 2
def baseEnd_745770 : Nat := 85097437267478312254505

theorem tailTrace_745770 : CollatzResearch.WordTrace tailWord_745770 prefixEnd_745770 85097437267478312254505 := by
  unfold tailWord_745770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800116627052533055218691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18133644338806754813916509 6800116627052533055218691)
  ·
    refine ⟨10200174940578799582828037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800116627052533055218691 10200174940578799582828037)
    ·
      refine ⟨1912532801358524921780257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10200174940578799582828037 1912532801358524921780257)
      ·
        refine ⟨1434399601018893691335193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912532801358524921780257 1434399601018893691335193)
        ·
          refine ⟨1075799700764170268501395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434399601018893691335193 1075799700764170268501395)
          ·
            refine ⟨1613699551146255402752093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075799700764170268501395 1613699551146255402752093)
            ·
              refine ⟨605137331679845776032035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1613699551146255402752093 605137331679845776032035)
              ·
                refine ⟨907705997519768664048053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605137331679845776032035 907705997519768664048053)
                ·
                  refine ⟨85097437267478312254505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 907705997519768664048053 85097437267478312254505)
                  ·
                    rfl

theorem cell22_745770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_745770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745770 prefixEnd_745770 := by exact prefixLift 745770
  have htrace : WordTrace (prefixWord ++ tailWord_745770) baseStart_745770 baseEnd_745770 := by
    simpa [prefixWord, tailWord_745770, baseEnd_745770] using wordTrace_append hprefix tailTrace_745770
  have hstable : (prefixWord ++ tailWord_745770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745770).length < 2 ^ (prefixWord ++ tailWord_745770).sum := by decide
  have hdescent : baseEnd_745770 < baseStart_745770 := by decide
  rcases family_descends (prefixWord ++ tailWord_745770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745809 : List Nat := [1, 2, 2, 1, 4, 2, 10]
def baseStart_745809 : Nat := 118140960795 + 745809 * 2 ^ 59
def prefixEnd_745809 : Nat := 4983230072969 + 3 ^ 40 * 745809 * 2
def baseEnd_745809 : Nat := 9455765270350067964385

theorem tailTrace_745809 : CollatzResearch.WordTrace tailWord_745809 prefixEnd_745809 9455765270350067964385 := by
  unfold tailWord_745809
  simp only [CollatzResearch.WordTrace]
  refine ⟨27201888955068841881544481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18134592636712561254362987 27201888955068841881544481)
  ·
    refine ⟨20401416716301631411158361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27201888955068841881544481 20401416716301631411158361)
    ·
      refine ⟨15301062537226223558368771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20401416716301631411158361 15301062537226223558368771)
      ·
        refine ⟨22951593805839335337553157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15301062537226223558368771 22951593805839335337553157)
        ·
          refine ⟨4303423838594875375791217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22951593805839335337553157 4303423838594875375791217)
          ·
            refine ⟨3227567878946156531843413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4303423838594875375791217 3227567878946156531843413)
            ·
              refine ⟨9455765270350067964385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3227567878946156531843413 9455765270350067964385)
              ·
                rfl

theorem cell22_745809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 10].length) (baseStart_745809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745809 prefixEnd_745809 := by exact prefixLift 745809
  have htrace : WordTrace (prefixWord ++ tailWord_745809) baseStart_745809 baseEnd_745809 := by
    simpa [prefixWord, tailWord_745809, baseEnd_745809] using wordTrace_append hprefix tailTrace_745809
  have hstable : (prefixWord ++ tailWord_745809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745809).length < 2 ^ (prefixWord ++ tailWord_745809).sum := by decide
  have hdescent : baseEnd_745809 < baseStart_745809 := by decide
  rcases family_descends (prefixWord ++ tailWord_745809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745826 : List Nat := [3, 3, 2, 1, 1, 2, 1, 9]
def baseStart_745826 : Nat := 118140960795 + 745826 * 2 ^ 59
def prefixEnd_745826 : Nat := 4983230072969 + 3 ^ 40 * 745826 * 2
def baseEnd_745826 : Nat := 28367942416318828595927

theorem tailTrace_745826 : CollatzResearch.WordTrace tailWord_745826 prefixEnd_745826 28367942416318828595927 := by
  unfold tailWord_745826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800627249001813446228333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18135005997338169189942221 6800627249001813446228333)
  ·
    refine ⟨2550235218375680042335625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6800627249001813446228333 2550235218375680042335625)
    ·
      refine ⟨1912676413781760031751719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550235218375680042335625 1912676413781760031751719)
      ·
        refine ⟨2869014620672640047627579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912676413781760031751719 2869014620672640047627579)
        ·
          refine ⟨4303521931008960071441369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869014620672640047627579 4303521931008960071441369)
          ·
            refine ⟨3227641448256720053581027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4303521931008960071441369 3227641448256720053581027)
            ·
              refine ⟨4841462172385080080371541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227641448256720053581027 4841462172385080080371541)
              ·
                refine ⟨28367942416318828595927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4841462172385080080371541 28367942416318828595927)
                ·
                  rfl

theorem cell22_745826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_745826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745826 prefixEnd_745826 := by exact prefixLift 745826
  have htrace : WordTrace (prefixWord ++ tailWord_745826) baseStart_745826 baseEnd_745826 := by
    simpa [prefixWord, tailWord_745826, baseEnd_745826] using wordTrace_append hprefix tailTrace_745826
  have hstable : (prefixWord ++ tailWord_745826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745826).length < 2 ^ (prefixWord ++ tailWord_745826).sum := by decide
  have hdescent : baseEnd_745826 < baseStart_745826 := by decide
  rcases family_descends (prefixWord ++ tailWord_745826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745839 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_745839 : Nat := 118140960795 + 745839 * 2 ^ 59
def prefixEnd_745839 : Nat := 4983230072969 + 3 ^ 40 * 745839 * 2
def baseEnd_745839 : Nat := 255315931912541756788303

theorem tailTrace_745839 : CollatzResearch.WordTrace tailWord_745839 prefixEnd_745839 255315931912541756788303 := by
  unfold tailWord_745839
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202983144960157005136571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135322096640104670091047 27202983144960157005136571)
  ·
    refine ⟨40804474717440235507704857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27202983144960157005136571 40804474717440235507704857)
    ·
      refine ⟨30603356038080176630778643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40804474717440235507704857 30603356038080176630778643)
      ·
        refine ⟨45905034057120264946167965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30603356038080176630778643 45905034057120264946167965)
        ·
          refine ⟨17214387771420099354812987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45905034057120264946167965 17214387771420099354812987)
          ·
            refine ⟨25821581657130149032219481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17214387771420099354812987 25821581657130149032219481)
            ·
              refine ⟨19366186242847611774164611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25821581657130149032219481 19366186242847611774164611)
              ·
                refine ⟨29049279364271417661246917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19366186242847611774164611 29049279364271417661246917)
                ·
                  refine ⟨5446739880800890811483797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29049279364271417661246917 5446739880800890811483797)
                  ·
                    refine ⟨255315931912541756788303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5446739880800890811483797 255315931912541756788303)
                    ·
                      rfl

theorem cell22_745839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_745839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745839 prefixEnd_745839 := by exact prefixLift 745839
  have htrace : WordTrace (prefixWord ++ tailWord_745839) baseStart_745839 baseEnd_745839 := by
    simpa [prefixWord, tailWord_745839, baseEnd_745839] using wordTrace_append hprefix tailTrace_745839
  have hstable : (prefixWord ++ tailWord_745839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745839).length < 2 ^ (prefixWord ++ tailWord_745839).sum := by decide
  have hdescent : baseEnd_745839 < baseStart_745839 := by decide
  rcases family_descends (prefixWord ++ tailWord_745839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745841 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_745841 : Nat := 118140960795 + 745841 * 2 ^ 59
def prefixEnd_745841 : Nat := 4983230072969 + 3 ^ 40 * 745841 * 2
def baseEnd_745841 : Nat := 255316616553414418238297

theorem tailTrace_745841 : CollatzResearch.WordTrace tailWord_745841 prefixEnd_745841 255316616553414418238297 := by
  unfold tailWord_745841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203056090952911346709377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135370727301940897806251 27203056090952911346709377)
  ·
    refine ⟨20402292068214683510032033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27203056090952911346709377 20402292068214683510032033)
    ·
      refine ⟨15301719051161012632524025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20402292068214683510032033 15301719051161012632524025)
      ·
        refine ⟨11476289288370759474393019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15301719051161012632524025 11476289288370759474393019)
        ·
          refine ⟨17214433932556139211589529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11476289288370759474393019 17214433932556139211589529)
          ·
            refine ⟨12910825449417104408692147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17214433932556139211589529 12910825449417104408692147)
            ·
              refine ⟨19366238174125656613038221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12910825449417104408692147 19366238174125656613038221)
              ·
                refine ⟨7262339315297121229889333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19366238174125656613038221 7262339315297121229889333)
                ·
                  refine ⟨680844310809105115302125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7262339315297121229889333 680844310809105115302125)
                  ·
                    refine ⟨255316616553414418238297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680844310809105115302125 255316616553414418238297)
                    ·
                      rfl

theorem cell22_745841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_745841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745841 prefixEnd_745841 := by exact prefixLift 745841
  have htrace : WordTrace (prefixWord ++ tailWord_745841) baseStart_745841 baseEnd_745841 := by
    simpa [prefixWord, tailWord_745841, baseEnd_745841] using wordTrace_append hprefix tailTrace_745841
  have hstable : (prefixWord ++ tailWord_745841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745841).length < 2 ^ (prefixWord ++ tailWord_745841).sum := by decide
  have hdescent : baseEnd_745841 < baseStart_745841 := by decide
  rcases family_descends (prefixWord ++ tailWord_745841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745946 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_745946 : Nat := 118140960795 + 745946 * 2 ^ 59
def prefixEnd_745946 : Nat := 4983230072969 + 3 ^ 40 * 745946 * 2
def baseEnd_745946 : Nat := 255352560199229144362975

theorem tailTrace_745946 : CollatzResearch.WordTrace tailWord_745946 prefixEnd_745946 255352560199229144362975 := by
  unfold tailWord_745946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801721438893128569820423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18137923837048342852854461 6801721438893128569820423)
  ·
    refine ⟨10202582158339692854730635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6801721438893128569820423 10202582158339692854730635)
    ·
      refine ⟨15303873237509539282095953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202582158339692854730635 15303873237509539282095953)
      ·
        refine ⟨11477904928132154461571965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15303873237509539282095953 11477904928132154461571965)
        ·
          refine ⟨4304214348049557923089487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11477904928132154461571965 4304214348049557923089487)
          ·
            refine ⟨6456321522074336884634231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304214348049557923089487 6456321522074336884634231)
            ·
              refine ⟨9684482283111505326951347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456321522074336884634231 9684482283111505326951347)
              ·
                refine ⟨14526723424667257990427021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684482283111505326951347 14526723424667257990427021)
                ·
                  refine ⟨5447521284250221746410133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14526723424667257990427021 5447521284250221746410133)
                  ·
                    refine ⟨255352560199229144362975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5447521284250221746410133 255352560199229144362975)
                    ·
                      rfl

theorem cell22_745946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_745946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745946 prefixEnd_745946 := by exact prefixLift 745946
  have htrace : WordTrace (prefixWord ++ tailWord_745946) baseStart_745946 baseEnd_745946 := by
    simpa [prefixWord, tailWord_745946, baseEnd_745946] using wordTrace_append hprefix tailTrace_745946
  have hstable : (prefixWord ++ tailWord_745946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745946).length < 2 ^ (prefixWord ++ tailWord_745946).sum := by decide
  have hdescent : baseEnd_745946 < baseStart_745946 := by decide
  rcases family_descends (prefixWord ++ tailWord_745946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745965 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_745965 : Nat := 118140960795 + 745965 * 2 ^ 59
def prefixEnd_745965 : Nat := 4983230072969 + 3 ^ 40 * 745965 * 2
def baseEnd_745965 : Nat := 255359064287519428137917

theorem tailTrace_745965 : CollatzResearch.WordTrace tailWord_745965 prefixEnd_745965 255359064287519428137917 := by
  unfold tailWord_745965
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207578742503680524223349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18138385828335787016148899 27207578742503680524223349)
  ·
    refine ⟨2550710507109720049145939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27207578742503680524223349 2550710507109720049145939)
    ·
      refine ⟨3826065760664580073718909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550710507109720049145939 3826065760664580073718909)
      ·
        refine ⟨1434774660249217527644591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3826065760664580073718909 1434774660249217527644591)
        ·
          refine ⟨2152161990373826291466887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434774660249217527644591 2152161990373826291466887)
          ·
            refine ⟨3228242985560739437200331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152161990373826291466887 3228242985560739437200331)
            ·
              refine ⟨4842364478341109155800497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228242985560739437200331 4842364478341109155800497)
              ·
                refine ⟨3631773358755831866850373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842364478341109155800497 3631773358755831866850373)
                ·
                  refine ⟨680957504766718475034445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3631773358755831866850373 680957504766718475034445)
                  ·
                    refine ⟨255359064287519428137917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680957504766718475034445 255359064287519428137917)
                    ·
                      rfl

theorem cell22_745965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_745965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745965 prefixEnd_745965 := by exact prefixLift 745965
  have htrace : WordTrace (prefixWord ++ tailWord_745965) baseStart_745965 baseEnd_745965 := by
    simpa [prefixWord, tailWord_745965, baseEnd_745965] using wordTrace_append hprefix tailTrace_745965
  have hstable : (prefixWord ++ tailWord_745965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745965).length < 2 ^ (prefixWord ++ tailWord_745965).sum := by decide
  have hdescent : baseEnd_745965 < baseStart_745965 := by decide
  rcases family_descends (prefixWord ++ tailWord_745965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745993 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_745993 : Nat := 118140960795 + 745993 * 2 ^ 59
def prefixEnd_745993 : Nat := 4983230072969 + 3 ^ 40 * 745993 * 2
def baseEnd_745993 : Nat := 255368649259736688437831

theorem tailTrace_745993 : CollatzResearch.WordTrace tailWord_745993 prefixEnd_745993 255368649259736688437831 := by
  unfold tailWord_745993
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208599986402241306242633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18139066657601494204161755 27208599986402241306242633)
  ·
    refine ⟨20406449989801680979681975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27208599986402241306242633 20406449989801680979681975)
    ·
      refine ⟨30609674984702521469522963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20406449989801680979681975 30609674984702521469522963)
      ·
        refine ⟨45914512477053782204284445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30609674984702521469522963 45914512477053782204284445)
        ·
          refine ⟨17217942178895168326606667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45914512477053782204284445 17217942178895168326606667)
          ·
            refine ⟨25826913268342752489910001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217942178895168326606667 25826913268342752489910001)
            ·
              refine ⟨19370184951257064367432501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25826913268342752489910001 19370184951257064367432501)
              ·
                refine ⟨1815954839180349784446797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19370184951257064367432501 1815954839180349784446797)
                ·
                  refine ⟨680983064692631169167549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1815954839180349784446797 680983064692631169167549)
                  ·
                    refine ⟨255368649259736688437831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680983064692631169167549 255368649259736688437831)
                    ·
                      rfl

theorem cell22_745993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_745993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745993 prefixEnd_745993 := by exact prefixLift 745993
  have htrace : WordTrace (prefixWord ++ tailWord_745993) baseStart_745993 baseEnd_745993 := by
    simpa [prefixWord, tailWord_745993, baseEnd_745993] using wordTrace_append hprefix tailTrace_745993
  have hstable : (prefixWord ++ tailWord_745993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745993).length < 2 ^ (prefixWord ++ tailWord_745993).sum := by decide
  have hdescent : baseEnd_745993 < baseStart_745993 := by decide
  rcases family_descends (prefixWord ++ tailWord_745993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746044 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_746044 : Nat := 118140960795 + 746044 * 2 ^ 59
def prefixEnd_746044 : Nat := 4983230072969 + 3 ^ 40 * 746044 * 2
def baseEnd_746044 : Nat := 255386107601989555412675

theorem tailTrace_746044 : CollatzResearch.WordTrace tailWord_746044 prefixEnd_746044 255386107601989555412675 := by
  unfold tailWord_746044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605230054608738508174593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18140306739478318010899457 13605230054608738508174593)
  ·
    refine ⟨10203922540956553881130945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13605230054608738508174593 10203922540956553881130945)
    ·
      refine ⟨7652941905717415410848209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10203922540956553881130945 7652941905717415410848209)
      ·
        refine ⟨5739706429288061558136157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7652941905717415410848209 5739706429288061558136157)
        ·
          refine ⟨2152389910983023084301059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5739706429288061558136157 2152389910983023084301059)
          ·
            refine ⟨3228584866474534626451589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152389910983023084301059 3228584866474534626451589)
            ·
              refine ⟨605359662463975242459673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3228584866474534626451589 605359662463975242459673)
              ·
                refine ⟨454019746847981431844755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605359662463975242459673 454019746847981431844755)
                ·
                  refine ⟨681029620271972147767133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454019746847981431844755 681029620271972147767133)
                  ·
                    refine ⟨255386107601989555412675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681029620271972147767133 255386107601989555412675)
                    ·
                      rfl

theorem cell22_746044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_746044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746044 prefixEnd_746044 := by exact prefixLift 746044
  have htrace : WordTrace (prefixWord ++ tailWord_746044) baseStart_746044 baseEnd_746044 := by
    simpa [prefixWord, tailWord_746044, baseEnd_746044] using wordTrace_append hprefix tailTrace_746044
  have hstable : (prefixWord ++ tailWord_746044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746044).length < 2 ^ (prefixWord ++ tailWord_746044).sum := by decide
  have hdescent : baseEnd_746044 < baseStart_746044 := by decide
  rcases family_descends (prefixWord ++ tailWord_746044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746051 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 10]
def baseStart_746051 : Nat := 118140960795 + 746051 * 2 ^ 59
def prefixEnd_746051 : Nat := 4983230072969 + 3 ^ 40 * 746051 * 2
def baseEnd_746051 : Nat := 85129501281681290162551

theorem tailTrace_746051 : CollatzResearch.WordTrace tailWord_746051 prefixEnd_746051 85129501281681290162551 := by
  unfold tailWord_746051
  simp only [CollatzResearch.WordTrace]
  refine ⟨27210715420192117211854007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140476946794744807902671 27210715420192117211854007)
  ·
    refine ⟨40816073130288175817781011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27210715420192117211854007 40816073130288175817781011)
    ·
      refine ⟨61224109695432263726671517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40816073130288175817781011 61224109695432263726671517)
      ·
        refine ⟨22959041135787098897501819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61224109695432263726671517 22959041135787098897501819)
        ·
          refine ⟨34438561703680648346252729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22959041135787098897501819 34438561703680648346252729)
          ·
            refine ⟨25828921277760486259689547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34438561703680648346252729 25828921277760486259689547)
            ·
              refine ⟨38743381916640729389534321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25828921277760486259689547 38743381916640729389534321)
              ·
                refine ⟨29057536437480547042150741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38743381916640729389534321 29057536437480547042150741)
                ·
                  refine ⟨85129501281681290162551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29057536437480547042150741 85129501281681290162551)
                  ·
                    rfl

theorem cell22_746051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_746051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746051 prefixEnd_746051 := by exact prefixLift 746051
  have htrace : WordTrace (prefixWord ++ tailWord_746051) baseStart_746051 baseEnd_746051 := by
    simpa [prefixWord, tailWord_746051, baseEnd_746051] using wordTrace_append hprefix tailTrace_746051
  have hstable : (prefixWord ++ tailWord_746051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746051).length < 2 ^ (prefixWord ++ tailWord_746051).sum := by decide
  have hdescent : baseEnd_746051 < baseStart_746051 := by decide
  rcases family_descends (prefixWord ++ tailWord_746051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746053 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_746053 : Nat := 118140960795 + 746053 * 2 ^ 59
def prefixEnd_746053 : Nat := 4983230072969 + 3 ^ 40 * 746053 * 2
def baseEnd_746053 : Nat := 255389188485916531937647

theorem tailTrace_746053 : CollatzResearch.WordTrace tailWord_746053 prefixEnd_746053 255389188485916531937647 := by
  unfold tailWord_746053
  simp only [CollatzResearch.WordTrace]
  refine ⟨27210788366184871553426813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140525577456581035617875 27210788366184871553426813)
  ·
    refine ⟨10204045637319326832535055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27210788366184871553426813 10204045637319326832535055)
    ·
      refine ⟨15306068455978990248802583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10204045637319326832535055 15306068455978990248802583)
      ·
        refine ⟨22959102683968485373203875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15306068455978990248802583 22959102683968485373203875)
        ·
          refine ⟨34438654025952728059805813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22959102683968485373203875 34438654025952728059805813)
          ·
            refine ⟨3228623814933068255606795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34438654025952728059805813 3228623814933068255606795)
            ·
              refine ⟨4842935722399602383410193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228623814933068255606795 4842935722399602383410193)
              ·
                refine ⟨3632201791799701787557645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842935722399602383410193 3632201791799701787557645)
                ·
                  refine ⟨1362075671924888170334117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3632201791799701787557645 1362075671924888170334117)
                  ·
                    refine ⟨255389188485916531937647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362075671924888170334117 255389188485916531937647)
                    ·
                      rfl

theorem cell22_746053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_746053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746053 prefixEnd_746053 := by exact prefixLift 746053
  have htrace : WordTrace (prefixWord ++ tailWord_746053) baseStart_746053 baseEnd_746053 := by
    simpa [prefixWord, tailWord_746053, baseEnd_746053] using wordTrace_append hprefix tailTrace_746053
  have hstable : (prefixWord ++ tailWord_746053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746053).length < 2 ^ (prefixWord ++ tailWord_746053).sum := by decide
  have hdescent : baseEnd_746053 < baseStart_746053 := by decide
  rcases family_descends (prefixWord ++ tailWord_746053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746068 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_746068 : Nat := 118140960795 + 746068 * 2 ^ 59
def prefixEnd_746068 : Nat := 4983230072969 + 3 ^ 40 * 746068 * 2
def baseEnd_746068 : Nat := 85131441097487164270867

theorem tailTrace_746068 : CollatzResearch.WordTrace tailWord_746068 prefixEnd_746068 85131441097487164270867 := by
  unfold tailWord_746068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605667730565264557611429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18140890307420352743481905 13605667730565264557611429)
  ·
    refine ⟨2551062699480987104552143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13605667730565264557611429 2551062699480987104552143)
    ·
      refine ⟨3826594049221480656828215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551062699480987104552143 3826594049221480656828215)
      ·
        refine ⟨5739891073832220985242323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826594049221480656828215 5739891073832220985242323)
        ·
          refine ⟨8609836610748331477863485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739891073832220985242323 8609836610748331477863485)
          ·
            refine ⟨3228688729030624304198807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8609836610748331477863485 3228688729030624304198807)
            ·
              refine ⟨4843033093545936456298211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228688729030624304198807 4843033093545936456298211)
              ·
                refine ⟨7264549640318904684447317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843033093545936456298211 7264549640318904684447317)
                ·
                  refine ⟨85131441097487164270867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7264549640318904684447317 85131441097487164270867)
                  ·
                    rfl

theorem cell22_746068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_746068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746068 prefixEnd_746068 := by exact prefixLift 746068
  have htrace : WordTrace (prefixWord ++ tailWord_746068) baseStart_746068 baseEnd_746068 := by
    simpa [prefixWord, tailWord_746068, baseEnd_746068] using wordTrace_append hprefix tailTrace_746068
  have hstable : (prefixWord ++ tailWord_746068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746068).length < 2 ^ (prefixWord ++ tailWord_746068).sum := by decide
  have hdescent : baseEnd_746068 < baseStart_746068 := by decide
  rcases family_descends (prefixWord ++ tailWord_746068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746083 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_746083 : Nat := 118140960795 + 746083 * 2 ^ 59
def prefixEnd_746083 : Nat := 4983230072969 + 3 ^ 40 * 746083 * 2
def baseEnd_746083 : Nat := 255399458099006453687555

theorem tailTrace_746083 : CollatzResearch.WordTrace tailWord_746083 prefixEnd_746083 255399458099006453687555 := by
  unfold tailWord_746083
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211882556076186677018903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18141255037384124451345935 27211882556076186677018903)
  ·
    refine ⟨40817823834114280015528355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27211882556076186677018903 40817823834114280015528355)
    ·
      refine ⟨61226735751171420023292533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40817823834114280015528355 61226735751171420023292533)
      ·
        refine ⟨5740006476672320627183675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61226735751171420023292533 5740006476672320627183675)
        ·
          refine ⟨8610009715008480940775513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5740006476672320627183675 8610009715008480940775513)
          ·
            refine ⟨6457507286256360705581635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8610009715008480940775513 6457507286256360705581635)
            ·
              refine ⟨9686260929384541058372453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457507286256360705581635 9686260929384541058372453)
              ·
                refine ⟨1816173924259601448444835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9686260929384541058372453 1816173924259601448444835)
                ·
                  refine ⟨2724260886389402172667253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816173924259601448444835 2724260886389402172667253)
                  ·
                    refine ⟨255399458099006453687555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2724260886389402172667253 255399458099006453687555)
                    ·
                      rfl

theorem cell22_746083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_746083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746083 prefixEnd_746083 := by exact prefixLift 746083
  have htrace : WordTrace (prefixWord ++ tailWord_746083) baseStart_746083 baseEnd_746083 := by
    simpa [prefixWord, tailWord_746083, baseEnd_746083] using wordTrace_append hprefix tailTrace_746083
  have hstable : (prefixWord ++ tailWord_746083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746083).length < 2 ^ (prefixWord ++ tailWord_746083).sum := by decide
  have hdescent : baseEnd_746083 < baseStart_746083 := by decide
  rcases family_descends (prefixWord ++ tailWord_746083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746102 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_746102 : Nat := 118140960795 + 746102 * 2 ^ 59
def prefixEnd_746102 : Nat := 4983230072969 + 3 ^ 40 * 746102 * 2
def baseEnd_746102 : Nat := 85135320729098912487499

theorem tailTrace_746102 : CollatzResearch.WordTrace tailWord_746102 prefixEnd_746102 85135320729098912487499 := by
  unfold tailWord_746102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700785971437959557622535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18141717028671568614640373 1700785971437959557622535)
  ·
    refine ⟨2551178957156939336433803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1700785971437959557622535 2551178957156939336433803)
    ·
      refine ⟨3826768435735409004650705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551178957156939336433803 3826768435735409004650705)
      ·
        refine ⟨2870076326801556753488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3826768435735409004650705 2870076326801556753488029)
        ·
          refine ⟨1076278622550583782558011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2870076326801556753488029 1076278622550583782558011)
          ·
            refine ⟨1614417933825875673837017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076278622550583782558011 1614417933825875673837017)
            ·
              refine ⟨1210813450369406755377763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614417933825875673837017 1210813450369406755377763)
              ·
                refine ⟨1816220175554110133066645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210813450369406755377763 1816220175554110133066645)
                ·
                  refine ⟨85135320729098912487499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1816220175554110133066645 85135320729098912487499)
                  ·
                    rfl

theorem cell22_746102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_746102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746102 prefixEnd_746102 := by exact prefixLift 746102
  have htrace : WordTrace (prefixWord ++ tailWord_746102) baseStart_746102 baseEnd_746102 := by
    simpa [prefixWord, tailWord_746102, baseEnd_746102] using wordTrace_append hprefix tailTrace_746102
  have hstable : (prefixWord ++ tailWord_746102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746102).length < 2 ^ (prefixWord ++ tailWord_746102).sum := by decide
  have hdescent : baseEnd_746102 < baseStart_746102 := by decide
  rcases family_descends (prefixWord ++ tailWord_746102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746113 : List Nat := [1, 2, 4, 2, 1, 1, 2, 9]
def baseStart_746113 : Nat := 118140960795 + 746113 * 2 ^ 59
def prefixEnd_746113 : Nat := 4983230072969 + 3 ^ 40 * 746113 * 2
def baseEnd_746113 : Nat := 28378858634677375048607

theorem tailTrace_746113 : CollatzResearch.WordTrace tailWord_746113 prefixEnd_746113 28378858634677375048607 := by
  unfold tailWord_746113
  simp only [CollatzResearch.WordTrace]
  refine ⟨27212976745967501800610993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18141984497311667867073995 27212976745967501800610993)
  ·
    refine ⟨20409732559475626350458245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27212976745967501800610993 20409732559475626350458245)
    ·
      refine ⟨3826824854901679940710921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20409732559475626350458245 3826824854901679940710921)
      ·
        refine ⟨2870118641176259955533191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3826824854901679940710921 2870118641176259955533191)
        ·
          refine ⟨4305177961764389933299787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870118641176259955533191 4305177961764389933299787)
          ·
            refine ⟨6457766942646584899949681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305177961764389933299787 6457766942646584899949681)
            ·
              refine ⟨4843325206984938674962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6457766942646584899949681 4843325206984938674962261)
              ·
                refine ⟨28378858634677375048607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4843325206984938674962261 28378858634677375048607)
                ·
                  rfl

theorem cell22_746113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 9].length) (baseStart_746113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746113 prefixEnd_746113 := by exact prefixLift 746113
  have htrace : WordTrace (prefixWord ++ tailWord_746113) baseStart_746113 baseEnd_746113 := by
    simpa [prefixWord, tailWord_746113, baseEnd_746113] using wordTrace_append hprefix tailTrace_746113
  have hstable : (prefixWord ++ tailWord_746113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746113).length < 2 ^ (prefixWord ++ tailWord_746113).sum := by decide
  have hdescent : baseEnd_746113 < baseStart_746113 := by decide
  rcases family_descends (prefixWord ++ tailWord_746113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746130 : List Nat := [3, 2, 3, 1, 2, 2, 1, 8]
def baseStart_746130 : Nat := 118140960795 + 746130 * 2 ^ 59
def prefixEnd_746130 : Nat := 4983230072969 + 3 ^ 40 * 746130 * 2
def baseEnd_746130 : Nat := 28379505239945999751379

theorem tailTrace_746130 : CollatzResearch.WordTrace tailWord_746130 prefixEnd_746130 28379505239945999751379 := by
  unfold tailWord_746130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803399196726478425994961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18142397857937275802653229 6803399196726478425994961)
  ·
    refine ⟨5102549397544858819496221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6803399196726478425994961 5102549397544858819496221)
    ·
      refine ⟨1913456024079322057311083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5102549397544858819496221 1913456024079322057311083)
      ·
        refine ⟨2870184036118983085966625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913456024079322057311083 2870184036118983085966625)
        ·
          refine ⟨2152638027089237314474969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2870184036118983085966625 2152638027089237314474969)
          ·
            refine ⟨1614478520316927985856227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152638027089237314474969 1614478520316927985856227)
            ·
              refine ⟨2421717780475391978784341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614478520316927985856227 2421717780475391978784341)
              ·
                refine ⟨28379505239945999751379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2421717780475391978784341 28379505239945999751379)
                ·
                  rfl

theorem cell22_746130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_746130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746130 prefixEnd_746130 := by exact prefixLift 746130
  have htrace : WordTrace (prefixWord ++ tailWord_746130) baseStart_746130 baseEnd_746130 := by
    simpa [prefixWord, tailWord_746130, baseEnd_746130] using wordTrace_append hprefix tailTrace_746130
  have hstable : (prefixWord ++ tailWord_746130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746130).length < 2 ^ (prefixWord ++ tailWord_746130).sum := by decide
  have hdescent : baseEnd_746130 < baseStart_746130 := by decide
  rcases family_descends (prefixWord ++ tailWord_746130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746175 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 5]
def baseStart_746175 : Nat := 118140960795 + 746175 * 2 ^ 59
def prefixEnd_746175 : Nat := 4983230072969 + 3 ^ 40 * 746175 * 2
def baseEnd_746175 : Nat := 85143650526382960129091

theorem tailTrace_746175 : CollatzResearch.WordTrace tailWord_746175 prefixEnd_746175 85143650526382960129091 := by
  unfold tailWord_746175
  simp only [CollatzResearch.WordTrace]
  refine ⟨27215238071742886389367979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18143492047828590926245319 27215238071742886389367979)
  ·
    refine ⟨40822857107614329584051969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27215238071742886389367979 40822857107614329584051969)
    ·
      refine ⟨30617142830710747188038977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40822857107614329584051969 30617142830710747188038977)
      ·
        refine ⟨22962857123033060391029233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30617142830710747188038977 22962857123033060391029233)
        ·
          refine ⟨17222142842274795293271925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22962857123033060391029233 17222142842274795293271925)
          ·
            refine ⟨1614575891463262058744243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17222142842274795293271925 1614575891463262058744243)
            ·
              refine ⟨2421863837194893088116365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614575891463262058744243 2421863837194893088116365)
              ·
                refine ⟨908198938948084908043637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2421863837194893088116365 908198938948084908043637)
                ·
                  refine ⟨85143650526382960129091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 908198938948084908043637 85143650526382960129091)
                  ·
                    rfl

theorem cell22_746175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 5].length) (baseStart_746175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746175 prefixEnd_746175 := by exact prefixLift 746175
  have htrace : WordTrace (prefixWord ++ tailWord_746175) baseStart_746175 baseEnd_746175 := by
    simpa [prefixWord, tailWord_746175, baseEnd_746175] using wordTrace_append hprefix tailTrace_746175
  have hstable : (prefixWord ++ tailWord_746175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746175).length < 2 ^ (prefixWord ++ tailWord_746175).sum := by decide
  have hdescent : baseEnd_746175 < baseStart_746175 := by decide
  rcases family_descends (prefixWord ++ tailWord_746175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746250 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_746250 : Nat := 118140960795 + 746250 * 2 ^ 59
def prefixEnd_746250 : Nat := 4983230072969 + 3 ^ 40 * 746250 * 2
def baseEnd_746250 : Nat := 255456625611873684762043

theorem tailTrace_746250 : CollatzResearch.WordTrace tailWord_746250 prefixEnd_746250 255456625611873684762043 := by
  unfold tailWord_746250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804493386617793549587051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18145315697647449465565469 6804493386617793549587051)
  ·
    refine ⟨10206740079926690324380577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6804493386617793549587051 10206740079926690324380577)
    ·
      refine ⟨7655055059945017743285433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10206740079926690324380577 7655055059945017743285433)
      ·
        refine ⟨5741291294958763307464075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7655055059945017743285433 5741291294958763307464075)
        ·
          refine ⟨8611936942438144961196113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741291294958763307464075 8611936942438144961196113)
          ·
            refine ⟨6458952706828608720897085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8611936942438144961196113 6458952706828608720897085)
            ·
              refine ⟨2422107265060728270336407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6458952706828608720897085 2422107265060728270336407)
              ·
                refine ⟨3633160897591092405504611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422107265060728270336407 3633160897591092405504611)
                ·
                  refine ⟨5449741346386638608256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633160897591092405504611 5449741346386638608256917)
                  ·
                    refine ⟨255456625611873684762043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5449741346386638608256917 255456625611873684762043)
                    ·
                      rfl

theorem cell22_746250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_746250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746250 prefixEnd_746250 := by exact prefixLift 746250
  have htrace : WordTrace (prefixWord ++ tailWord_746250) baseStart_746250 baseEnd_746250 := by
    simpa [prefixWord, tailWord_746250, baseEnd_746250] using wordTrace_append hprefix tailTrace_746250
  have hstable : (prefixWord ++ tailWord_746250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746250).length < 2 ^ (prefixWord ++ tailWord_746250).sum := by decide
  have hdescent : baseEnd_746250 < baseStart_746250 := by decide
  rcases family_descends (prefixWord ++ tailWord_746250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746314 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_746314 : Nat := 118140960795 + 746314 * 2 ^ 59
def prefixEnd_746314 : Nat := 4983230072969 + 3 ^ 40 * 746314 * 2
def baseEnd_746314 : Nat := 255478534119798851161847

theorem tailTrace_746314 : CollatzResearch.WordTrace tailWord_746314 prefixEnd_746314 255478534119798851161847 := by
  unfold tailWord_746314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805076954559828282169499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18146871878826208752451997 6805076954559828282169499)
  ·
    refine ⟨10207615431839742423254249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6805076954559828282169499 10207615431839742423254249)
    ·
      refine ⟨7655711573879806817440687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10207615431839742423254249 7655711573879806817440687)
      ·
        refine ⟨11483567360819710226161031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655711573879806817440687 11483567360819710226161031)
        ·
          refine ⟨17225351041229565339241547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11483567360819710226161031 17225351041229565339241547)
          ·
            refine ⟨25838026561844348008862321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17225351041229565339241547 25838026561844348008862321)
            ·
              refine ⟨19378519921383261006646741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25838026561844348008862321 19378519921383261006646741)
              ·
                refine ⟨454184060657420179843283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19378519921383261006646741 454184060657420179843283)
                ·
                  refine ⟨681276090986130269764925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454184060657420179843283 681276090986130269764925)
                  ·
                    refine ⟨255478534119798851161847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681276090986130269764925 255478534119798851161847)
                    ·
                      rfl

theorem cell22_746314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_746314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746314 prefixEnd_746314 := by exact prefixLift 746314
  have htrace : WordTrace (prefixWord ++ tailWord_746314) baseStart_746314 baseEnd_746314 := by
    simpa [prefixWord, tailWord_746314, baseEnd_746314] using wordTrace_append hprefix tailTrace_746314
  have hstable : (prefixWord ++ tailWord_746314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746314).length < 2 ^ (prefixWord ++ tailWord_746314).sum := by decide
  have hdescent : baseEnd_746314 < baseStart_746314 := by decide
  rcases family_descends (prefixWord ++ tailWord_746314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746344 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_746344 : Nat := 118140960795 + 746344 * 2 ^ 59
def prefixEnd_746344 : Nat := 4983230072969 + 3 ^ 40 * 746344 * 2
def baseEnd_746344 : Nat := 85162934577629590970585

theorem tailTrace_746344 : CollatzResearch.WordTrace tailWord_746344 prefixEnd_746344 85162934577629590970585 := by
  unfold tailWord_746344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610701004065314126135043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18147601338753752168180057 13610701004065314126135043)
  ·
    refine ⟨20416051506097971189202565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610701004065314126135043 20416051506097971189202565)
    ·
      refine ⟨3828009657393369597975481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20416051506097971189202565 3828009657393369597975481)
      ·
        refine ⟨2871007243045027198481611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3828009657393369597975481 2871007243045027198481611)
        ·
          refine ⟨4306510864567540797722417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871007243045027198481611 4306510864567540797722417)
          ·
            refine ⟨3229883148425655598291813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4306510864567540797722417 3229883148425655598291813)
            ·
              refine ⟨605603090329810424679715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3229883148425655598291813 605603090329810424679715)
              ·
                refine ⟨908404635494715637019573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605603090329810424679715 908404635494715637019573)
                ·
                  refine ⟨85162934577629590970585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 908404635494715637019573 85162934577629590970585)
                  ·
                    rfl

theorem cell22_746344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_746344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746344 prefixEnd_746344 := by exact prefixLift 746344
  have htrace : WordTrace (prefixWord ++ tailWord_746344) baseStart_746344 baseEnd_746344 := by
    simpa [prefixWord, tailWord_746344, baseEnd_746344] using wordTrace_append hprefix tailTrace_746344
  have hstable : (prefixWord ++ tailWord_746344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746344).length < 2 ^ (prefixWord ++ tailWord_746344).sum := by decide
  have hdescent : baseEnd_746344 < baseStart_746344 := by decide
  rcases family_descends (prefixWord ++ tailWord_746344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746355 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 6]
def baseStart_746355 : Nat := 118140960795 + 746355 * 2 ^ 59
def prefixEnd_746355 : Nat := 4983230072969 + 3 ^ 40 * 746355 * 2
def baseEnd_746355 : Nat := 85164189752562803628907

theorem tailTrace_746355 : CollatzResearch.WordTrace tailWord_746355 prefixEnd_746355 85164189752562803628907 := by
  unfold tailWord_746355
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221803211090777130920519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18147868807393851420613679 27221803211090777130920519)
  ·
    refine ⟨40832704816636165696380779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27221803211090777130920519 40832704816636165696380779)
    ·
      refine ⟨61249057224954248544571169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40832704816636165696380779 61249057224954248544571169)
      ·
        refine ⟨45936792918715686408428377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61249057224954248544571169 45936792918715686408428377)
        ·
          refine ⟨34452594689036764806321283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45936792918715686408428377 34452594689036764806321283)
          ·
            refine ⟨51678892033555147209481925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34452594689036764806321283 51678892033555147209481925)
            ·
              refine ⟨9689792256291590101777861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51678892033555147209481925 9689792256291590101777861)
              ·
                refine ⟨1816836048054673144083349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9689792256291590101777861 1816836048054673144083349)
                ·
                  refine ⟨85164189752562803628907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1816836048054673144083349 85164189752562803628907)
                  ·
                    rfl

theorem cell22_746355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_746355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746355 prefixEnd_746355 := by exact prefixLift 746355
  have htrace : WordTrace (prefixWord ++ tailWord_746355) baseStart_746355 baseEnd_746355 := by
    simpa [prefixWord, tailWord_746355, baseEnd_746355] using wordTrace_append hprefix tailTrace_746355
  have hstable : (prefixWord ++ tailWord_746355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746355).length < 2 ^ (prefixWord ++ tailWord_746355).sum := by decide
  have hdescent : baseEnd_746355 < baseStart_746355 := by decide
  rcases family_descends (prefixWord ++ tailWord_746355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746385 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_746385 : Nat := 118140960795 + 746385 * 2 ^ 59
def prefixEnd_746385 : Nat := 4983230072969 + 3 ^ 40 * 746385 * 2
def baseEnd_746385 : Nat := 255502838870778332636629

theorem tailTrace_746385 : CollatzResearch.WordTrace tailWord_746385 prefixEnd_746385 255502838870778332636629 := by
  unfold tailWord_746385
  simp only [CollatzResearch.WordTrace]
  refine ⟨27222897400982092254512609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18148598267321394836341739 27222897400982092254512609)
  ·
    refine ⟨20417173050736569190884457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27222897400982092254512609 20417173050736569190884457)
    ·
      refine ⟨15312879788052426893163343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20417173050736569190884457 15312879788052426893163343)
      ·
        refine ⟨22969319682078640339745015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15312879788052426893163343 22969319682078640339745015)
        ·
          refine ⟨34453979523117960509617523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22969319682078640339745015 34453979523117960509617523)
          ·
            refine ⟨51680969284676940764426285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34453979523117960509617523 51680969284676940764426285)
            ·
              refine ⟨19380363481753852786659857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51680969284676940764426285 19380363481753852786659857)
              ·
                refine ⟨14535272611315389589994893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19380363481753852786659857 14535272611315389589994893)
                ·
                  refine ⟨5450727229243271096248085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14535272611315389589994893 5450727229243271096248085)
                  ·
                    refine ⟨255502838870778332636629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5450727229243271096248085 255502838870778332636629)
                    ·
                      rfl

theorem cell22_746385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_746385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746385 prefixEnd_746385 := by exact prefixLift 746385
  have htrace : WordTrace (prefixWord ++ tailWord_746385) baseStart_746385 baseEnd_746385 := by
    simpa [prefixWord, tailWord_746385, baseEnd_746385] using wordTrace_append hprefix tailTrace_746385
  have hstable : (prefixWord ++ tailWord_746385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746385).length < 2 ^ (prefixWord ++ tailWord_746385).sum := by decide
  have hdescent : baseEnd_746385 < baseStart_746385 := by decide
  rcases family_descends (prefixWord ++ tailWord_746385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746389 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 4]
def baseStart_746389 : Nat := 118140960795 + 746389 * 2 ^ 59
def prefixEnd_746389 : Nat := 4983230072969 + 3 ^ 40 * 746389 * 2
def baseEnd_746389 : Nat := 85168069384174551845539

theorem tailTrace_746389 : CollatzResearch.WordTrace tailWord_746389 prefixEnd_746389 85168069384174551845539 := by
  unfold tailWord_746389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27223043292967600937658221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18148695528645067291772147 27223043292967600937658221)
  ·
    refine ⟨10208641234862850351621833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27223043292967600937658221 10208641234862850351621833)
    ·
      refine ⟨7656480926147137763716375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10208641234862850351621833 7656480926147137763716375)
      ·
        refine ⟨11484721389220706645574563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7656480926147137763716375 11484721389220706645574563)
        ·
          refine ⟨17227082083831059968361845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11484721389220706645574563 17227082083831059968361845)
          ·
            refine ⟨1615038945359161872033923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17227082083831059968361845 1615038945359161872033923)
            ·
              refine ⟨2422558418038742808050885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615038945359161872033923 2422558418038742808050885)
              ·
                refine ⟨454229703382264276509541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2422558418038742808050885 454229703382264276509541)
                ·
                  refine ⟨85168069384174551845539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454229703382264276509541 85168069384174551845539)
                  ·
                    rfl

theorem cell22_746389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_746389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746389 prefixEnd_746389 := by exact prefixLift 746389
  have htrace : WordTrace (prefixWord ++ tailWord_746389) baseStart_746389 baseEnd_746389 := by
    simpa [prefixWord, tailWord_746389, baseEnd_746389] using wordTrace_append hprefix tailTrace_746389
  have hstable : (prefixWord ++ tailWord_746389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746389).length < 2 ^ (prefixWord ++ tailWord_746389).sum := by decide
  have hdescent : baseEnd_746389 < baseStart_746389 := by decide
  rcases family_descends (prefixWord ++ tailWord_746389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746404 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_746404 : Nat := 118140960795 + 746404 * 2 ^ 59
def prefixEnd_746404 : Nat := 4983230072969 + 3 ^ 40 * 746404 * 2
def baseEnd_746404 : Nat := 255509342959068616411571

theorem tailTrace_746404 : CollatzResearch.WordTrace tailWord_746404 prefixEnd_746404 255509342959068616411571 := by
  unfold tailWord_746404
  simp only [CollatzResearch.WordTrace]
  refine ⟨13611795193956629249727133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18149060258608838999636177 13611795193956629249727133)
  ·
    refine ⟨5104423197733735968647675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13611795193956629249727133 5104423197733735968647675)
    ·
      refine ⟨7656634796600603952971513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5104423197733735968647675 7656634796600603952971513)
      ·
        refine ⟨5742476097450452964728635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7656634796600603952971513 5742476097450452964728635)
        ·
          refine ⟨8613714146175679447092953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5742476097450452964728635 8613714146175679447092953)
          ·
            refine ⟨6460285609631759585319715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8613714146175679447092953 6460285609631759585319715)
            ·
              refine ⟨9690428414447639377979573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460285609631759585319715 9690428414447639377979573)
              ·
                refine ⟨908477663854466191685585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9690428414447639377979573 908477663854466191685585)
                ·
                  refine ⟨681358247890849643764189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908477663854466191685585 681358247890849643764189)
                  ·
                    refine ⟨255509342959068616411571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681358247890849643764189 255509342959068616411571)
                    ·
                      rfl

theorem cell22_746404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_746404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746404 prefixEnd_746404 := by exact prefixLift 746404
  have htrace : WordTrace (prefixWord ++ tailWord_746404) baseStart_746404 baseEnd_746404 := by
    simpa [prefixWord, tailWord_746404, baseEnd_746404] using wordTrace_append hprefix tailTrace_746404
  have hstable : (prefixWord ++ tailWord_746404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746404).length < 2 ^ (prefixWord ++ tailWord_746404).sum := by decide
  have hdescent : baseEnd_746404 < baseStart_746404 := by decide
  rcases family_descends (prefixWord ++ tailWord_746404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746415 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_746415 : Nat := 118140960795 + 746415 * 2 ^ 59
def prefixEnd_746415 : Nat := 4983230072969 + 3 ^ 40 * 746415 * 2
def baseEnd_746415 : Nat := 255513108483868254386537

theorem tailTrace_746415 : CollatzResearch.WordTrace tailWord_746415 prefixEnd_746415 255513108483868254386537 := by
  unfold tailWord_746415
  simp only [CollatzResearch.WordTrace]
  refine ⟨27223991590873407378104699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18149327727248938252069799 27223991590873407378104699)
  ·
    refine ⟨40835987386310111067157049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27223991590873407378104699 40835987386310111067157049)
    ·
      refine ⟨30626990539732583300367787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40835987386310111067157049 30626990539732583300367787)
      ·
        refine ⟨45940485809598874950551681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30626990539732583300367787 45940485809598874950551681)
        ·
          refine ⟨34455364357199156212913761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45940485809598874950551681 34455364357199156212913761)
          ·
            refine ⟨25841523267899367159685321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34455364357199156212913761 25841523267899367159685321)
            ·
              refine ⟨19381142450924525369763991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25841523267899367159685321 19381142450924525369763991)
              ·
                refine ⟨29071713676386788054645987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19381142450924525369763991 29071713676386788054645987)
                ·
                  refine ⟨43607570514580182081968981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29071713676386788054645987 43607570514580182081968981)
                  ·
                    refine ⟨255513108483868254386537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43607570514580182081968981 255513108483868254386537)
                    ·
                      rfl

theorem cell22_746415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_746415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746415 prefixEnd_746415 := by exact prefixLift 746415
  have htrace : WordTrace (prefixWord ++ tailWord_746415) baseStart_746415 baseEnd_746415 := by
    simpa [prefixWord, tailWord_746415, baseEnd_746415] using wordTrace_append hprefix tailTrace_746415
  have hstable : (prefixWord ++ tailWord_746415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746415).length < 2 ^ (prefixWord ++ tailWord_746415).sum := by decide
  have hdescent : baseEnd_746415 < baseStart_746415 := by decide
  rcases family_descends (prefixWord ++ tailWord_746415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746449 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_746449 : Nat := 118140960795 + 746449 * 2 ^ 59
def prefixEnd_746449 : Nat := 4983230072969 + 3 ^ 40 * 746449 * 2
def baseEnd_746449 : Nat := 255524747378703499036433

theorem tailTrace_746449 : CollatzResearch.WordTrace tailWord_746449 prefixEnd_746449 255524747378703499036433 := by
  unfold tailWord_746449
  simp only [CollatzResearch.WordTrace]
  refine ⟨27225231672750231184842401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18150154448500154123228267 27225231672750231184842401)
  ·
    refine ⟨20418923754562673388631801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27225231672750231184842401 20418923754562673388631801)
    ·
      refine ⟨15314192815922005041473851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20418923754562673388631801 15314192815922005041473851)
      ·
        refine ⟨22971289223883007562210777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15314192815922005041473851 22971289223883007562210777)
        ·
          refine ⟨17228466917912255671658083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22971289223883007562210777 17228466917912255671658083)
          ·
            refine ⟨25842700376868383507487125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17228466917912255671658083 25842700376868383507487125)
            ·
              refine ⟨1211376580165705476913459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25842700376868383507487125 1211376580165705476913459)
              ·
                refine ⟨1817064870248558215370189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211376580165705476913459 1817064870248558215370189)
                ·
                  refine ⟨681399326343209330763821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1817064870248558215370189 681399326343209330763821)
                  ·
                    refine ⟨255524747378703499036433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681399326343209330763821 255524747378703499036433)
                    ·
                      rfl

theorem cell22_746449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_746449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746449 prefixEnd_746449 := by exact prefixLift 746449
  have htrace : WordTrace (prefixWord ++ tailWord_746449) baseStart_746449 baseEnd_746449 := by
    simpa [prefixWord, tailWord_746449, baseEnd_746449] using wordTrace_append hprefix tailTrace_746449
  have hstable : (prefixWord ++ tailWord_746449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746449).length < 2 ^ (prefixWord ++ tailWord_746449).sum := by decide
  have hdescent : baseEnd_746449 < baseStart_746449 := by decide
  rcases family_descends (prefixWord ++ tailWord_746449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746552 : List Nat := [2, 1, 2, 1, 5, 11]
def baseStart_746552 : Nat := 118140960795 + 746552 * 2 ^ 59
def prefixEnd_746552 : Nat := 4983230072969 + 3 ^ 40 * 746552 * 2
def baseEnd_746552 : Nat := 3155061807205500786557

theorem tailTrace_746552 : CollatzResearch.WordTrace tailWord_746552 prefixEnd_746552 3155061807205500786557 := by
  unfold tailWord_746552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614494195688539887920955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18152658927584719850561273 13614494195688539887920955)
  ·
    refine ⟨20421741293532809831881433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13614494195688539887920955 20421741293532809831881433)
    ·
      refine ⟨15316305970149607373911075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20421741293532809831881433 15316305970149607373911075)
      ·
        refine ⟨22974458955224411060866613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15316305970149607373911075 22974458955224411060866613)
        ·
          refine ⟨2153855527052288536956245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22974458955224411060866613 2153855527052288536956245)
          ·
            refine ⟨3155061807205500786557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2153855527052288536956245 3155061807205500786557)
            ·
              rfl

theorem cell22_746552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 11].length) (baseStart_746552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746552 prefixEnd_746552 := by exact prefixLift 746552
  have htrace : WordTrace (prefixWord ++ tailWord_746552) baseStart_746552 baseEnd_746552 := by
    simpa [prefixWord, tailWord_746552, baseEnd_746552] using wordTrace_append hprefix tailTrace_746552
  have hstable : (prefixWord ++ tailWord_746552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746552).length < 2 ^ (prefixWord ++ tailWord_746552).sum := by decide
  have hdescent : baseEnd_746552 < baseStart_746552 := by decide
  rcases family_descends (prefixWord ++ tailWord_746552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746554 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_746554 : Nat := 118140960795 + 746554 * 2 ^ 59
def prefixEnd_746554 : Nat := 4983230072969 + 3 ^ 40 * 746554 * 2
def baseEnd_746554 : Nat := 255560691024518225161111

theorem tailTrace_746554 : CollatzResearch.WordTrace tailWord_746554 prefixEnd_746554 255560691024518225161111 := by
  unfold tailWord_746554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807265334342458529353679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18152707558246556078276477 6807265334342458529353679)
  ·
    refine ⟨10210898001513687794030519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6807265334342458529353679 10210898001513687794030519)
    ·
      refine ⟨15316347002270531691045779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10210898001513687794030519 15316347002270531691045779)
      ·
        refine ⟨22974520503405797536568669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15316347002270531691045779 22974520503405797536568669)
        ·
          refine ⟨8615445188777174076213251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22974520503405797536568669 8615445188777174076213251)
          ·
            refine ⟨12923167783165761114319877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8615445188777174076213251 12923167783165761114319877)
            ·
              refine ⟨2423093959343580208934977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12923167783165761114319877 2423093959343580208934977)
              ·
                refine ⟨1817320469507685156701233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423093959343580208934977 1817320469507685156701233)
                ·
                  refine ⟨1362990352130763867525925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817320469507685156701233 1362990352130763867525925)
                  ·
                    refine ⟨255560691024518225161111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362990352130763867525925 255560691024518225161111)
                    ·
                      rfl

theorem cell22_746554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_746554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746554 prefixEnd_746554 := by exact prefixLift 746554
  have htrace : WordTrace (prefixWord ++ tailWord_746554) baseStart_746554 baseEnd_746554 := by
    simpa [prefixWord, tailWord_746554, baseEnd_746554] using wordTrace_append hprefix tailTrace_746554
  have hstable : (prefixWord ++ tailWord_746554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746554).length < 2 ^ (prefixWord ++ tailWord_746554).sum := by decide
  have hdescent : baseEnd_746554 < baseStart_746554 := by decide
  rcases family_descends (prefixWord ++ tailWord_746554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746556 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_746556 : Nat := 118140960795 + 746556 * 2 ^ 59
def prefixEnd_746556 : Nat := 4983230072969 + 3 ^ 40 * 746556 * 2
def baseEnd_746556 : Nat := 255561375665390886611105

theorem tailTrace_746556 : CollatzResearch.WordTrace tailWord_746556 prefixEnd_746556 255561375665390886611105 := by
  unfold tailWord_746556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614567141681294229493761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18152756188908392305991681 13614567141681294229493761)
  ·
    refine ⟨10210925356260970672120321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13614567141681294229493761 10210925356260970672120321)
    ·
      refine ⟨7658194017195728004090241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10210925356260970672120321 7658194017195728004090241)
      ·
        refine ⟨5743645512896796003067681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7658194017195728004090241 5743645512896796003067681)
        ·
          refine ⟨4307734134672597002300761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743645512896796003067681 4307734134672597002300761)
          ·
            refine ⟨3230800601004447751725571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4307734134672597002300761 3230800601004447751725571)
            ·
              refine ⟨4846200901506671627588357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230800601004447751725571 4846200901506671627588357)
              ·
                refine ⟨908662669032500930172817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4846200901506671627588357 908662669032500930172817)
                ·
                  refine ⟨681497001774375697629613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908662669032500930172817 681497001774375697629613)
                  ·
                    refine ⟨255561375665390886611105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681497001774375697629613 255561375665390886611105)
                    ·
                      rfl

theorem cell22_746556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_746556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746556 prefixEnd_746556 := by exact prefixLift 746556
  have htrace : WordTrace (prefixWord ++ tailWord_746556) baseStart_746556 baseEnd_746556 := by
    simpa [prefixWord, tailWord_746556, baseEnd_746556] using wordTrace_append hprefix tailTrace_746556
  have hstable : (prefixWord ++ tailWord_746556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746556).length < 2 ^ (prefixWord ++ tailWord_746556).sum := by decide
  have hdescent : baseEnd_746556 < baseStart_746556 := by decide
  rcases family_descends (prefixWord ++ tailWord_746556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746558 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_746558 : Nat := 118140960795 + 746558 * 2 ^ 59
def prefixEnd_746558 : Nat := 4983230072969 + 3 ^ 40 * 746558 * 2
def baseEnd_746558 : Nat := 85187353435421182687033

theorem tailTrace_746558 : CollatzResearch.WordTrace tailWord_746558 prefixEnd_746558 85187353435421182687033 := by
  unfold tailWord_746558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403650903669417850070041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18152804819570228533706885 3403650903669417850070041)
  ·
    refine ⟨2552738177752063387552531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3403650903669417850070041 2552738177752063387552531)
    ·
      refine ⟨3829107266628095081328797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552738177752063387552531 3829107266628095081328797)
      ·
        refine ⟨1435915224985535655498299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3829107266628095081328797 1435915224985535655498299)
        ·
          refine ⟨2153872837478303483247449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435915224985535655498299 2153872837478303483247449)
          ·
            refine ⟨1615404628108727612435587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153872837478303483247449 1615404628108727612435587)
            ·
              refine ⟨2423106942163091418653381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615404628108727612435587 2423106942163091418653381)
              ·
                refine ⟨454332551655579640997509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2423106942163091418653381 454332551655579640997509)
                ·
                  refine ⟨85187353435421182687033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454332551655579640997509 85187353435421182687033)
                  ·
                    rfl

theorem cell22_746558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_746558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746558 prefixEnd_746558 := by exact prefixLift 746558
  have htrace : WordTrace (prefixWord ++ tailWord_746558) baseStart_746558 baseEnd_746558 := by
    simpa [prefixWord, tailWord_746558, baseEnd_746558] using wordTrace_append hprefix tailTrace_746558
  have hstable : (prefixWord ++ tailWord_746558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746558).length < 2 ^ (prefixWord ++ tailWord_746558).sum := by decide
  have hdescent : baseEnd_746558 < baseStart_746558 := by decide
  rcases family_descends (prefixWord ++ tailWord_746558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746573 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_746573 : Nat := 118140960795 + 746573 * 2 ^ 59
def prefixEnd_746573 : Nat := 4983230072969 + 3 ^ 40 * 746573 * 2
def baseEnd_746573 : Nat := 255567195112808508936053

theorem tailTrace_746573 : CollatzResearch.WordTrace tailWord_746573 prefixEnd_746573 255567195112808508936053 := by
  unfold tailWord_746573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27229754324301000362356373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18153169549534000241570915 27229754324301000362356373)
  ·
    refine ⟨1276394733951609391985455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27229754324301000362356373 1276394733951609391985455)
    ·
      refine ⟨1914592100927414087978183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276394733951609391985455 1914592100927414087978183)
      ·
        refine ⟨2871888151391121131967275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914592100927414087978183 2871888151391121131967275)
        ·
          refine ⟨4307832227086681697950913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871888151391121131967275 4307832227086681697950913)
          ·
            refine ⟨3230874170315011273463185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4307832227086681697950913 3230874170315011273463185)
            ·
              refine ⟨2423155627736258455097389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230874170315011273463185 2423155627736258455097389)
              ·
                refine ⟨908683360401096920661521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423155627736258455097389 908683360401096920661521)
                ·
                  refine ⟨681512520300822690496141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908683360401096920661521 681512520300822690496141)
                  ·
                    refine ⟨255567195112808508936053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681512520300822690496141 255567195112808508936053)
                    ·
                      rfl

theorem cell22_746573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_746573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746573 prefixEnd_746573 := by exact prefixLift 746573
  have htrace : WordTrace (prefixWord ++ tailWord_746573) baseStart_746573 baseEnd_746573 := by
    simpa [prefixWord, tailWord_746573, baseEnd_746573] using wordTrace_append hprefix tailTrace_746573
  have hstable : (prefixWord ++ tailWord_746573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746573).length < 2 ^ (prefixWord ++ tailWord_746573).sum := by decide
  have hdescent : baseEnd_746573 < baseStart_746573 := by decide
  rcases family_descends (prefixWord ++ tailWord_746573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746661 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_746661 : Nat := 118140960795 + 746661 * 2 ^ 59
def prefixEnd_746661 : Nat := 4983230072969 + 3 ^ 40 * 746661 * 2
def baseEnd_746661 : Nat := 255597319311205612735783

theorem tailTrace_746661 : CollatzResearch.WordTrace tailWord_746661 prefixEnd_746661 255597319311205612735783 := by
  unfold tailWord_746661
  simp only [CollatzResearch.WordTrace]
  refine ⟨27232963947982191391559837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18155309298654794261039891 27232963947982191391559837)
  ·
    refine ⟨10212361480493321771834939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27232963947982191391559837 10212361480493321771834939)
    ·
      refine ⟨15318542220739982657752409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10212361480493321771834939 15318542220739982657752409)
      ·
        refine ⟨11488906665554986993314307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15318542220739982657752409 11488906665554986993314307)
        ·
          refine ⟨17233359998332480489971461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11488906665554986993314307 17233359998332480489971461)
          ·
            refine ⟨3231254999687340091869649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17233359998332480489971461 3231254999687340091869649)
            ·
              refine ⟨2423441249765505068902237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231254999687340091869649 2423441249765505068902237)
              ·
                refine ⟨908790468662064400838339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423441249765505068902237 908790468662064400838339)
                ·
                  refine ⟨1363185702993096601257509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908790468662064400838339 1363185702993096601257509)
                  ·
                    refine ⟨255597319311205612735783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1363185702993096601257509 255597319311205612735783)
                    ·
                      rfl

theorem cell22_746661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_746661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746661 prefixEnd_746661 := by exact prefixLift 746661
  have htrace : WordTrace (prefixWord ++ tailWord_746661) baseStart_746661 baseEnd_746661 := by
    simpa [prefixWord, tailWord_746661, baseEnd_746661] using wordTrace_append hprefix tailTrace_746661
  have hstable : (prefixWord ++ tailWord_746661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746661).length < 2 ^ (prefixWord ++ tailWord_746661).sum := by decide
  have hdescent : baseEnd_746661 < baseStart_746661 := by decide
  rcases family_descends (prefixWord ++ tailWord_746661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746725 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_746725 : Nat := 118140960795 + 746725 * 2 ^ 59
def prefixEnd_746725 : Nat := 4983230072969 + 3 ^ 40 * 746725 * 2
def baseEnd_746725 : Nat := 255619227819130779135587

theorem tailTrace_746725 : CollatzResearch.WordTrace tailWord_746725 prefixEnd_746725 255619227819130779135587 := by
  unfold tailWord_746725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235298219750330321889629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18156865479833553547926419 27235298219750330321889629)
  ·
    refine ⟨10213236832406373870708611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27235298219750330321889629 10213236832406373870708611)
    ·
      refine ⟨15319855248609560806062917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213236832406373870708611 15319855248609560806062917)
      ·
        refine ⟨2872472859114292651136797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15319855248609560806062917 2872472859114292651136797)
        ·
          refine ⟨1077177322167859744176299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2872472859114292651136797 1077177322167859744176299)
          ·
            refine ⟨1615765983251789616264449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077177322167859744176299 1615765983251789616264449)
            ·
              refine ⟨1211824487438842212198337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615765983251789616264449 1211824487438842212198337)
              ·
                refine ⟨908868365579131659148753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211824487438842212198337 908868365579131659148753)
                ·
                  refine ⟨681651274184348744361565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908868365579131659148753 681651274184348744361565)
                  ·
                    refine ⟨255619227819130779135587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681651274184348744361565 255619227819130779135587)
                    ·
                      rfl

theorem cell22_746725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_746725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746725 prefixEnd_746725 := by exact prefixLift 746725
  have htrace : WordTrace (prefixWord ++ tailWord_746725) baseStart_746725 baseEnd_746725 := by
    simpa [prefixWord, tailWord_746725, baseEnd_746725] using wordTrace_append hprefix tailTrace_746725
  have hstable : (prefixWord ++ tailWord_746725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746725).length < 2 ^ (prefixWord ++ tailWord_746725).sum := by decide
  have hdescent : baseEnd_746725 < baseStart_746725 := by decide
  rcases family_descends (prefixWord ++ tailWord_746725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746727 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 4]
def baseStart_746727 : Nat := 118140960795 + 746727 * 2 ^ 59
def prefixEnd_746727 : Nat := 4983230072969 + 3 ^ 40 * 746727 * 2
def baseEnd_746727 : Nat := 85206637486667813528527

theorem tailTrace_746727 : CollatzResearch.WordTrace tailWord_746727 prefixEnd_746727 85206637486667813528527 := by
  unfold tailWord_746727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235371165743084663462435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18156914110495389775641623 27235371165743084663462435)
  ·
    refine ⟨40853056748614626995193653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27235371165743084663462435 40853056748614626995193653)
    ·
      refine ⟨3829974070182621280799405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40853056748614626995193653 3829974070182621280799405)
      ·
        refine ⟨1436240276318482980299777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3829974070182621280799405 1436240276318482980299777)
        ·
          refine ⟨1077180207238862235224833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436240276318482980299777 1077180207238862235224833)
          ·
            refine ⟨807885155429146676418625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077180207238862235224833 807885155429146676418625)
            ·
              refine ⟨605913866571860007313969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807885155429146676418625 605913866571860007313969)
              ·
                refine ⟨454435399928895005485477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605913866571860007313969 454435399928895005485477)
                ·
                  refine ⟨85206637486667813528527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454435399928895005485477 85206637486667813528527)
                  ·
                    rfl

theorem cell22_746727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 4].length) (baseStart_746727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746727 prefixEnd_746727 := by exact prefixLift 746727
  have htrace : WordTrace (prefixWord ++ tailWord_746727) baseStart_746727 baseEnd_746727 := by
    simpa [prefixWord, tailWord_746727, baseEnd_746727] using wordTrace_append hprefix tailTrace_746727
  have hstable : (prefixWord ++ tailWord_746727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746727).length < 2 ^ (prefixWord ++ tailWord_746727).sum := by decide
  have hdescent : baseEnd_746727 < baseStart_746727 := by decide
  rcases family_descends (prefixWord ++ tailWord_746727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746738 : List Nat := [3, 2, 1, 3, 3, 2, 1, 7]
def baseStart_746738 : Nat := 118140960795 + 746738 * 2 ^ 59
def prefixEnd_746738 : Nat := 4983230072969 + 3 ^ 40 * 746738 * 2
def baseEnd_746738 : Nat := 28402630887200342062283

theorem tailTrace_746738 : CollatzResearch.WordTrace tailWord_746738 prefixEnd_746738 28402630887200342062283 := by
  unfold tailWord_746738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808943092175808385528217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18157181579135489028075245 6808943092175808385528217)
  ·
    refine ⟨5106707319131856289146163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6808943092175808385528217 5106707319131856289146163)
    ·
      refine ⟨7660060978697784433719245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106707319131856289146163 7660060978697784433719245)
      ·
        refine ⟨2872522867011669162644717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7660060978697784433719245 2872522867011669162644717)
        ·
          refine ⟨1077196075129375935991769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2872522867011669162644717 1077196075129375935991769)
          ·
            refine ⟨807897056347031951993827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077196075129375935991769 807897056347031951993827)
            ·
              refine ⟨1211845584520547927990741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807897056347031951993827 1211845584520547927990741)
              ·
                refine ⟨28402630887200342062283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1211845584520547927990741 28402630887200342062283)
                ·
                  rfl

theorem cell22_746738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_746738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746738 prefixEnd_746738 := by exact prefixLift 746738
  have htrace : WordTrace (prefixWord ++ tailWord_746738) baseStart_746738 baseEnd_746738 := by
    simpa [prefixWord, tailWord_746738, baseEnd_746738] using wordTrace_append hprefix tailTrace_746738
  have hstable : (prefixWord ++ tailWord_746738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746738).length < 2 ^ (prefixWord ++ tailWord_746738).sum := by decide
  have hdescent : baseEnd_746738 < baseStart_746738 := by decide
  rcases family_descends (prefixWord ++ tailWord_746738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746749 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 11]
def baseStart_746749 : Nat := 118140960795 + 746749 * 2 ^ 59
def prefixEnd_746749 : Nat := 4983230072969 + 3 ^ 40 * 746749 * 2
def baseEnd_746749 : Nat := 85209147836534238845171

theorem tailTrace_746749 : CollatzResearch.WordTrace tailWord_746749 prefixEnd_746749 85209147836534238845171 := by
  unfold tailWord_746749
  simp only [CollatzResearch.WordTrace]
  refine ⟨27236173571663382420763301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18157449047775588280508867 27236173571663382420763301)
  ·
    refine ⟨5106782544686884203893119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27236173571663382420763301 5106782544686884203893119)
    ·
      refine ⟨7660173817030326305839679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106782544686884203893119 7660173817030326305839679)
      ·
        refine ⟨11490260725545489458759519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660173817030326305839679 11490260725545489458759519)
        ·
          refine ⟨17235391088318234188139279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490260725545489458759519 17235391088318234188139279)
          ·
            refine ⟨25853086632477351282208919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17235391088318234188139279 25853086632477351282208919)
            ·
              refine ⟨38779629948716026923313379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25853086632477351282208919 38779629948716026923313379)
              ·
                refine ⟨58169444923074040384970069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38779629948716026923313379 58169444923074040384970069)
                ·
                  refine ⟨85209147836534238845171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 58169444923074040384970069 85209147836534238845171)
                  ·
                    rfl

theorem cell22_746749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_746749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746749 prefixEnd_746749 := by exact prefixLift 746749
  have htrace : WordTrace (prefixWord ++ tailWord_746749) baseStart_746749 baseEnd_746749 := by
    simpa [prefixWord, tailWord_746749, baseEnd_746749] using wordTrace_append hprefix tailTrace_746749
  have hstable : (prefixWord ++ tailWord_746749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746749).length < 2 ^ (prefixWord ++ tailWord_746749).sum := by decide
  have hdescent : baseEnd_746749 < baseStart_746749 := by decide
  rcases family_descends (prefixWord ++ tailWord_746749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746753 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_746753 : Nat := 118140960795 + 746753 * 2 ^ 59
def prefixEnd_746753 : Nat := 4983230072969 + 3 ^ 40 * 746753 * 2
def baseEnd_746753 : Nat := 255628812791348039435501

theorem tailTrace_746753 : CollatzResearch.WordTrace tailWord_746753 prefixEnd_746753 255628812791348039435501 := by
  unfold tailWord_746753
  simp only [CollatzResearch.WordTrace]
  refine ⟨27236319463648891103908913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18157546309099260735939275 27236319463648891103908913)
  ·
    refine ⟨20427239597736668327931685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27236319463648891103908913 20427239597736668327931685)
    ·
      refine ⟨3830107424575625311487191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20427239597736668327931685 3830107424575625311487191)
      ·
        refine ⟨5745161136863437967230787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830107424575625311487191 5745161136863437967230787)
        ·
          refine ⟨8617741705295156950846181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745161136863437967230787 8617741705295156950846181)
          ·
            refine ⟨1615826569742841928283659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8617741705295156950846181 1615826569742841928283659)
            ·
              refine ⟨2423739854614262892425489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615826569742841928283659 2423739854614262892425489)
              ·
                refine ⟨1817804890960697169319117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423739854614262892425489 1817804890960697169319117)
                ·
                  refine ⟨681676834110261438494669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1817804890960697169319117 681676834110261438494669)
                  ·
                    refine ⟨255628812791348039435501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681676834110261438494669 255628812791348039435501)
                    ·
                      rfl

theorem cell22_746753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_746753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746753 prefixEnd_746753 := by exact prefixLift 746753
  have htrace : WordTrace (prefixWord ++ tailWord_746753) baseStart_746753 baseEnd_746753 := by
    simpa [prefixWord, tailWord_746753, baseEnd_746753] using wordTrace_append hprefix tailTrace_746753
  have hstable : (prefixWord ++ tailWord_746753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746753).length < 2 ^ (prefixWord ++ tailWord_746753).sum := by decide
  have hdescent : baseEnd_746753 < baseStart_746753 := by decide
  rcases family_descends (prefixWord ++ tailWord_746753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746826 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_746826 : Nat := 118140960795 + 746826 * 2 ^ 59
def prefixEnd_746826 : Nat := 4983230072969 + 3 ^ 40 * 746826 * 2
def baseEnd_746826 : Nat := 255653802183200182360277

theorem tailTrace_746826 : CollatzResearch.WordTrace tailWord_746826 prefixEnd_746826 255653802183200182360277 := by
  unfold tailWord_746826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809745498096106142829083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18159321328256283047544221 6809745498096106142829083)
  ·
    refine ⟨10214618247144159214243625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6809745498096106142829083 10214618247144159214243625)
    ·
      refine ⟨7660963685358119410682719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10214618247144159214243625 7660963685358119410682719)
      ·
        refine ⟨11491445528037179116024079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660963685358119410682719 11491445528037179116024079)
        ·
          refine ⟨17237168292055768674036119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491445528037179116024079 17237168292055768674036119)
          ·
            refine ⟨25855752438083653011054179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17237168292055768674036119 25855752438083653011054179)
            ·
              refine ⟨38783628657125479516581269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25855752438083653011054179 38783628657125479516581269)
              ·
                refine ⟨1817982593302756852339747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38783628657125479516581269 1817982593302756852339747)
                ·
                  refine ⟨2726973889954135278509621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817982593302756852339747 2726973889954135278509621)
                  ·
                    refine ⟨255653802183200182360277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2726973889954135278509621 255653802183200182360277)
                    ·
                      rfl

theorem cell22_746826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_746826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746826 prefixEnd_746826 := by exact prefixLift 746826
  have htrace : WordTrace (prefixWord ++ tailWord_746826) baseStart_746826 baseEnd_746826 := by
    simpa [prefixWord, tailWord_746826, baseEnd_746826] using wordTrace_append hprefix tailTrace_746826
  have hstable : (prefixWord ++ tailWord_746826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746826).length < 2 ^ (prefixWord ++ tailWord_746826).sum := by decide
  have hdescent : baseEnd_746826 < baseStart_746826 := by decide
  rcases family_descends (prefixWord ++ tailWord_746826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746838 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_746838 : Nat := 118140960795 + 746838 * 2 ^ 59
def prefixEnd_746838 : Nat := 4983230072969 + 3 ^ 40 * 746838 * 2
def baseEnd_746838 : Nat := 255657910028436151060241

theorem tailTrace_746838 : CollatzResearch.WordTrace tailWord_746838 prefixEnd_746838 255657910028436151060241 := by
  unfold tailWord_746838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702463729271309413797073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18159613112227300413835445 1702463729271309413797073)
  ·
    refine ⟨1276847796953482060347805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702463729271309413797073 1276847796953482060347805)
    ·
      refine ⟨478817923857555772630427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1276847796953482060347805 478817923857555772630427)
      ·
        refine ⟨718226885786333658945641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478817923857555772630427 718226885786333658945641)
        ·
          refine ⟨538670164339750244209231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718226885786333658945641 538670164339750244209231)
          ·
            refine ⟨808005246509625366313847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538670164339750244209231 808005246509625366313847)
            ·
              refine ⟨1212007869764438049470771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808005246509625366313847 1212007869764438049470771)
              ·
                refine ⟨1818011804646657074206157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212007869764438049470771 1818011804646657074206157)
                ·
                  refine ⟨681754426742496402827309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1818011804646657074206157 681754426742496402827309)
                  ·
                    refine ⟨255657910028436151060241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681754426742496402827309 255657910028436151060241)
                    ·
                      rfl

theorem cell22_746838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_746838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746838 prefixEnd_746838 := by exact prefixLift 746838
  have htrace : WordTrace (prefixWord ++ tailWord_746838) baseStart_746838 baseEnd_746838 := by
    simpa [prefixWord, tailWord_746838, baseEnd_746838] using wordTrace_append hprefix tailTrace_746838
  have hstable : (prefixWord ++ tailWord_746838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746838).length < 2 ^ (prefixWord ++ tailWord_746838).sum := by decide
  have hdescent : baseEnd_746838 < baseStart_746838 := by decide
  rcases family_descends (prefixWord ++ tailWord_746838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746841 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_746841 : Nat := 118140960795 + 746841 * 2 ^ 59
def prefixEnd_746841 : Nat := 4983230072969 + 3 ^ 40 * 746841 * 2
def baseEnd_746841 : Nat := 255658936989745143235231

theorem tailTrace_746841 : CollatzResearch.WordTrace tailWord_746841 prefixEnd_746841 255658936989745143235231 := by
  unfold tailWord_746841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27239529087330082133112377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18159686058220054755408251 27239529087330082133112377)
  ·
    refine ⟨20429646815497561599834283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27239529087330082133112377 20429646815497561599834283)
    ·
      refine ⟨30644470223246342399751425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20429646815497561599834283 30644470223246342399751425)
      ·
        refine ⟨22983352667434756799813569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30644470223246342399751425 22983352667434756799813569)
        ·
          refine ⟨17237514500576067599860177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22983352667434756799813569 17237514500576067599860177)
          ·
            refine ⟨12928135875432050699895133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17237514500576067599860177 12928135875432050699895133)
            ·
              refine ⟨4848050953287019012460675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12928135875432050699895133 4848050953287019012460675)
              ·
                refine ⟨7272076429930528518691013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848050953287019012460675 7272076429930528518691013)
                ·
                  refine ⟨1363514330611974097254565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7272076429930528518691013 1363514330611974097254565)
                  ·
                    refine ⟨255658936989745143235231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1363514330611974097254565 255658936989745143235231)
                    ·
                      rfl

theorem cell22_746841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_746841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746841 prefixEnd_746841 := by exact prefixLift 746841
  have htrace : WordTrace (prefixWord ++ tailWord_746841) baseStart_746841 baseEnd_746841 := by
    simpa [prefixWord, tailWord_746841, baseEnd_746841] using wordTrace_append hprefix tailTrace_746841
  have hstable : (prefixWord ++ tailWord_746841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746841).length < 2 ^ (prefixWord ++ tailWord_746841).sum := by decide
  have hdescent : baseEnd_746841 < baseStart_746841 := by decide
  rcases family_descends (prefixWord ++ tailWord_746841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746860 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_746860 : Nat := 118140960795 + 746860 * 2 ^ 59
def prefixEnd_746860 : Nat := 4983230072969 + 3 ^ 40 * 746860 * 2
def baseEnd_746860 : Nat := 255665441078035427010173

theorem tailTrace_746860 : CollatzResearch.WordTrace tailWord_746860 prefixEnd_746860 255665441078035427010173 := by
  unfold tailWord_746860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620111037130624189027017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18160148049507498918702689 13620111037130624189027017)
  ·
    refine ⟨10215083277847968141770263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13620111037130624189027017 10215083277847968141770263)
    ·
      refine ⟨15322624916771952212655395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215083277847968141770263 15322624916771952212655395)
      ·
        refine ⟨22983937375157928318983093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15322624916771952212655395 22983937375157928318983093)
        ·
          refine ⟨2154744128921055779904665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22983937375157928318983093 2154744128921055779904665)
          ·
            refine ⟨1616058096690791834928499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2154744128921055779904665 1616058096690791834928499)
            ·
              refine ⟨2424087145036187752392749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616058096690791834928499 2424087145036187752392749)
              ·
                refine ⟨909032679388570407147281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424087145036187752392749 909032679388570407147281)
                ·
                  refine ⟨681774509541427805360461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909032679388570407147281 681774509541427805360461)
                  ·
                    refine ⟨255665441078035427010173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681774509541427805360461 255665441078035427010173)
                    ·
                      rfl

theorem cell22_746860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_746860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746860 prefixEnd_746860 := by exact prefixLift 746860
  have htrace : WordTrace (prefixWord ++ tailWord_746860) baseStart_746860 baseEnd_746860 := by
    simpa [prefixWord, tailWord_746860, baseEnd_746860] using wordTrace_append hprefix tailTrace_746860
  have hstable : (prefixWord ++ tailWord_746860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746860).length < 2 ^ (prefixWord ++ tailWord_746860).sum := by decide
  have hdescent : baseEnd_746860 < baseStart_746860 := by decide
  rcases family_descends (prefixWord ++ tailWord_746860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746901 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 7]
def baseStart_746901 : Nat := 118140960795 + 746901 * 2 ^ 59
def prefixEnd_746901 : Nat := 4983230072969 + 3 ^ 40 * 746901 * 2
def baseEnd_746901 : Nat := 85226492071974995578349

theorem tailTrace_746901 : CollatzResearch.WordTrace tailWord_746901 prefixEnd_746901 85226492071974995578349 := by
  unfold tailWord_746901
  simp only [CollatzResearch.WordTrace]
  refine ⟨27241717467112712380296557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18161144978075141586864371 27241717467112712380296557)
  ·
    refine ⟨10215644050167267142611209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27241717467112712380296557 10215644050167267142611209)
    ·
      refine ⟨7661733037625450356958407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10215644050167267142611209 7661733037625450356958407)
      ·
        refine ⟨11492599556438175535437611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7661733037625450356958407 11492599556438175535437611)
        ·
          refine ⟨17238899334657263303156417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11492599556438175535437611 17238899334657263303156417)
          ·
            refine ⟨12929174500992947477367313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17238899334657263303156417 12929174500992947477367313)
            ·
              refine ⟨9696880875744710608025485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12929174500992947477367313 9696880875744710608025485)
              ·
                refine ⟨3636330328404266478009557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9696880875744710608025485 3636330328404266478009557)
                ·
                  refine ⟨85226492071974995578349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3636330328404266478009557 85226492071974995578349)
                  ·
                    rfl

theorem cell22_746901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_746901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746901 prefixEnd_746901 := by exact prefixLift 746901
  have htrace : WordTrace (prefixWord ++ tailWord_746901) baseStart_746901 baseEnd_746901 := by
    simpa [prefixWord, tailWord_746901, baseEnd_746901] using wordTrace_append hprefix tailTrace_746901
  have hstable : (prefixWord ++ tailWord_746901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746901).length < 2 ^ (prefixWord ++ tailWord_746901).sum := by decide
  have hdescent : baseEnd_746901 < baseStart_746901 := by decide
  rcases family_descends (prefixWord ++ tailWord_746901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746961 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_746961 : Nat := 118140960795 + 746961 * 2 ^ 59
def prefixEnd_746961 : Nat := 4983230072969 + 3 ^ 40 * 746961 * 2
def baseEnd_746961 : Nat := 255700015442104830234863

theorem tailTrace_746961 : CollatzResearch.WordTrace tailWord_746961 prefixEnd_746961 255700015442104830234863 := by
  unfold tailWord_746961
  simp only [CollatzResearch.WordTrace]
  refine ⟨27243905846895342627480737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18162603897930228418320491 27243905846895342627480737)
  ·
    refine ⟨20432929385171506970610553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27243905846895342627480737 20432929385171506970610553)
    ·
      refine ⟨15324697038878630227957915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20432929385171506970610553 15324697038878630227957915)
      ·
        refine ⟨22987045558317945341936873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15324697038878630227957915 22987045558317945341936873)
        ·
          refine ⟨17240284168738459006452655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22987045558317945341936873 17240284168738459006452655)
          ·
            refine ⟨25860426253107688509678983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17240284168738459006452655 25860426253107688509678983)
            ·
              refine ⟨38790639379661532764518475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25860426253107688509678983 38790639379661532764518475)
              ·
                refine ⟨58185959069492299146777713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38790639379661532764518475 58185959069492299146777713)
                ·
                  refine ⟨43639469302119224360083285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58185959069492299146777713 43639469302119224360083285)
                  ·
                    refine ⟨255700015442104830234863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43639469302119224360083285 255700015442104830234863)
                    ·
                      rfl

theorem cell22_746961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_746961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746961 prefixEnd_746961 := by exact prefixLift 746961
  have htrace : WordTrace (prefixWord ++ tailWord_746961) baseStart_746961 baseEnd_746961 := by
    simpa [prefixWord, tailWord_746961, baseEnd_746961] using wordTrace_append hprefix tailTrace_746961
  have hstable : (prefixWord ++ tailWord_746961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746961).length < 2 ^ (prefixWord ++ tailWord_746961).sum := by decide
  have hdescent : baseEnd_746961 < baseStart_746961 := by decide
  rcases family_descends (prefixWord ++ tailWord_746961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746993 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_746993 : Nat := 118140960795 + 746993 * 2 ^ 59
def prefixEnd_746993 : Nat := 4983230072969 + 3 ^ 40 * 746993 * 2
def baseEnd_746993 : Nat := 255710969696067413434765

theorem tailTrace_746993 : CollatzResearch.WordTrace tailWord_746993 prefixEnd_746993 255710969696067413434765 := by
  unfold tailWord_746993
  simp only [CollatzResearch.WordTrace]
  refine ⟨27245072982779412092645633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18163381988519608061763755 27245072982779412092645633)
  ·
    refine ⟨20433804737084559069484225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27245072982779412092645633 20433804737084559069484225)
    ·
      refine ⟨15325353552813419302113169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20433804737084559069484225 15325353552813419302113169)
      ·
        refine ⟨11494015164610064476584877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15325353552813419302113169 11494015164610064476584877)
        ·
          refine ⟨4310255686728774178719329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11494015164610064476584877 4310255686728774178719329)
          ·
            refine ⟨3232691765046580634039497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310255686728774178719329 3232691765046580634039497)
            ·
              refine ⟨2424518823784935475529623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232691765046580634039497 2424518823784935475529623)
              ·
                refine ⟨3636778235677403213294435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424518823784935475529623 3636778235677403213294435)
                ·
                  refine ⟨5455167353516104819941653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636778235677403213294435 5455167353516104819941653)
                  ·
                    refine ⟨255710969696067413434765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5455167353516104819941653 255710969696067413434765)
                    ·
                      rfl

theorem cell22_746993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_746993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_746993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_746993 prefixEnd_746993 := by exact prefixLift 746993
  have htrace : WordTrace (prefixWord ++ tailWord_746993) baseStart_746993 baseEnd_746993 := by
    simpa [prefixWord, tailWord_746993, baseEnd_746993] using wordTrace_append hprefix tailTrace_746993
  have hstable : (prefixWord ++ tailWord_746993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746993).length < 2 ^ (prefixWord ++ tailWord_746993).sum := by decide
  have hdescent : baseEnd_746993 < baseStart_746993 := by decide
  rcases family_descends (prefixWord ++ tailWord_746993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747029 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_747029 : Nat := 118140960795 + 747029 * 2 ^ 59
def prefixEnd_747029 : Nat := 4983230072969 + 3 ^ 40 * 747029 * 2
def baseEnd_747029 : Nat := 255723293231775319534655

theorem tailTrace_747029 : CollatzResearch.WordTrace tailWord_747029 prefixEnd_747029 255723293231775319534655 := by
  unfold tailWord_747029
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246386010648990240956141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18164257340432660160637427 27246386010648990240956141)
  ·
    refine ⟨10217394753993371340358553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27246386010648990240956141 10217394753993371340358553)
    ·
      refine ⟨7663046065495028505268915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10217394753993371340358553 7663046065495028505268915)
      ·
        refine ⟨11494569098242542757903373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7663046065495028505268915 11494569098242542757903373)
        ·
          refine ⟨4310463411840953534213765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11494569098242542757903373 4310463411840953534213765)
          ·
            refine ⟨808211889720178787665081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4310463411840953534213765 808211889720178787665081)
            ·
              refine ⟨606158917290134090748811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808211889720178787665081 606158917290134090748811)
              ·
                refine ⟨909238375935201136123217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606158917290134090748811 909238375935201136123217)
                ·
                  refine ⟨681928781951400852092413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909238375935201136123217 681928781951400852092413)
                  ·
                    refine ⟨255723293231775319534655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681928781951400852092413 255723293231775319534655)
                    ·
                      rfl

theorem cell22_747029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_747029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747029 prefixEnd_747029 := by exact prefixLift 747029
  have htrace : WordTrace (prefixWord ++ tailWord_747029) baseStart_747029 baseEnd_747029 := by
    simpa [prefixWord, tailWord_747029, baseEnd_747029] using wordTrace_append hprefix tailTrace_747029
  have hstable : (prefixWord ++ tailWord_747029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747029).length < 2 ^ (prefixWord ++ tailWord_747029).sum := by decide
  have hdescent : baseEnd_747029 < baseStart_747029 := by decide
  rcases family_descends (prefixWord ++ tailWord_747029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747057 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 1, 3]
def baseStart_747057 : Nat := 118140960795 + 747057 * 2 ^ 59
def prefixEnd_747057 : Nat := 4983230072969 + 3 ^ 40 * 747057 * 2
def baseEnd_747057 : Nat := 255732878203992579834569

theorem tailTrace_747057 : CollatzResearch.WordTrace tailWord_747057 prefixEnd_747057 255732878203992579834569 := by
  unfold tailWord_747057
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247407254547551022975425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18164938169698367348650283 27247407254547551022975425)
  ·
    refine ⟨20435555440910663267231569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27247407254547551022975425 20435555440910663267231569)
    ·
      refine ⟨15326666580682997450423677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20435555440910663267231569 15326666580682997450423677)
      ·
        refine ⟨5747499967756124043908879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15326666580682997450423677 5747499967756124043908879)
        ·
          refine ⟨8621249951634186065863319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747499967756124043908879 8621249951634186065863319)
          ·
            refine ⟨12931874927451279098794979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621249951634186065863319 12931874927451279098794979)
            ·
              refine ⟨19397812391176918648192469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931874927451279098794979 19397812391176918648192469)
              ·
                refine ⟨454636227918209030817011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19397812391176918648192469 454636227918209030817011)
                ·
                  refine ⟨681954341877313546225517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454636227918209030817011 681954341877313546225517)
                  ·
                    refine ⟨255732878203992579834569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681954341877313546225517 255732878203992579834569)
                    ·
                      rfl

theorem cell22_747057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_747057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747057 prefixEnd_747057 := by exact prefixLift 747057
  have htrace : WordTrace (prefixWord ++ tailWord_747057) baseStart_747057 baseEnd_747057 := by
    simpa [prefixWord, tailWord_747057, baseEnd_747057] using wordTrace_append hprefix tailTrace_747057
  have hstable : (prefixWord ++ tailWord_747057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747057).length < 2 ^ (prefixWord ++ tailWord_747057).sum := by decide
  have hdescent : baseEnd_747057 < baseStart_747057 := by decide
  rcases family_descends (prefixWord ++ tailWord_747057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747128 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_747128 : Nat := 118140960795 + 747128 * 2 ^ 59
def prefixEnd_747128 : Nat := 4983230072969 + 3 ^ 40 * 747128 * 2
def baseEnd_747128 : Nat := 255757182954972061309351

theorem tailTrace_747128 : CollatzResearch.WordTrace tailWord_747128 prefixEnd_747128 255757182954972061309351 := by
  unfold tailWord_747128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624998418645165074405019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18166664558193553432540025 13624998418645165074405019)
  ·
    refine ⟨20437497627967747611607529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13624998418645165074405019 20437497627967747611607529)
    ·
      refine ⟨15328123220975810708705647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20437497627967747611607529 15328123220975810708705647)
      ·
        refine ⟨22992184831463716063058471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15328123220975810708705647 22992184831463716063058471)
        ·
          refine ⟨34488277247195574094587707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22992184831463716063058471 34488277247195574094587707)
          ·
            refine ⟨51732415870793361141881561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34488277247195574094587707 51732415870793361141881561)
            ·
              refine ⟨38799311903095020856411171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51732415870793361141881561 38799311903095020856411171)
              ·
                refine ⟨58198967854642531284616757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38799311903095020856411171 58198967854642531284616757)
                ·
                  refine ⟨5456153236372737307932821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58198967854642531284616757 5456153236372737307932821)
                  ·
                    refine ⟨255757182954972061309351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5456153236372737307932821 255757182954972061309351)
                    ·
                      rfl

theorem cell22_747128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_747128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747128 prefixEnd_747128 := by exact prefixLift 747128
  have htrace : WordTrace (prefixWord ++ tailWord_747128) baseStart_747128 baseEnd_747128 := by
    simpa [prefixWord, tailWord_747128, baseEnd_747128] using wordTrace_append hprefix tailTrace_747128
  have hstable : (prefixWord ++ tailWord_747128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747128).length < 2 ^ (prefixWord ++ tailWord_747128).sum := by decide
  have hdescent : baseEnd_747128 < baseStart_747128 := by decide
  rcases family_descends (prefixWord ++ tailWord_747128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747160 : List Nat := [2, 1, 2, 4, 1, 3, 1, 8]
def baseStart_747160 : Nat := 118140960795 + 747160 * 2 ^ 59
def prefixEnd_747160 : Nat := 4983230072969 + 3 ^ 40 * 747160 * 2
def baseEnd_747160 : Nat := 28418681912103849389917

theorem tailTrace_747160 : CollatzResearch.WordTrace tailWord_747160 prefixEnd_747160 28418681912103849389917 := by
  unfold tailWord_747160
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625581986587199806987467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18167442648782933075983289 13625581986587199806987467)
  ·
    refine ⟨20438372979880799710481201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13625581986587199806987467 20438372979880799710481201)
    ·
      refine ⟨15328779734910599782860901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20438372979880799710481201 15328779734910599782860901)
      ·
        refine ⟨2874146200295737459286419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15328779734910599782860901 2874146200295737459286419)
        ·
          refine ⟨4311219300443606188929629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874146200295737459286419 4311219300443606188929629)
          ·
            refine ⟨1616707237666352320848611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4311219300443606188929629 1616707237666352320848611)
            ·
              refine ⟨2425060856499528481272917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616707237666352320848611 2425060856499528481272917)
              ·
                refine ⟨28418681912103849389917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2425060856499528481272917 28418681912103849389917)
                ·
                  rfl

theorem cell22_747160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_747160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747160 prefixEnd_747160 := by exact prefixLift 747160
  have htrace : WordTrace (prefixWord ++ tailWord_747160) baseStart_747160 baseEnd_747160 := by
    simpa [prefixWord, tailWord_747160, baseEnd_747160] using wordTrace_append hprefix tailTrace_747160
  have hstable : (prefixWord ++ tailWord_747160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747160).length < 2 ^ (prefixWord ++ tailWord_747160).sum := by decide
  have hdescent : baseEnd_747160 < baseStart_747160 := by decide
  rcases family_descends (prefixWord ++ tailWord_747160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747166 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_747166 : Nat := 118140960795 + 747166 * 2 ^ 59
def prefixEnd_747166 : Nat := 4983230072969 + 3 ^ 40 * 747166 * 2
def baseEnd_747166 : Nat := 85256730377184209619745

theorem tailTrace_747166 : CollatzResearch.WordTrace tailWord_747166 prefixEnd_747166 85256730377184209619745 := by
  unfold tailWord_747166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406422851394082829836669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18167588540768441759128901 3406422851394082829836669)
  ·
    refine ⟨1277408569272781061188751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3406422851394082829836669 1277408569272781061188751)
    ·
      refine ⟨1916112853909171591783127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277408569272781061188751 1916112853909171591783127)
      ·
        refine ⟨2874169280863757387674691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916112853909171591783127 2874169280863757387674691)
        ·
          refine ⟨4311253921295636081512037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874169280863757387674691 4311253921295636081512037)
          ·
            refine ⟨808360110242931765283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4311253921295636081512037 808360110242931765283507)
            ·
              refine ⟨1212540165364397647925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808360110242931765283507 1212540165364397647925261)
              ·
                refine ⟨454702562011649117971973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1212540165364397647925261 454702562011649117971973)
                ·
                  refine ⟨85256730377184209619745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454702562011649117971973 85256730377184209619745)
                  ·
                    rfl

theorem cell22_747166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_747166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747166 prefixEnd_747166 := by exact prefixLift 747166
  have htrace : WordTrace (prefixWord ++ tailWord_747166) baseStart_747166 baseEnd_747166 := by
    simpa [prefixWord, tailWord_747166, baseEnd_747166] using wordTrace_append hprefix tailTrace_747166
  have hstable : (prefixWord ++ tailWord_747166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747166).length < 2 ^ (prefixWord ++ tailWord_747166).sum := by decide
  have hdescent : baseEnd_747166 < baseStart_747166 := by decide
  rcases family_descends (prefixWord ++ tailWord_747166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747205 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 5]
def baseStart_747205 : Nat := 118140960795 + 747205 * 2 ^ 59
def prefixEnd_747205 : Nat := 4983230072969 + 3 ^ 40 * 747205 * 2
def baseEnd_747205 : Nat := 85261180542856509044705

theorem tailTrace_747205 : CollatzResearch.WordTrace tailWord_747205 prefixEnd_747205 85261180542856509044705 := by
  unfold tailWord_747205
  simp only [CollatzResearch.WordTrace]
  refine ⟨27252805258011372299363069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18168536838674248199575379 27252805258011372299363069)
  ·
    refine ⟨10219801971754264612261151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27252805258011372299363069 10219801971754264612261151)
    ·
      refine ⟨15329702957631396918391727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10219801971754264612261151 15329702957631396918391727)
      ·
        refine ⟨22994554436447095377587591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15329702957631396918391727 22994554436447095377587591)
        ·
          refine ⟨34491831654670643066381387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22994554436447095377587591 34491831654670643066381387)
          ·
            refine ⟨51737747482005964599572081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34491831654670643066381387 51737747482005964599572081)
            ·
              refine ⟨38803310611504473449679061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51737747482005964599572081 38803310611504473449679061)
              ·
                refine ⟨909452592457136096476853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38803310611504473449679061 909452592457136096476853)
                ·
                  refine ⟨85261180542856509044705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 909452592457136096476853 85261180542856509044705)
                  ·
                    rfl

theorem cell22_747205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_747205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747205 prefixEnd_747205 := by exact prefixLift 747205
  have htrace : WordTrace (prefixWord ++ tailWord_747205) baseStart_747205 baseEnd_747205 := by
    simpa [prefixWord, tailWord_747205, baseEnd_747205] using wordTrace_append hprefix tailTrace_747205
  have hstable : (prefixWord ++ tailWord_747205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747205).length < 2 ^ (prefixWord ++ tailWord_747205).sum := by decide
  have hdescent : baseEnd_747205 < baseStart_747205 := by decide
  rcases family_descends (prefixWord ++ tailWord_747205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747295 : List Nat := [1, 1, 2, 4, 2, 1, 11]
def baseStart_747295 : Nat := 118140960795 + 747295 * 2 ^ 59
def prefixEnd_747295 : Nat := 4983230072969 + 3 ^ 40 * 747295 * 2
def baseEnd_747295 : Nat := 9474605572882936754957

theorem tailTrace_747295 : CollatzResearch.WordTrace tailWord_747295 prefixEnd_747295 9474605572882936754957 := by
  unfold tailWord_747295
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256087827685317670139339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18170725218456878446759559 27256087827685317670139339)
  ·
    refine ⟨40884131741527976505209009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27256087827685317670139339 40884131741527976505209009)
    ·
      refine ⟨30663098806145982378906757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40884131741527976505209009 30663098806145982378906757)
      ·
        refine ⟨5749331026152371696045017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30663098806145982378906757 5749331026152371696045017)
        ·
          refine ⟨4311998269614278772033763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5749331026152371696045017 4311998269614278772033763)
          ·
            refine ⟨6467997404421418158050645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311998269614278772033763 6467997404421418158050645)
            ·
              refine ⟨9474605572882936754957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6467997404421418158050645 9474605572882936754957)
              ·
                rfl

theorem cell22_747295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 11].length) (baseStart_747295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747295 prefixEnd_747295 := by exact prefixLift 747295
  have htrace : WordTrace (prefixWord ++ tailWord_747295) baseStart_747295 baseEnd_747295 := by
    simpa [prefixWord, tailWord_747295, baseEnd_747295] using wordTrace_append hprefix tailTrace_747295
  have hstable : (prefixWord ++ tailWord_747295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747295).length < 2 ^ (prefixWord ++ tailWord_747295).sum := by decide
  have hdescent : baseEnd_747295 < baseStart_747295 := by decide
  rcases family_descends (prefixWord ++ tailWord_747295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747299 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 2, 3]
def baseStart_747299 : Nat := 118140960795 + 747299 * 2 ^ 59
def prefixEnd_747299 : Nat := 4983230072969 + 3 ^ 40 * 747299 * 2
def baseEnd_747299 : Nat := 255815719749584615283827

theorem tailTrace_747299 : CollatzResearch.WordTrace tailWord_747299 prefixEnd_747299 255815719749584615283827 := by
  unfold tailWord_747299
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256233719670826353284951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18170822479780550902189967 27256233719670826353284951)
  ·
    refine ⟨40884350579506239529927427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27256233719670826353284951 40884350579506239529927427)
    ·
      refine ⟨61326525869259359294891141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40884350579506239529927427 61326525869259359294891141)
      ·
        refine ⟨11498723600486129867792089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61326525869259359294891141 11498723600486129867792089)
        ·
          refine ⟨8624042700364597400844067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11498723600486129867792089 8624042700364597400844067)
          ·
            refine ⟨12936064050546896101266101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624042700364597400844067 12936064050546896101266101)
            ·
              refine ⟨1212756004738771509493697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12936064050546896101266101 1212756004738771509493697)
              ·
                refine ⟨909567003554078632120273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212756004738771509493697 909567003554078632120273)
                ·
                  refine ⟨682175252665558974090205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909567003554078632120273 682175252665558974090205)
                  ·
                    refine ⟨255815719749584615283827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682175252665558974090205 255815719749584615283827)
                    ·
                      rfl

theorem cell22_747299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3].length) (baseStart_747299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747299 prefixEnd_747299 := by exact prefixLift 747299
  have htrace : WordTrace (prefixWord ++ tailWord_747299) baseStart_747299 baseEnd_747299 := by
    simpa [prefixWord, tailWord_747299, baseEnd_747299] using wordTrace_append hprefix tailTrace_747299
  have hstable : (prefixWord ++ tailWord_747299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747299).length < 2 ^ (prefixWord ++ tailWord_747299).sum := by decide
  have hdescent : baseEnd_747299 < baseStart_747299 := by decide
  rcases family_descends (prefixWord ++ tailWord_747299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747316 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_747316 : Nat := 118140960795 + 747316 * 2 ^ 59
def prefixEnd_747316 : Nat := 4983230072969 + 3 ^ 40 * 747316 * 2
def baseEnd_747316 : Nat := 255821539197002237608775

theorem tailTrace_747316 : CollatzResearch.WordTrace tailWord_747316 prefixEnd_747316 255821539197002237608775 := by
  unfold tailWord_747316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13628426880304619128326901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18171235840406158837769201 13628426880304619128326901)
  ·
    refine ⟨1277665020028558043280647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13628426880304619128326901 1277665020028558043280647)
    ·
      refine ⟨1916497530042837064920971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277665020028558043280647 1916497530042837064920971)
      ·
        refine ⟨2874746295064255597381457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916497530042837064920971 2874746295064255597381457)
        ·
          refine ⟨2156059721298191698036093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874746295064255597381457 2156059721298191698036093)
          ·
            refine ⟨808522395486821886763535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2156059721298191698036093 808522395486821886763535)
            ·
              refine ⟨1212783593230232830145303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808522395486821886763535 1212783593230232830145303)
              ·
                refine ⟨1819175389845349245217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212783593230232830145303 1819175389845349245217955)
                ·
                  refine ⟨2728763084768023867826933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819175389845349245217955 2728763084768023867826933)
                  ·
                    refine ⟨255821539197002237608775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2728763084768023867826933 255821539197002237608775)
                    ·
                      rfl

theorem cell22_747316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_747316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747316 prefixEnd_747316 := by exact prefixLift 747316
  have htrace : WordTrace (prefixWord ++ tailWord_747316) baseStart_747316 baseEnd_747316 := by
    simpa [prefixWord, tailWord_747316, baseEnd_747316] using wordTrace_append hprefix tailTrace_747316
  have hstable : (prefixWord ++ tailWord_747316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747316).length < 2 ^ (prefixWord ++ tailWord_747316).sum := by decide
  have hdescent : baseEnd_747316 < baseStart_747316 := by decide
  rcases family_descends (prefixWord ++ tailWord_747316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747468 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_747468 : Nat := 118140960795 + 747468 * 2 ^ 59
def prefixEnd_747468 : Nat := 4983230072969 + 3 ^ 40 * 747468 * 2
def baseEnd_747468 : Nat := 255873571903324507808309

theorem tailTrace_747468 : CollatzResearch.WordTrace tailWord_747468 prefixEnd_747468 255873571903324507808309 := by
  unfold tailWord_747468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631198828029284108093529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18174931770705712144124705 13631198828029284108093529)
  ·
    refine ⟨10223399121021963081070147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13631198828029284108093529 10223399121021963081070147)
    ·
      refine ⟨15335098681532944621605221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10223399121021963081070147 15335098681532944621605221)
      ·
        refine ⟨2875331002787427116550979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15335098681532944621605221 2875331002787427116550979)
        ·
          refine ⟨4312996504181140674826469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875331002787427116550979 4312996504181140674826469)
          ·
            refine ⟨808686844533963876529963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4312996504181140674826469 808686844533963876529963)
            ·
              refine ⟨1213030266800945814794945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808686844533963876529963 1213030266800945814794945)
              ·
                refine ⟨909772700100709361096209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213030266800945814794945 909772700100709361096209)
                ·
                  refine ⟨682329525075532020822157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909772700100709361096209 682329525075532020822157)
                  ·
                    refine ⟨255873571903324507808309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682329525075532020822157 255873571903324507808309)
                    ·
                      rfl

theorem cell22_747468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_747468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747468 prefixEnd_747468 := by exact prefixLift 747468
  have htrace : WordTrace (prefixWord ++ tailWord_747468) baseStart_747468 baseEnd_747468 := by
    simpa [prefixWord, tailWord_747468, baseEnd_747468] using wordTrace_append hprefix tailTrace_747468
  have hstable : (prefixWord ++ tailWord_747468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747468).length < 2 ^ (prefixWord ++ tailWord_747468).sum := by decide
  have hdescent : baseEnd_747468 < baseStart_747468 := by decide
  rcases family_descends (prefixWord ++ tailWord_747468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747485 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_747485 : Nat := 118140960795 + 747485 * 2 ^ 59
def prefixEnd_747485 : Nat := 4983230072969 + 3 ^ 40 * 747485 * 2
def baseEnd_747485 : Nat := 255879391350742130133257

theorem tailTrace_747485 : CollatzResearch.WordTrace tailWord_747485 prefixEnd_747485 255879391350742130133257 := by
  unfold tailWord_747485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263017696996980119555909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18175345131331320079703939 27263017696996980119555909)
  ·
    refine ⟨5111815818186933772416733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27263017696996980119555909 5111815818186933772416733)
    ·
      refine ⟨1916930931820100164656275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5111815818186933772416733 1916930931820100164656275)
      ·
        refine ⟨2875396397730150246984413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916930931820100164656275 2875396397730150246984413)
        ·
          refine ⟨1078273649148806342619155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2875396397730150246984413 1078273649148806342619155)
          ·
            refine ⟨1617410473723209513928733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078273649148806342619155 1617410473723209513928733)
            ·
              refine ⟨606528927646203567723275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617410473723209513928733 606528927646203567723275)
              ·
                refine ⟨909793391469305351584913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606528927646203567723275 909793391469305351584913)
                ·
                  refine ⟨682345043601979013688685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909793391469305351584913 682345043601979013688685)
                  ·
                    refine ⟨255879391350742130133257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682345043601979013688685 255879391350742130133257)
                    ·
                      rfl

theorem cell22_747485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_747485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747485 prefixEnd_747485 := by exact prefixLift 747485
  have htrace : WordTrace (prefixWord ++ tailWord_747485) baseStart_747485 baseEnd_747485 := by
    simpa [prefixWord, tailWord_747485, baseEnd_747485] using wordTrace_append hprefix tailTrace_747485
  have hstable : (prefixWord ++ tailWord_747485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747485).length < 2 ^ (prefixWord ++ tailWord_747485).sum := by decide
  have hdescent : baseEnd_747485 < baseStart_747485 := by decide
  rcases family_descends (prefixWord ++ tailWord_747485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747507 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_747507 : Nat := 118140960795 + 747507 * 2 ^ 59
def prefixEnd_747507 : Nat := 4983230072969 + 3 ^ 40 * 747507 * 2
def baseEnd_747507 : Nat := 255886922400341406083189

theorem tailTrace_747507 : CollatzResearch.WordTrace tailWord_747507 prefixEnd_747507 255886922400341406083189 := by
  unfold tailWord_747507
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263820102917277876856775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18175880068611518584571183 27263820102917277876856775)
  ·
    refine ⟨40895730154375916815285163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27263820102917277876856775 40895730154375916815285163)
    ·
      refine ⟨61343595231563875222927745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40895730154375916815285163 61343595231563875222927745)
      ·
        refine ⟨46007696423672906417195809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61343595231563875222927745 46007696423672906417195809)
        ·
          refine ⟨34505772317754679812896857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46007696423672906417195809 34505772317754679812896857)
          ·
            refine ⟨25879329238316009859672643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34505772317754679812896857 25879329238316009859672643)
            ·
              refine ⟨38818993857474014789508965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25879329238316009859672643 38818993857474014789508965)
              ·
                refine ⟨7278561348276377773032931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38818993857474014789508965 7278561348276377773032931)
                ·
                  refine ⟨10917842022414566659549397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278561348276377773032931 10917842022414566659549397)
                  ·
                    refine ⟨255886922400341406083189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10917842022414566659549397 255886922400341406083189)
                    ·
                      rfl

theorem cell22_747507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_747507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747507 prefixEnd_747507 := by exact prefixLift 747507
  have htrace : WordTrace (prefixWord ++ tailWord_747507) baseStart_747507 baseEnd_747507 := by
    simpa [prefixWord, tailWord_747507, baseEnd_747507] using wordTrace_append hprefix tailTrace_747507
  have hstable : (prefixWord ++ tailWord_747507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747507).length < 2 ^ (prefixWord ++ tailWord_747507).sum := by decide
  have hdescent : baseEnd_747507 < baseStart_747507 := by decide
  rcases family_descends (prefixWord ++ tailWord_747507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747513 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 1, 3]
def baseStart_747513 : Nat := 118140960795 + 747513 * 2 ^ 59
def prefixEnd_747513 : Nat := 4983230072969 + 3 ^ 40 * 747513 * 2
def baseEnd_747513 : Nat := 255888976322959390433171

theorem tailTrace_747513 : CollatzResearch.WordTrace tailWord_747513 prefixEnd_747513 255888976322959390433171 := by
  unfold tailWord_747513
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264038940895540901575193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18176025960597027267716795 27264038940895540901575193)
  ·
    refine ⟨20448029205671655676181395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27264038940895540901575193 20448029205671655676181395)
    ·
      refine ⟨30672043808507483514272093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20448029205671655676181395 30672043808507483514272093)
      ·
        refine ⟨11502016428190306317852035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30672043808507483514272093 11502016428190306317852035)
        ·
          refine ⟨17253024642285459476778053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11502016428190306317852035 17253024642285459476778053)
          ·
            refine ⟨3234942120428523651895885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17253024642285459476778053 3234942120428523651895885)
            ·
              refine ⟨1213103295160696369460957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3234942120428523651895885 1213103295160696369460957)
              ·
                refine ⟨454913735685261138547859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213103295160696369460957 454913735685261138547859)
                ·
                  refine ⟨682370603527891707821789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454913735685261138547859 682370603527891707821789)
                  ·
                    refine ⟨255888976322959390433171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682370603527891707821789 255888976322959390433171)
                    ·
                      rfl

theorem cell22_747513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_747513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747513 prefixEnd_747513 := by exact prefixLift 747513
  have htrace : WordTrace (prefixWord ++ tailWord_747513) baseStart_747513 baseEnd_747513 := by
    simpa [prefixWord, tailWord_747513, baseEnd_747513] using wordTrace_append hprefix tailTrace_747513
  have hstable : (prefixWord ++ tailWord_747513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747513).length < 2 ^ (prefixWord ++ tailWord_747513).sum := by decide
  have hdescent : baseEnd_747513 < baseStart_747513 := by decide
  rcases family_descends (prefixWord ++ tailWord_747513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747530 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_747530 : Nat := 118140960795 + 747530 * 2 ^ 59
def prefixEnd_747530 : Nat := 4983230072969 + 3 ^ 40 * 747530 * 2
def baseEnd_747530 : Nat := 255894795770377012758119

theorem tailTrace_747530 : CollatzResearch.WordTrace tailWord_747530 prefixEnd_747530 255894795770377012758119 := by
  unfold tailWord_747530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816164745458488201236011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18176439321222635203296029 6816164745458488201236011)
  ·
    refine ⟨10224247118187732301854017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6816164745458488201236011 10224247118187732301854017)
    ·
      refine ⟨7668185338640799226390513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10224247118187732301854017 7668185338640799226390513)
      ·
        refine ⟨5751139003980599419792885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7668185338640799226390513 5751139003980599419792885)
        ·
          refine ⟨539169281623181195605583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5751139003980599419792885 539169281623181195605583)
          ·
            refine ⟨808753922434771793408375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539169281623181195605583 808753922434771793408375)
            ·
              refine ⟨1213130883652157690112563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808753922434771793408375 1213130883652157690112563)
              ·
                refine ⟨1819696325478236535168845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213130883652157690112563 1819696325478236535168845)
                ·
                  refine ⟨682386122054338700688317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1819696325478236535168845 682386122054338700688317)
                  ·
                    refine ⟨255894795770377012758119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682386122054338700688317 255894795770377012758119)
                    ·
                      rfl

theorem cell22_747530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_747530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747530 prefixEnd_747530 := by exact prefixLift 747530
  have htrace : WordTrace (prefixWord ++ tailWord_747530) baseStart_747530 baseEnd_747530 := by
    simpa [prefixWord, tailWord_747530, baseEnd_747530] using wordTrace_append hprefix tailTrace_747530
  have hstable : (prefixWord ++ tailWord_747530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747530).length < 2 ^ (prefixWord ++ tailWord_747530).sum := by decide
  have hdescent : baseEnd_747530 < baseStart_747530 := by decide
  rcases family_descends (prefixWord ++ tailWord_747530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747554 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_747554 : Nat := 118140960795 + 747554 * 2 ^ 59
def prefixEnd_747554 : Nat := 4983230072969 + 3 ^ 40 * 747554 * 2
def baseEnd_747554 : Nat := 85301003820282983386015

theorem tailTrace_747554 : CollatzResearch.WordTrace tailWord_747554 prefixEnd_747554 85301003820282983386015 := by
  unfold tailWord_747554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816383583436751225954429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18177022889164669935878477 6816383583436751225954429)
  ·
    refine ⟨2556143843788781709732911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6816383583436751225954429 2556143843788781709732911)
    ·
      refine ⟨3834215765683172564599367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556143843788781709732911 3834215765683172564599367)
      ·
        refine ⟨5751323648524758846899051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834215765683172564599367 5751323648524758846899051)
        ·
          refine ⟨8626985472787138270348577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751323648524758846899051 8626985472787138270348577)
          ·
            refine ⟨6470239104590353702761433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8626985472787138270348577 6470239104590353702761433)
            ·
              refine ⟨4852679328442765277071075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470239104590353702761433 4852679328442765277071075)
              ·
                refine ⟨7279018992664147915606613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852679328442765277071075 7279018992664147915606613)
                ·
                  refine ⟨85301003820282983386015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7279018992664147915606613 85301003820282983386015)
                  ·
                    rfl

theorem cell22_747554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_747554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747554 prefixEnd_747554 := by exact prefixLift 747554
  have htrace : WordTrace (prefixWord ++ tailWord_747554) baseStart_747554 baseEnd_747554 := by
    simpa [prefixWord, tailWord_747554, baseEnd_747554] using wordTrace_append hprefix tailTrace_747554
  have hstable : (prefixWord ++ tailWord_747554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747554).length < 2 ^ (prefixWord ++ tailWord_747554).sum := by decide
  have hdescent : baseEnd_747554 < baseStart_747554 := by decide
  rcases family_descends (prefixWord ++ tailWord_747554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747569 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_747569 : Nat := 118140960795 + 747569 * 2 ^ 59
def prefixEnd_747569 : Nat := 4983230072969 + 3 ^ 40 * 747569 * 2
def baseEnd_747569 : Nat := 255908146267393911032999

theorem tailTrace_747569 : CollatzResearch.WordTrace tailWord_747569 prefixEnd_747569 255908146267393911032999 := by
  unfold tailWord_747569
  simp only [CollatzResearch.WordTrace]
  refine ⟨27266081428692662465613761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18177387619128441643742507 27266081428692662465613761)
  ·
    refine ⟨20449561071519496849210321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27266081428692662465613761 20449561071519496849210321)
    ·
      refine ⟨15337170803639622636907741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20449561071519496849210321 15337170803639622636907741)
      ·
        refine ⟨5751439051364858488840403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15337170803639622636907741 5751439051364858488840403)
        ·
          refine ⟨8627158577047287733260605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751439051364858488840403 8627158577047287733260605)
          ·
            refine ⟨3235184466392732899972727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8627158577047287733260605 3235184466392732899972727)
            ·
              refine ⟨4852776699589099349959091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235184466392732899972727 4852776699589099349959091)
              ·
                refine ⟨7279165049383649024938637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852776699589099349959091 7279165049383649024938637)
                ·
                  refine ⟨2729686893518868384351989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7279165049383649024938637 2729686893518868384351989)
                  ·
                    refine ⟨255908146267393911032999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2729686893518868384351989 255908146267393911032999)
                    ·
                      rfl

theorem cell22_747569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_747569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747569 prefixEnd_747569 := by exact prefixLift 747569
  have htrace : WordTrace (prefixWord ++ tailWord_747569) baseStart_747569 baseEnd_747569 := by
    simpa [prefixWord, tailWord_747569, baseEnd_747569] using wordTrace_append hprefix tailTrace_747569
  have hstable : (prefixWord ++ tailWord_747569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747569).length < 2 ^ (prefixWord ++ tailWord_747569).sum := by decide
  have hdescent : baseEnd_747569 < baseStart_747569 := by decide
  rcases family_descends (prefixWord ++ tailWord_747569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747616 : List Nat := [2, 1, 1, 3, 2, 4, 3, 6]
def baseStart_747616 : Nat := 118140960795 + 747616 * 2 ^ 59
def prefixEnd_747616 : Nat := 4983230072969 + 3 ^ 40 * 747616 * 2
def baseEnd_747616 : Nat := 28436026147544606123095

theorem tailTrace_747616 : CollatzResearch.WordTrace tailWord_747616 prefixEnd_747616 28436026147544606123095 := by
  unfold tailWord_747616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13633897829761194746287351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18178530439681592995049801 13633897829761194746287351)
  ·
    refine ⟨20450846744641792119431027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13633897829761194746287351 20450846744641792119431027)
    ·
      refine ⟨30676270116962688179146541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20450846744641792119431027 30676270116962688179146541)
      ·
        refine ⟨11503601293861008067179953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30676270116962688179146541 11503601293861008067179953)
        ·
          refine ⟨8627700970395756050384965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11503601293861008067179953 8627700970395756050384965)
          ·
            refine ⟨1617693931949204259447181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8627700970395756050384965 1617693931949204259447181)
            ·
              refine ⟨606635224480951597292693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617693931949204259447181 606635224480951597292693)
              ·
                refine ⟨28436026147544606123095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 606635224480951597292693 28436026147544606123095)
                ·
                  rfl

theorem cell22_747616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_747616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747616 prefixEnd_747616 := by exact prefixLift 747616
  have htrace : WordTrace (prefixWord ++ tailWord_747616) baseStart_747616 baseEnd_747616 := by
    simpa [prefixWord, tailWord_747616, baseEnd_747616] using wordTrace_append hprefix tailTrace_747616
  have hstable : (prefixWord ++ tailWord_747616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747616).length < 2 ^ (prefixWord ++ tailWord_747616).sum := by decide
  have hdescent : baseEnd_747616 < baseStart_747616 := by decide
  rcases family_descends (prefixWord ++ tailWord_747616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747618 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_747618 : Nat := 118140960795 + 747618 * 2 ^ 59
def prefixEnd_747618 : Nat := 4983230072969 + 3 ^ 40 * 747618 * 2
def baseEnd_747618 : Nat := 255924919968774116557849

theorem tailTrace_747618 : CollatzResearch.WordTrace tailWord_747618 prefixEnd_747618 255924919968774116557849 := by
  unfold tailWord_747618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816967151378785958536877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18178579070343429222765005 6816967151378785958536877)
  ·
    refine ⟨2556362681767044734451329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6816967151378785958536877 2556362681767044734451329)
    ·
      refine ⟨1917272011325283550838497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2556362681767044734451329 1917272011325283550838497)
      ·
        refine ⟨1437954008493962663128873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1917272011325283550838497 1437954008493962663128873)
        ·
          refine ⟨1078465506370471997346655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437954008493962663128873 1078465506370471997346655)
          ·
            refine ⟨1617698259555707996019983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078465506370471997346655 1617698259555707996019983)
            ·
              refine ⟨2426547389333561994029975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617698259555707996019983 2426547389333561994029975)
              ·
                refine ⟨3639821084000342991044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426547389333561994029975 3639821084000342991044963)
                ·
                  refine ⟨5459731626000514486567445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639821084000342991044963 5459731626000514486567445)
                  ·
                    refine ⟨255924919968774116557849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5459731626000514486567445 255924919968774116557849)
                    ·
                      rfl

theorem cell22_747618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_747618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747618 prefixEnd_747618 := by exact prefixLift 747618
  have htrace : WordTrace (prefixWord ++ tailWord_747618) baseStart_747618 baseEnd_747618 := by
    simpa [prefixWord, tailWord_747618, baseEnd_747618] using wordTrace_append hprefix tailTrace_747618
  have hstable : (prefixWord ++ tailWord_747618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747618).length < 2 ^ (prefixWord ++ tailWord_747618).sum := by decide
  have hdescent : baseEnd_747618 < baseStart_747618 := by decide
  rcases family_descends (prefixWord ++ tailWord_747618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747682 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_747682 : Nat := 118140960795 + 747682 * 2 ^ 59
def prefixEnd_747682 : Nat := 4983230072969 + 3 ^ 40 * 747682 * 2
def baseEnd_747682 : Nat := 255946828476699282957653

theorem tailTrace_747682 : CollatzResearch.WordTrace tailWord_747682 prefixEnd_747682 255946828476699282957653 := by
  unfold tailWord_747682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817550719320820691119325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18180135251522188509651533 6817550719320820691119325)
  ·
    refine ⟨2556581519745307759169747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6817550719320820691119325 2556581519745307759169747)
    ·
      refine ⟨3834872279617961638754621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556581519745307759169747 3834872279617961638754621)
      ·
        refine ⟨1438077104856735614532983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3834872279617961638754621 1438077104856735614532983)
        ·
          refine ⟨2157115657285103421799475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438077104856735614532983 2157115657285103421799475)
          ·
            refine ⟨3235673485927655132699213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157115657285103421799475 3235673485927655132699213)
            ·
              refine ⟨1213377557222870674762205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3235673485927655132699213 1213377557222870674762205)
              ·
                refine ⟨455016583958576503035827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213377557222870674762205 455016583958576503035827)
                ·
                  refine ⟨682524875937864754553741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455016583958576503035827 682524875937864754553741)
                  ·
                    refine ⟨255946828476699282957653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682524875937864754553741 255946828476699282957653)
                    ·
                      rfl

theorem cell22_747682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_747682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747682 prefixEnd_747682 := by exact prefixLift 747682
  have htrace : WordTrace (prefixWord ++ tailWord_747682) baseStart_747682 baseEnd_747682 := by
    simpa [prefixWord, tailWord_747682, baseEnd_747682] using wordTrace_append hprefix tailTrace_747682
  have hstable : (prefixWord ++ tailWord_747682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747682).length < 2 ^ (prefixWord ++ tailWord_747682).sum := by decide
  have hdescent : baseEnd_747682 < baseStart_747682 := by decide
  rcases family_descends (prefixWord ++ tailWord_747682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747706 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_747706 : Nat := 118140960795 + 747706 * 2 ^ 59
def prefixEnd_747706 : Nat := 4983230072969 + 3 ^ 40 * 747706 * 2
def baseEnd_747706 : Nat := 85318348055723740119193

theorem tailTrace_747706 : CollatzResearch.WordTrace tailWord_747706 prefixEnd_747706 85318348055723740119193 := by
  unfold tailWord_747706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817769557299083715837743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18180718819464223242233981 6817769557299083715837743)
  ·
    refine ⟨10226654335948625573756615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6817769557299083715837743 10226654335948625573756615)
    ·
      refine ⟨15339981503922938360634923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10226654335948625573756615 15339981503922938360634923)
      ·
        refine ⟨23009972255884407540952385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15339981503922938360634923 23009972255884407540952385)
        ·
          refine ⟨17257479191913305655714289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23009972255884407540952385 17257479191913305655714289)
          ·
            refine ⟨12943109393934979241785717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17257479191913305655714289 12943109393934979241785717)
            ·
              refine ⟨1213416505681404303917411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12943109393934979241785717 1213416505681404303917411)
              ·
                refine ⟨1820124758522106455876117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213416505681404303917411 1820124758522106455876117)
                ·
                  refine ⟨85318348055723740119193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1820124758522106455876117 85318348055723740119193)
                  ·
                    rfl

theorem cell22_747706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_747706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747706 prefixEnd_747706 := by exact prefixLift 747706
  have htrace : WordTrace (prefixWord ++ tailWord_747706) baseStart_747706 baseEnd_747706 := by
    simpa [prefixWord, tailWord_747706, baseEnd_747706] using wordTrace_append hprefix tailTrace_747706
  have hstable : (prefixWord ++ tailWord_747706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747706).length < 2 ^ (prefixWord ++ tailWord_747706).sum := by decide
  have hdescent : baseEnd_747706 < baseStart_747706 := by decide
  rcases family_descends (prefixWord ++ tailWord_747706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747721 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_747721 : Nat := 118140960795 + 747721 * 2 ^ 59
def prefixEnd_747721 : Nat := 4983230072969 + 3 ^ 40 * 747721 * 2
def baseEnd_747721 : Nat := 255960178973716181232533

theorem tailTrace_747721 : CollatzResearch.WordTrace tailWord_747721 prefixEnd_747721 255960178973716181232533 := by
  unfold tailWord_747721
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271625324141992425147017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18181083549427994950098011 27271625324141992425147017)
  ·
    refine ⟨20453718993106494318860263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27271625324141992425147017 20453718993106494318860263)
    ·
      refine ⟨30680578489659741478290395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20453718993106494318860263 30680578489659741478290395)
      ·
        refine ⟨46020867734489612217435593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30680578489659741478290395 46020867734489612217435593)
        ·
          refine ⟨34515650800867209163076695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46020867734489612217435593 34515650800867209163076695)
          ·
            refine ⟨51773476201300813744615043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34515650800867209163076695 51773476201300813744615043)
            ·
              refine ⟨77660214301951220616922565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51773476201300813744615043 77660214301951220616922565)
              ·
                refine ⟨14561290181615853865672981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77660214301951220616922565 14561290181615853865672981)
                ·
                  refine ⟨682560477263243149953421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14561290181615853865672981 682560477263243149953421)
                  ·
                    refine ⟨255960178973716181232533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682560477263243149953421 255960178973716181232533)
                    ·
                      rfl

theorem cell22_747721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_747721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747721 prefixEnd_747721 := by exact prefixLift 747721
  have htrace : WordTrace (prefixWord ++ tailWord_747721) baseStart_747721 baseEnd_747721 := by
    simpa [prefixWord, tailWord_747721, baseEnd_747721] using wordTrace_append hprefix tailTrace_747721
  have hstable : (prefixWord ++ tailWord_747721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747721).length < 2 ^ (prefixWord ++ tailWord_747721).sum := by decide
  have hdescent : baseEnd_747721 < baseStart_747721 := by decide
  rcases family_descends (prefixWord ++ tailWord_747721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747751 : List Nat := [1, 1, 5, 3, 1, 11]
def baseStart_747751 : Nat := 118140960795 + 747751 * 2 ^ 59
def prefixEnd_747751 : Nat := 4983230072969 + 3 ^ 40 * 747751 * 2
def baseEnd_747751 : Nat := 3160128994898840777561

theorem tailTrace_747751 : CollatzResearch.WordTrace tailWord_747751 prefixEnd_747751 3160128994898840777561 := by
  unfold tailWord_747751
  simp only [CollatzResearch.WordTrace]
  refine ⟨27272719514033307548739107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18181813009355538365826071 27272719514033307548739107)
  ·
    refine ⟨40909079271049961323108661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27272719514033307548739107 40909079271049961323108661)
    ·
      refine ⟨3835226181660933874041437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40909079271049961323108661 3835226181660933874041437)
      ·
        refine ⟨1438209818122850202765539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3835226181660933874041437 1438209818122850202765539)
        ·
          refine ⟨2157314727184275304148309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438209818122850202765539 2157314727184275304148309)
          ·
            refine ⟨3160128994898840777561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2157314727184275304148309 3160128994898840777561)
            ·
              rfl

theorem cell22_747751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 11].length) (baseStart_747751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747751 prefixEnd_747751 := by exact prefixLift 747751
  have htrace : WordTrace (prefixWord ++ tailWord_747751) baseStart_747751 baseEnd_747751 := by
    simpa [prefixWord, tailWord_747751, baseEnd_747751] using wordTrace_append hprefix tailTrace_747751
  have hstable : (prefixWord ++ tailWord_747751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747751).length < 2 ^ (prefixWord ++ tailWord_747751).sum := by decide
  have hdescent : baseEnd_747751 < baseStart_747751 := by decide
  rcases family_descends (prefixWord ++ tailWord_747751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747811 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_747811 : Nat := 118140960795 + 747811 * 2 ^ 59
def prefixEnd_747811 : Nat := 4983230072969 + 3 ^ 40 * 747811 * 2
def baseEnd_747811 : Nat := 255990987812985946482257

theorem tailTrace_747811 : CollatzResearch.WordTrace tailWord_747811 prefixEnd_747811 255990987812985946482257 := by
  unfold tailWord_747811
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274907893815937795923287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18183271929210625197282191 27274907893815937795923287)
  ·
    refine ⟨40912361840723906693884931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27274907893815937795923287 40912361840723906693884931)
    ·
      refine ⟨61368542761085860040827397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40912361840723906693884931 61368542761085860040827397)
      ·
        refine ⟨11506601767703598757655137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61368542761085860040827397 11506601767703598757655137)
        ·
          refine ⟨8629951325777699068241353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11506601767703598757655137 8629951325777699068241353)
          ·
            refine ⟨6472463494333274301181015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8629951325777699068241353 6472463494333274301181015)
            ·
              refine ⟨9708695241499911451771523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472463494333274301181015 9708695241499911451771523)
              ·
                refine ⟨14563042862249867177657285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708695241499911451771523 14563042862249867177657285)
                ·
                  refine ⟨2730570536671850095810741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14563042862249867177657285 2730570536671850095810741)
                  ·
                    refine ⟨255990987812985946482257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2730570536671850095810741 255990987812985946482257)
                    ·
                      rfl

theorem cell22_747811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_747811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747811 prefixEnd_747811 := by exact prefixLift 747811
  have htrace : WordTrace (prefixWord ++ tailWord_747811) baseStart_747811 baseEnd_747811 := by
    simpa [prefixWord, tailWord_747811, baseEnd_747811] using wordTrace_append hprefix tailTrace_747811
  have hstable : (prefixWord ++ tailWord_747811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747811).length < 2 ^ (prefixWord ++ tailWord_747811).sum := by decide
  have hdescent : baseEnd_747811 < baseStart_747811 := by decide
  rcases family_descends (prefixWord ++ tailWord_747811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747813 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 7]
def baseStart_747813 : Nat := 118140960795 + 747813 * 2 ^ 59
def prefixEnd_747813 : Nat := 4983230072969 + 3 ^ 40 * 747813 * 2
def baseEnd_747813 : Nat := 85330557484619535977417

theorem tailTrace_747813 : CollatzResearch.WordTrace tailWord_747813 prefixEnd_747813 85330557484619535977417 := by
  unfold tailWord_747813
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274980839808692137496093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18183320559872461424997395 27274980839808692137496093)
  ·
    refine ⟨10228117814928259551561035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27274980839808692137496093 10228117814928259551561035)
    ·
      refine ⟨15342176722392389327341553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10228117814928259551561035 15342176722392389327341553)
      ·
        refine ⟨11506632541794291995506165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15342176722392389327341553 11506632541794291995506165)
        ·
          refine ⟨1078746800793214874578703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11506632541794291995506165 1078746800793214874578703)
          ·
            refine ⟨1618120201189822311868055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078746800793214874578703 1618120201189822311868055)
            ·
              refine ⟨2427180301784733467802083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618120201189822311868055 2427180301784733467802083)
              ·
                refine ⟨3640770452677100201703125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427180301784733467802083 3640770452677100201703125)
                ·
                  refine ⟨85330557484619535977417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3640770452677100201703125 85330557484619535977417)
                  ·
                    rfl

theorem cell22_747813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_747813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747813 prefixEnd_747813 := by exact prefixLift 747813
  have htrace : WordTrace (prefixWord ++ tailWord_747813) baseStart_747813 baseEnd_747813 := by
    simpa [prefixWord, tailWord_747813, baseEnd_747813] using wordTrace_append hprefix tailTrace_747813
  have hstable : (prefixWord ++ tailWord_747813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747813).length < 2 ^ (prefixWord ++ tailWord_747813).sum := by decide
  have hdescent : baseEnd_747813 < baseStart_747813 := by decide
  rcases family_descends (prefixWord ++ tailWord_747813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747843 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 1, 4]
def baseStart_747843 : Nat := 118140960795 + 747843 * 2 ^ 59
def prefixEnd_747843 : Nat := 4983230072969 + 3 ^ 40 * 747843 * 2
def baseEnd_747843 : Nat := 256001942066948529682159

theorem tailTrace_747843 : CollatzResearch.WordTrace tailWord_747843 prefixEnd_747843 256001942066948529682159 := by
  unfold tailWord_747843
  simp only [CollatzResearch.WordTrace]
  refine ⟨27276075029700007261088183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18184050019800004840725455 27276075029700007261088183)
  ·
    refine ⟨40914112544550010891632275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27276075029700007261088183 40914112544550010891632275)
    ·
      refine ⟨61371168816825016337448413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40914112544550010891632275 61371168816825016337448413)
      ·
        refine ⟨23014188306309381126543155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61371168816825016337448413 23014188306309381126543155)
        ·
          refine ⟨34521282459464071689814733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23014188306309381126543155 34521282459464071689814733)
          ·
            refine ⟨12945480922299026883680525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34521282459464071689814733 12945480922299026883680525)
            ·
              refine ⟨4854555345862135081380197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12945480922299026883680525 4854555345862135081380197)
              ·
                refine ⟨910229127349150327758787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4854555345862135081380197 910229127349150327758787)
                ·
                  refine ⟨1365343691023725491638181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910229127349150327758787 1365343691023725491638181)
                  ·
                    refine ⟨256001942066948529682159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365343691023725491638181 256001942066948529682159)
                    ·
                      rfl

theorem cell22_747843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4].length) (baseStart_747843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747843 prefixEnd_747843 := by exact prefixLift 747843
  have htrace : WordTrace (prefixWord ++ tailWord_747843) baseStart_747843 baseEnd_747843 := by
    simpa [prefixWord, tailWord_747843, baseEnd_747843] using wordTrace_append hprefix tailTrace_747843
  have hstable : (prefixWord ++ tailWord_747843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747843).length < 2 ^ (prefixWord ++ tailWord_747843).sum := by decide
  have hdescent : baseEnd_747843 < baseStart_747843 := by decide
  rcases family_descends (prefixWord ++ tailWord_747843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747860 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_747860 : Nat := 118140960795 + 747860 * 2 ^ 59
def prefixEnd_747860 : Nat := 4983230072969 + 3 ^ 40 * 747860 * 2
def baseEnd_747860 : Nat := 256007761514366152007107

theorem tailTrace_747860 : CollatzResearch.WordTrace tailWord_747860 prefixEnd_747860 256007761514366152007107 := by
  unfold tailWord_747860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638347535319209582228517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18184463380425612776304689 13638347535319209582228517)
  ·
    refine ⟨2557190162872351796667847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13638347535319209582228517 2557190162872351796667847)
    ·
      refine ⟨3835785244308527695001771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557190162872351796667847 3835785244308527695001771)
      ·
        refine ⟨5753677866462791542502657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835785244308527695001771 5753677866462791542502657)
        ·
          refine ⟨4315258399847093656876993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5753677866462791542502657 4315258399847093656876993)
          ·
            refine ⟨3236443799885320242657745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4315258399847093656876993 3236443799885320242657745)
            ·
              refine ⟨2427332849913990181993309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236443799885320242657745 2427332849913990181993309)
              ·
                refine ⟨910249818717746318247491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427332849913990181993309 910249818717746318247491)
                ·
                  refine ⟨1365374728076619477371237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910249818717746318247491 1365374728076619477371237)
                  ·
                    refine ⟨256007761514366152007107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365374728076619477371237 256007761514366152007107)
                    ·
                      rfl

theorem cell22_747860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_747860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747860 prefixEnd_747860 := by exact prefixLift 747860
  have htrace : WordTrace (prefixWord ++ tailWord_747860) baseStart_747860 baseEnd_747860 := by
    simpa [prefixWord, tailWord_747860, baseEnd_747860] using wordTrace_append hprefix tailTrace_747860
  have hstable : (prefixWord ++ tailWord_747860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747860).length < 2 ^ (prefixWord ++ tailWord_747860).sum := by decide
  have hdescent : baseEnd_747860 < baseStart_747860 := by decide
  rcases family_descends (prefixWord ++ tailWord_747860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747905 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_747905 : Nat := 118140960795 + 747905 * 2 ^ 59
def prefixEnd_747905 : Nat := 4983230072969 + 3 ^ 40 * 747905 * 2
def baseEnd_747905 : Nat := 256023165934001034631969

theorem tailTrace_747905 : CollatzResearch.WordTrace tailWord_747905 prefixEnd_747905 256023165934001034631969 := by
  unfold tailWord_747905
  simp only [CollatzResearch.WordTrace]
  refine ⟨27278336355475391849845169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18185557570316927899896779 27278336355475391849845169)
  ·
    refine ⟨20458752266606543887383877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27278336355475391849845169 20458752266606543887383877)
    ·
      refine ⟨3836016049988726978884477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20458752266606543887383877 3836016049988726978884477)
      ·
        refine ⟨1438506018745772617081679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3836016049988726978884477 1438506018745772617081679)
        ·
          refine ⟨2157759028118658925622519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438506018745772617081679 2157759028118658925622519)
          ·
            refine ⟨3236638542177988388433779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157759028118658925622519 3236638542177988388433779)
            ·
              refine ⟨4854957813266982582650669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236638542177988388433779 4854957813266982582650669)
              ·
                refine ⟨1820609179975118468494001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4854957813266982582650669 1820609179975118468494001)
                ·
                  refine ⟨1365456884981338851370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820609179975118468494001 1365456884981338851370501)
                  ·
                    refine ⟨256023165934001034631969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365456884981338851370501 256023165934001034631969)
                    ·
                      rfl

theorem cell22_747905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_747905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747905 prefixEnd_747905 := by exact prefixLift 747905
  have htrace : WordTrace (prefixWord ++ tailWord_747905) baseStart_747905 baseEnd_747905 := by
    simpa [prefixWord, tailWord_747905, baseEnd_747905] using wordTrace_append hprefix tailTrace_747905
  have hstable : (prefixWord ++ tailWord_747905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747905).length < 2 ^ (prefixWord ++ tailWord_747905).sum := by decide
  have hdescent : baseEnd_747905 < baseStart_747905 := by decide
  rcases family_descends (prefixWord ++ tailWord_747905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747924 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_747924 : Nat := 118140960795 + 747924 * 2 ^ 59
def prefixEnd_747924 : Nat := 4983230072969 + 3 ^ 40 * 747924 * 2
def baseEnd_747924 : Nat := 256029670022291318406911

theorem tailTrace_747924 : CollatzResearch.WordTrace tailWord_747924 prefixEnd_747924 256029670022291318406911 := by
  unfold tailWord_747924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639514671203279047393413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18186019561604372063191217 13639514671203279047393413)
  ·
    refine ⟨2557409000850614821386265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13639514671203279047393413 2557409000850614821386265)
    ·
      refine ⟨1918056750637961116039699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2557409000850614821386265 1918056750637961116039699)
      ·
        refine ⟨2877085125956941674059549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918056750637961116039699 2877085125956941674059549)
        ·
          refine ⟨1078906922233853127772331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2877085125956941674059549 1078906922233853127772331)
          ·
            refine ⟨1618360383350779691658497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078906922233853127772331 1618360383350779691658497)
            ·
              refine ⟨1213770287513084768743873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618360383350779691658497 1213770287513084768743873)
              ·
                refine ⟨910327715634813576557905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213770287513084768743873 910327715634813576557905)
                ·
                  refine ⟨682745786726110182418429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910327715634813576557905 682745786726110182418429)
                  ·
                    refine ⟨256029670022291318406911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682745786726110182418429 256029670022291318406911)
                    ·
                      rfl

theorem cell22_747924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_747924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747924 prefixEnd_747924 := by exact prefixLift 747924
  have htrace : WordTrace (prefixWord ++ tailWord_747924) baseStart_747924 baseEnd_747924 := by
    simpa [prefixWord, tailWord_747924, baseEnd_747924] using wordTrace_append hprefix tailTrace_747924
  have hstable : (prefixWord ++ tailWord_747924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747924).length < 2 ^ (prefixWord ++ tailWord_747924).sum := by decide
  have hdescent : baseEnd_747924 < baseStart_747924 := by decide
  rcases family_descends (prefixWord ++ tailWord_747924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747935 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 3, 3]
def baseStart_747935 : Nat := 118140960795 + 747935 * 2 ^ 59
def prefixEnd_747935 : Nat := 4983230072969 + 3 ^ 40 * 747935 * 2
def baseEnd_747935 : Nat := 256033435547090956381877

theorem tailTrace_747935 : CollatzResearch.WordTrace tailWord_747935 prefixEnd_747935 256033435547090956381877 := by
  unfold tailWord_747935
  simp only [CollatzResearch.WordTrace]
  refine ⟨27279430545366706973437259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18186287030244471315624839 27279430545366706973437259)
  ·
    refine ⟨40919145818050060460155889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27279430545366706973437259 40919145818050060460155889)
    ·
      refine ⟨30689359363537545345116917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40919145818050060460155889 30689359363537545345116917)
      ·
        refine ⟨2877127440331644876104711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30689359363537545345116917 2877127440331644876104711)
        ·
          refine ⟨4315691160497467314157067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877127440331644876104711 4315691160497467314157067)
          ·
            refine ⟨6473536740746200971235601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315691160497467314157067 6473536740746200971235601)
            ·
              refine ⟨4855152555559650728426701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6473536740746200971235601 4855152555559650728426701)
              ·
                refine ⟨1820682208334869023160013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4855152555559650728426701 1820682208334869023160013)
                ·
                  refine ⟨682755828125575883685005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1820682208334869023160013 682755828125575883685005)
                  ·
                    refine ⟨256033435547090956381877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682755828125575883685005 256033435547090956381877)
                    ·
                      rfl

theorem cell22_747935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_747935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747935 prefixEnd_747935 := by exact prefixLift 747935
  have htrace : WordTrace (prefixWord ++ tailWord_747935) baseStart_747935 baseEnd_747935 := by
    simpa [prefixWord, tailWord_747935, baseEnd_747935] using wordTrace_append hprefix tailTrace_747935
  have hstable : (prefixWord ++ tailWord_747935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747935).length < 2 ^ (prefixWord ++ tailWord_747935).sum := by decide
  have hdescent : baseEnd_747935 < baseStart_747935 := by decide
  rcases family_descends (prefixWord ++ tailWord_747935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747937 : List Nat := [1, 2, 3, 5, 1, 2, 1, 7]
def baseStart_747937 : Nat := 118140960795 + 747937 * 2 ^ 59
def prefixEnd_747937 : Nat := 4983230072969 + 3 ^ 40 * 747937 * 2
def baseEnd_747937 : Nat := 28448235576440401981319

theorem tailTrace_747937 : CollatzResearch.WordTrace tailWord_747937 prefixEnd_747937 28448235576440401981319 := by
  unfold tailWord_747937
  simp only [CollatzResearch.WordTrace]
  refine ⟨27279503491359461315010065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18186335660906307543340043 27279503491359461315010065)
  ·
    refine ⟨20459627618519595986257549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27279503491359461315010065 20459627618519595986257549)
    ·
      refine ⟨7672360356944848494846581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20459627618519595986257549 7672360356944848494846581)
      ·
        refine ⟨719283783463579546391867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7672360356944848494846581 719283783463579546391867)
        ·
          refine ⟨1078925675195369319587801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719283783463579546391867 1078925675195369319587801)
          ·
            refine ⟨809194256396526989690851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078925675195369319587801 809194256396526989690851)
            ·
              refine ⟨1213791384594790484536277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809194256396526989690851 1213791384594790484536277)
              ·
                refine ⟨28448235576440401981319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1213791384594790484536277 28448235576440401981319)
                ·
                  rfl

theorem cell22_747937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 7].length) (baseStart_747937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747937 prefixEnd_747937 := by exact prefixLift 747937
  have htrace : WordTrace (prefixWord ++ tailWord_747937) baseStart_747937 baseEnd_747937 := by
    simpa [prefixWord, tailWord_747937, baseEnd_747937] using wordTrace_append hprefix tailTrace_747937
  have hstable : (prefixWord ++ tailWord_747937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747937).length < 2 ^ (prefixWord ++ tailWord_747937).sum := by decide
  have hdescent : baseEnd_747937 < baseStart_747937 := by decide
  rcases family_descends (prefixWord ++ tailWord_747937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747956 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_747956 : Nat := 118140960795 + 747956 * 2 ^ 59
def prefixEnd_747956 : Nat := 4983230072969 + 3 ^ 40 * 747956 * 2
def baseEnd_747956 : Nat := 256040624276253901606813

theorem tailTrace_747956 : CollatzResearch.WordTrace tailWord_747956 prefixEnd_747956 256040624276253901606813 := by
  unfold tailWord_747956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640098239145313779975861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18186797652193751706634481 13640098239145313779975861)
  ·
    refine ⟨1278759209919873166872737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13640098239145313779975861 1278759209919873166872737)
    ·
      refine ⟨959069407439904875154553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278759209919873166872737 959069407439904875154553)
      ·
        refine ⟨719302055579928656365915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959069407439904875154553 719302055579928656365915)
        ·
          refine ⟨1078953083369892984548873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719302055579928656365915 1078953083369892984548873)
          ·
            refine ⟨809214812527419738411655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078953083369892984548873 809214812527419738411655)
            ·
              refine ⟨1213822218791129607617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809214812527419738411655 1213822218791129607617483)
              ·
                refine ⟨1820733328186694411426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213822218791129607617483 1820733328186694411426225)
                ·
                  refine ⟨1365549996140020808569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820733328186694411426225 1365549996140020808569669)
                  ·
                    refine ⟨256040624276253901606813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365549996140020808569669 256040624276253901606813)
                    ·
                      rfl

theorem cell22_747956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_747956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_747956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_747956 prefixEnd_747956 := by exact prefixLift 747956
  have htrace : WordTrace (prefixWord ++ tailWord_747956) baseStart_747956 baseEnd_747956 := by
    simpa [prefixWord, tailWord_747956, baseEnd_747956] using wordTrace_append hprefix tailTrace_747956
  have hstable : (prefixWord ++ tailWord_747956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747956).length < 2 ^ (prefixWord ++ tailWord_747956).sum := by decide
  have hdescent : baseEnd_747956 < baseStart_747956 := by decide
  rcases family_descends (prefixWord ++ tailWord_747956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748010 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_748010 : Nat := 118140960795 + 748010 * 2 ^ 59
def prefixEnd_748010 : Nat := 4983230072969 + 3 ^ 40 * 748010 * 2
def baseEnd_748010 : Nat := 85353036526605253585549

theorem tailTrace_748010 : CollatzResearch.WordTrace tailWord_748010 prefixEnd_748010 85353036526605253585549 := by
  unfold tailWord_748010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820541505023748695604371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18188110680063329854944989 6820541505023748695604371)
  ·
    refine ⟨10230812257535623043406557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6820541505023748695604371 10230812257535623043406557)
    ·
      refine ⟨3836554596575858641277459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10230812257535623043406557 3836554596575858641277459)
      ·
        refine ⟨5754831894863787961916189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836554596575858641277459 5754831894863787961916189)
        ·
          refine ⟨2158061960573920485718571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5754831894863787961916189 2158061960573920485718571)
          ·
            refine ⟨3237092940860880728577857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158061960573920485718571 3237092940860880728577857)
            ·
              refine ⟨2427819705645660546433393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237092940860880728577857 2427819705645660546433393)
              ·
                refine ⟨1820864779234245409825045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427819705645660546433393 1820864779234245409825045)
                ·
                  refine ⟨85353036526605253585549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1820864779234245409825045 85353036526605253585549)
                  ·
                    rfl

theorem cell22_748010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_748010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748010 prefixEnd_748010 := by exact prefixLift 748010
  have htrace : WordTrace (prefixWord ++ tailWord_748010) baseStart_748010 baseEnd_748010 := by
    simpa [prefixWord, tailWord_748010, baseEnd_748010] using wordTrace_append hprefix tailTrace_748010
  have hstable : (prefixWord ++ tailWord_748010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748010).length < 2 ^ (prefixWord ++ tailWord_748010).sum := by decide
  have hdescent : baseEnd_748010 < baseStart_748010 := by decide
  rcases family_descends (prefixWord ++ tailWord_748010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748025 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_748025 : Nat := 118140960795 + 748025 * 2 ^ 59
def prefixEnd_748025 : Nat := 4983230072969 + 3 ^ 40 * 748025 * 2
def baseEnd_748025 : Nat := 256064244386360721631601

theorem tailTrace_748025 : CollatzResearch.WordTrace tailWord_748025 prefixEnd_748025 256064244386360721631601 := by
  unfold tailWord_748025
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282713115040652344213529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18188475410027101562809019 27282713115040652344213529)
  ·
    refine ⟨20462034836280489258160147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27282713115040652344213529 20462034836280489258160147)
    ·
      refine ⟨30693052254420733887240221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20462034836280489258160147 30693052254420733887240221)
      ·
        refine ⟨11509894595407775207715083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30693052254420733887240221 11509894595407775207715083)
        ·
          refine ⟨17264841893111662811572625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11509894595407775207715083 17264841893111662811572625)
          ·
            refine ⟨12948631419833747108679469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17264841893111662811572625 12948631419833747108679469)
            ·
              refine ⟨4855736782437655165754801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12948631419833747108679469 4855736782437655165754801)
              ·
                refine ⟨3641802586828241374316101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4855736782437655165754801 3641802586828241374316101)
                ·
                  refine ⟨682837985030295257684269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3641802586828241374316101 682837985030295257684269)
                  ·
                    refine ⟨256064244386360721631601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682837985030295257684269 256064244386360721631601)
                    ·
                      rfl

theorem cell22_748025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_748025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748025 prefixEnd_748025 := by exact prefixLift 748025
  have htrace : WordTrace (prefixWord ++ tailWord_748025) baseStart_748025 baseEnd_748025 := by
    simpa [prefixWord, tailWord_748025, baseEnd_748025] using wordTrace_append hprefix tailTrace_748025
  have hstable : (prefixWord ++ tailWord_748025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748025).length < 2 ^ (prefixWord ++ tailWord_748025).sum := by decide
  have hdescent : baseEnd_748025 < baseStart_748025 := by decide
  rcases family_descends (prefixWord ++ tailWord_748025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748042 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_748042 : Nat := 118140960795 + 748042 * 2 ^ 59
def prefixEnd_748042 : Nat := 4983230072969 + 3 ^ 40 * 748042 * 2
def baseEnd_748042 : Nat := 256070063833778343956549

theorem tailTrace_748042 : CollatzResearch.WordTrace tailWord_748042 prefixEnd_748042 256070063833778343956549 := by
  unfold tailWord_748042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820833288994766061895595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18188888770652709498388253 6820833288994766061895595)
  ·
    refine ⟨10231249933492149092843393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6820833288994766061895595 10231249933492149092843393)
    ·
      refine ⟨7673437450119111819632545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10231249933492149092843393 7673437450119111819632545)
      ·
        refine ⟨5755078087589333864724409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7673437450119111819632545 5755078087589333864724409)
        ·
          refine ⟨4316308565692000398543307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5755078087589333864724409 4316308565692000398543307)
          ·
            refine ⟨6474462848538000597814961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316308565692000398543307 6474462848538000597814961)
            ·
              refine ⟨4855847136403500448361221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6474462848538000597814961 4855847136403500448361221)
              ·
                refine ⟨910471338075656334067729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4855847136403500448361221 910471338075656334067729)
                ·
                  refine ⟨682853503556742250550797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910471338075656334067729 682853503556742250550797)
                  ·
                    refine ⟨256070063833778343956549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682853503556742250550797 256070063833778343956549)
                    ·
                      rfl

theorem cell22_748042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_748042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748042 prefixEnd_748042 := by exact prefixLift 748042
  have htrace : WordTrace (prefixWord ++ tailWord_748042) baseStart_748042 baseEnd_748042 := by
    simpa [prefixWord, tailWord_748042, baseEnd_748042] using wordTrace_append hprefix tailTrace_748042
  have hstable : (prefixWord ++ tailWord_748042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748042).length < 2 ^ (prefixWord ++ tailWord_748042).sum := by decide
  have hdescent : baseEnd_748042 < baseStart_748042 := by decide
  rcases family_descends (prefixWord ++ tailWord_748042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748044 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_748044 : Nat := 118140960795 + 748044 * 2 ^ 59
def prefixEnd_748044 : Nat := 4983230072969 + 3 ^ 40 * 748044 * 2
def baseEnd_748044 : Nat := 85356916158217001802181

theorem tailTrace_748044 : CollatzResearch.WordTrace tailWord_748044 prefixEnd_748044 85356916158217001802181 := by
  unfold tailWord_748044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641703050985909294577593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18188937401314545726103457 13641703050985909294577593)
  ·
    refine ⟨10231277288239431970933195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13641703050985909294577593 10231277288239431970933195)
    ·
      refine ⟨15346915932359147956399793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10231277288239431970933195 15346915932359147956399793)
      ·
        refine ⟨11510186949269360967299845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15346915932359147956399793 11510186949269360967299845)
        ·
          refine ⟨2158160052988005181368721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11510186949269360967299845 2158160052988005181368721)
          ·
            refine ⟨1618620039741003886026541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158160052988005181368721 1618620039741003886026541)
            ·
              refine ⟨606982514902876457259953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618620039741003886026541 606982514902876457259953)
              ·
                refine ⟨455236886177157342944965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606982514902876457259953 455236886177157342944965)
                ·
                  refine ⟨85356916158217001802181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455236886177157342944965 85356916158217001802181)
                  ·
                    rfl

theorem cell22_748044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_748044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748044 prefixEnd_748044 := by exact prefixLift 748044
  have htrace : WordTrace (prefixWord ++ tailWord_748044) baseStart_748044 baseEnd_748044 := by
    simpa [prefixWord, tailWord_748044, baseEnd_748044] using wordTrace_append hprefix tailTrace_748044
  have hstable : (prefixWord ++ tailWord_748044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748044).length < 2 ^ (prefixWord ++ tailWord_748044).sum := by decide
  have hdescent : baseEnd_748044 < baseStart_748044 := by decide
  rcases family_descends (prefixWord ++ tailWord_748044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748175 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_748175 : Nat := 118140960795 + 748175 * 2 ^ 59
def prefixEnd_748175 : Nat := 4983230072969 + 3 ^ 40 * 748175 * 2
def baseEnd_748175 : Nat := 256115592451810330381141

theorem tailTrace_748175 : CollatzResearch.WordTrace tailWord_748175 prefixEnd_748175 256115592451810330381141 := by
  unfold tailWord_748175
  simp only [CollatzResearch.WordTrace]
  refine ⟨27288184064497227962173979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18192122709664818641449319 27288184064497227962173979)
  ·
    refine ⟨40932276096745841943260969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27288184064497227962173979 40932276096745841943260969)
    ·
      refine ⟨30699207072559381457445727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40932276096745841943260969 30699207072559381457445727)
      ·
        refine ⟨46048810608839072186168591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30699207072559381457445727 46048810608839072186168591)
        ·
          refine ⟨69073215913258608279252887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46048810608839072186168591 69073215913258608279252887)
          ·
            refine ⟨103609823869887912418879331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69073215913258608279252887 103609823869887912418879331)
            ·
              refine ⟨155414735804831868628318997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103609823869887912418879331 155414735804831868628318997)
              ·
                refine ⟨7285065740851493841952453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155414735804831868628318997 7285065740851493841952453)
                ·
                  refine ⟨1365949826409655095366085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7285065740851493841952453 1365949826409655095366085)
                  ·
                    refine ⟨256115592451810330381141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365949826409655095366085 256115592451810330381141)
                    ·
                      rfl

theorem cell22_748175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_748175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748175 prefixEnd_748175 := by exact prefixLift 748175
  have htrace : WordTrace (prefixWord ++ tailWord_748175) baseStart_748175 baseEnd_748175 := by
    simpa [prefixWord, tailWord_748175, baseEnd_748175] using wordTrace_append hprefix tailTrace_748175
  have hstable : (prefixWord ++ tailWord_748175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748175).length < 2 ^ (prefixWord ++ tailWord_748175).sum := by decide
  have hdescent : baseEnd_748175 < baseStart_748175 := by decide
  rcases family_descends (prefixWord ++ tailWord_748175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748228 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_748228 : Nat := 118140960795 + 748228 * 2 ^ 59
def prefixEnd_748228 : Nat := 4983230072969 + 3 ^ 40 * 748228 * 2
def baseEnd_748228 : Nat := 256133735434935858805979

theorem tailTrace_748228 : CollatzResearch.WordTrace tailWord_748228 prefixEnd_748228 256133735434935858805979 := by
  unfold tailWord_748228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645058566652609006926669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18193411422203478675902225 13645058566652609006926669)
  ·
    refine ⟨5116896962494728377597501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13645058566652609006926669 5116896962494728377597501)
    ·
      refine ⟨1918836360935523141599063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5116896962494728377597501 1918836360935523141599063)
      ·
        refine ⟨2878254541403284712398595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918836360935523141599063 2878254541403284712398595)
        ·
          refine ⟨4317381812104927068597893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878254541403284712398595 4317381812104927068597893)
          ·
            refine ⟨809509089769673825362105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4317381812104927068597893 809509089769673825362105)
            ·
              refine ⟨607131817327255369021579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809509089769673825362105 607131817327255369021579)
              ·
                refine ⟨910697725990883053532369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607131817327255369021579 910697725990883053532369)
                ·
                  refine ⟨683023294493162290149277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910697725990883053532369 683023294493162290149277)
                  ·
                    refine ⟨256133735434935858805979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683023294493162290149277 256133735434935858805979)
                    ·
                      rfl

theorem cell22_748228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_748228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748228 prefixEnd_748228 := by exact prefixLift 748228
  have htrace : WordTrace (prefixWord ++ tailWord_748228) baseStart_748228 baseEnd_748228 := by
    simpa [prefixWord, tailWord_748228, baseEnd_748228] using wordTrace_append hprefix tailTrace_748228
  have hstable : (prefixWord ++ tailWord_748228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748228).length < 2 ^ (prefixWord ++ tailWord_748228).sum := by decide
  have hdescent : baseEnd_748228 < baseStart_748228 := by decide
  rcases family_descends (prefixWord ++ tailWord_748228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748269 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 5]
def baseStart_748269 : Nat := 118140960795 + 748269 * 2 ^ 59
def prefixEnd_748269 : Nat := 4983230072969 + 3 ^ 40 * 748269 * 2
def baseEnd_748269 : Nat := 85382590190941806176951

theorem tailTrace_748269 : CollatzResearch.WordTrace tailWord_748269 prefixEnd_748269 85382590190941806176951 := by
  unfold tailWord_748269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27291612526156682016095861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18194408350771121344063907 27291612526156682016095861)
  ·
    refine ⟨2558588674327188939008987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27291612526156682016095861 2558588674327188939008987)
    ·
      refine ⟨3837883011490783408513481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558588674327188939008987 3837883011490783408513481)
      ·
        refine ⟨2878412258618087556385111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3837883011490783408513481 2878412258618087556385111)
        ·
          refine ⟨4317618387927131334577667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878412258618087556385111 4317618387927131334577667)
          ·
            refine ⟨6476427581890697001866501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317618387927131334577667 6476427581890697001866501)
            ·
              refine ⟨1214330171604505687849969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6476427581890697001866501 1214330171604505687849969)
              ·
                refine ⟨910747628703379265887477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214330171604505687849969 910747628703379265887477)
                ·
                  refine ⟨85382590190941806176951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 910747628703379265887477 85382590190941806176951)
                  ·
                    rfl

theorem cell22_748269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_748269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748269 prefixEnd_748269 := by exact prefixLift 748269
  have htrace : WordTrace (prefixWord ++ tailWord_748269) baseStart_748269 baseEnd_748269 := by
    simpa [prefixWord, tailWord_748269, baseEnd_748269] using wordTrace_append hprefix tailTrace_748269
  have hstable : (prefixWord ++ tailWord_748269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748269).length < 2 ^ (prefixWord ++ tailWord_748269).sum := by decide
  have hdescent : baseEnd_748269 < baseStart_748269 := by decide
  rcases family_descends (prefixWord ++ tailWord_748269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748282 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_748282 : Nat := 118140960795 + 748282 * 2 ^ 59
def prefixEnd_748282 : Nat := 4983230072969 + 3 ^ 40 * 748282 * 2
def baseEnd_748282 : Nat := 256152220738497717955813

theorem tailTrace_748282 : CollatzResearch.WordTrace tailWord_748282 prefixEnd_748282 256152220738497717955813 := by
  unfold tailWord_748282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823021668777396309079775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18194724450073056824212733 6823021668777396309079775)
  ·
    refine ⟨10234532503166094463619663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6823021668777396309079775 10234532503166094463619663)
    ·
      refine ⟨15351798754749141695429495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10234532503166094463619663 15351798754749141695429495)
      ·
        refine ⟨23027698132123712543144243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15351798754749141695429495 23027698132123712543144243)
        ·
          refine ⟨34541547198185568814716365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23027698132123712543144243 34541547198185568814716365)
          ·
            refine ⟨12953080199319588305518637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34541547198185568814716365 12953080199319588305518637)
            ·
              refine ⟨4857405074744845614569489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12953080199319588305518637 4857405074744845614569489)
              ·
                refine ⟨3643053806058634210927117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4857405074744845614569489 3643053806058634210927117)
                ·
                  refine ⟨1366145177271987829097669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3643053806058634210927117 1366145177271987829097669)
                  ·
                    refine ⟨256152220738497717955813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366145177271987829097669 256152220738497717955813)
                    ·
                      rfl

theorem cell22_748282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_748282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748282 prefixEnd_748282 := by exact prefixLift 748282
  have htrace : WordTrace (prefixWord ++ tailWord_748282) baseStart_748282 baseEnd_748282 := by
    simpa [prefixWord, tailWord_748282, baseEnd_748282] using wordTrace_append hprefix tailTrace_748282
  have hstable : (prefixWord ++ tailWord_748282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748282).length < 2 ^ (prefixWord ++ tailWord_748282).sum := by decide
  have hdescent : baseEnd_748282 < baseStart_748282 := by decide
  rcases family_descends (prefixWord ++ tailWord_748282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748316 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_748316 : Nat := 118140960795 + 748316 * 2 ^ 59
def prefixEnd_748316 : Nat := 4983230072969 + 3 ^ 40 * 748316 * 2
def baseEnd_748316 : Nat := 256163859633332962605709

theorem tailTrace_748316 : CollatzResearch.WordTrace tailWord_748316 prefixEnd_748316 256163859633332962605709 := by
  unfold tailWord_748316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646663378493204521528401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18195551171324272695371201 13646663378493204521528401)
  ·
    refine ⟨10234997533869903391146301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13646663378493204521528401 10234997533869903391146301)
    ·
      refine ⟨3838124075201213771679863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10234997533869903391146301 3838124075201213771679863)
      ·
        refine ⟨5757186112801820657519795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838124075201213771679863 5757186112801820657519795)
        ·
          refine ⟨8635779169202730986279693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757186112801820657519795 8635779169202730986279693)
          ·
            refine ⟨3238417188451024119854885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8635779169202730986279693 3238417188451024119854885)
            ·
              refine ⟨607203222834567022472791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3238417188451024119854885 607203222834567022472791)
              ·
                refine ⟨910804834251850533709187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607203222834567022472791 910804834251850533709187)
                ·
                  refine ⟨1366207251377775800563781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910804834251850533709187 1366207251377775800563781)
                  ·
                    refine ⟨256163859633332962605709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366207251377775800563781 256163859633332962605709)
                    ·
                      rfl

theorem cell22_748316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_748316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748316 prefixEnd_748316 := by exact prefixLift 748316
  have htrace : WordTrace (prefixWord ++ tailWord_748316) baseStart_748316 baseEnd_748316 := by
    simpa [prefixWord, tailWord_748316, baseEnd_748316] using wordTrace_append hprefix tailTrace_748316
  have hstable : (prefixWord ++ tailWord_748316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748316).length < 2 ^ (prefixWord ++ tailWord_748316).sum := by decide
  have hdescent : baseEnd_748316 < baseStart_748316 := by decide
  rcases family_descends (prefixWord ++ tailWord_748316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748346 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_748346 : Nat := 118140960795 + 748346 * 2 ^ 59
def prefixEnd_748346 : Nat := 4983230072969 + 3 ^ 40 * 748346 * 2
def baseEnd_748346 : Nat := 256174129246422884355617

theorem tailTrace_748346 : CollatzResearch.WordTrace tailWord_748346 prefixEnd_748346 256174129246422884355617 := by
  unfold tailWord_748346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823605236719431041662223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18196280631251816111099261 6823605236719431041662223)
  ·
    refine ⟨10235407855079146562493335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6823605236719431041662223 10235407855079146562493335)
    ·
      refine ⟨15353111782618719843740003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10235407855079146562493335 15353111782618719843740003)
      ·
        refine ⟨23029667673928079765610005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15353111782618719843740003 23029667673928079765610005)
        ·
          refine ⟨1079515672215378739012969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23029667673928079765610005 1079515672215378739012969)
          ·
            refine ⟨809636754161534054259727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079515672215378739012969 809636754161534054259727)
            ·
              refine ⟨1214455131242301081389591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809636754161534054259727 1214455131242301081389591)
              ·
                refine ⟨1821682696863451622084387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214455131242301081389591 1821682696863451622084387)
                ·
                  refine ⟨2732524045295177433126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821682696863451622084387 2732524045295177433126581)
                  ·
                    refine ⟨256174129246422884355617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2732524045295177433126581 256174129246422884355617)
                    ·
                      rfl

theorem cell22_748346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_748346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748346 prefixEnd_748346 := by exact prefixLift 748346
  have htrace : WordTrace (prefixWord ++ tailWord_748346) baseStart_748346 baseEnd_748346 := by
    simpa [prefixWord, tailWord_748346, baseEnd_748346] using wordTrace_append hprefix tailTrace_748346
  have hstable : (prefixWord ++ tailWord_748346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748346).length < 2 ^ (prefixWord ++ tailWord_748346).sum := by decide
  have hdescent : baseEnd_748346 < baseStart_748346 := by decide
  rcases family_descends (prefixWord ++ tailWord_748346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748365 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 4]
def baseStart_748365 : Nat := 118140960795 + 748365 * 2 ^ 59
def prefixEnd_748365 : Nat := 4983230072969 + 3 ^ 40 * 748365 * 2
def baseEnd_748365 : Nat := 85393544444904389376853

theorem tailTrace_748365 : CollatzResearch.WordTrace tailWord_748365 prefixEnd_748365 85393544444904389376853 := by
  unfold tailWord_748365
  simp only [CollatzResearch.WordTrace]
  refine ⟨27295113933808890411590549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18196742622539260274393699 27295113933808890411590549)
  ·
    refine ⟨1279458465647291738043307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27295113933808890411590549 1279458465647291738043307)
    ·
      refine ⟨1919187698470937607064961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279458465647291738043307 1919187698470937607064961)
      ·
        refine ⟨1439390773853203205298721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919187698470937607064961 1439390773853203205298721)
        ·
          refine ⟨1079543080389902403974041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439390773853203205298721 1079543080389902403974041)
          ·
            refine ⟨809657310292426802980531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079543080389902403974041 809657310292426802980531)
            ·
              refine ⟨1214485965438640204470797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809657310292426802980531 1214485965438640204470797)
              ·
                refine ⟨455432237039490076676549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214485965438640204470797 455432237039490076676549)
                ·
                  refine ⟨85393544444904389376853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455432237039490076676549 85393544444904389376853)
                  ·
                    rfl

theorem cell22_748365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_748365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748365 prefixEnd_748365 := by exact prefixLift 748365
  have htrace : WordTrace (prefixWord ++ tailWord_748365) baseStart_748365 baseEnd_748365 := by
    simpa [prefixWord, tailWord_748365, baseEnd_748365] using wordTrace_append hprefix tailTrace_748365
  have hstable : (prefixWord ++ tailWord_748365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748365).length < 2 ^ (prefixWord ++ tailWord_748365).sum := by decide
  have hdescent : baseEnd_748365 < baseStart_748365 := by decide
  rcases family_descends (prefixWord ++ tailWord_748365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748391 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 3, 3]
def baseStart_748391 : Nat := 118140960795 + 748391 * 2 ^ 59
def prefixEnd_748391 : Nat := 4983230072969 + 3 ^ 40 * 748391 * 2
def baseEnd_748391 : Nat := 256189533666057766980479

theorem tailTrace_748391 : CollatzResearch.WordTrace tailWord_748391 prefixEnd_748391 256189533666057766980479 := by
  unfold tailWord_748391
  simp only [CollatzResearch.WordTrace]
  refine ⟨27296062231714696852037027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18197374821143131234691351 27296062231714696852037027)
  ·
    refine ⟨40944093347572045278055541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27296062231714696852037027 40944093347572045278055541)
    ·
      refine ⟨3838508751334879244817707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40944093347572045278055541 3838508751334879244817707)
      ·
        refine ⟨5757763127002318867226561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838508751334879244817707 5757763127002318867226561)
        ·
          refine ⟨4318322345251739150419921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757763127002318867226561 4318322345251739150419921)
          ·
            refine ⟨3238741758938804362814941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318322345251739150419921 3238741758938804362814941)
            ·
              refine ⟨1214528159602051636055603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3238741758938804362814941 1214528159602051636055603)
              ·
                refine ⟨1821792239403077454083405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214528159602051636055603 1821792239403077454083405)
                ·
                  refine ⟨683172089776154045281277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1821792239403077454083405 683172089776154045281277)
                  ·
                    refine ⟨256189533666057766980479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683172089776154045281277 256189533666057766980479)
                    ·
                      rfl

theorem cell22_748391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_748391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748391 prefixEnd_748391 := by exact prefixLift 748391
  have htrace : WordTrace (prefixWord ++ tailWord_748391) baseStart_748391 baseEnd_748391 := by
    simpa [prefixWord, tailWord_748391, baseEnd_748391] using wordTrace_append hprefix tailTrace_748391
  have hstable : (prefixWord ++ tailWord_748391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748391).length < 2 ^ (prefixWord ++ tailWord_748391).sum := by decide
  have hdescent : baseEnd_748391 < baseStart_748391 := by decide
  rcases family_descends (prefixWord ++ tailWord_748391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748442 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_748442 : Nat := 118140960795 + 748442 * 2 ^ 59
def prefixEnd_748442 : Nat := 4983230072969 + 3 ^ 40 * 748442 * 2
def baseEnd_748442 : Nat := 256206992008310633955323

theorem tailTrace_748442 : CollatzResearch.WordTrace tailWord_748442 prefixEnd_748442 256206992008310633955323 := by
  unfold tailWord_748442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824480588632483140535895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18198614903019955041429053 6824480588632483140535895)
  ·
    refine ⟨10236720882948724710803843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6824480588632483140535895 10236720882948724710803843)
    ·
      refine ⟨15355081324423087066205765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10236720882948724710803843 15355081324423087066205765)
      ·
        refine ⟨2879077748329328824913581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15355081324423087066205765 2879077748329328824913581)
        ·
          refine ⟨1079654155623498309342593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2879077748329328824913581 1079654155623498309342593)
          ·
            refine ⟨809740616717623732006945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079654155623498309342593 809740616717623732006945)
            ·
              refine ⟨607305462538217799005209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809740616717623732006945 607305462538217799005209)
              ·
                refine ⟨455479096903663349253907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607305462538217799005209 455479096903663349253907)
                ·
                  refine ⟨683218645355495023880861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455479096903663349253907 683218645355495023880861)
                  ·
                    refine ⟨256206992008310633955323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683218645355495023880861 256206992008310633955323)
                    ·
                      rfl

theorem cell22_748442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_748442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748442 prefixEnd_748442 := by exact prefixLift 748442
  have htrace : WordTrace (prefixWord ++ tailWord_748442) baseStart_748442 baseEnd_748442 := by
    simpa [prefixWord, tailWord_748442, baseEnd_748442] using wordTrace_append hprefix tailTrace_748442
  have hstable : (prefixWord ++ tailWord_748442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748442).length < 2 ^ (prefixWord ++ tailWord_748442).sum := by decide
  have hdescent : baseEnd_748442 < baseStart_748442 := by decide
  rcases family_descends (prefixWord ++ tailWord_748442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748468 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_748468 : Nat := 118140960795 + 748468 * 2 ^ 59
def prefixEnd_748468 : Nat := 4983230072969 + 3 ^ 40 * 748468 * 2
def baseEnd_748468 : Nat := 256215892339655232805243

theorem tailTrace_748468 : CollatzResearch.WordTrace tailWord_748468 prefixEnd_748468 256215892339655232805243 := by
  unfold tailWord_748468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13649435326217869501295029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18199247101623826001726705 13649435326217869501295029)
  ·
    refine ⟨1279634561832925265746409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13649435326217869501295029 1279634561832925265746409)
    ·
      refine ⟨959725921374693949309807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1279634561832925265746409 959725921374693949309807)
      ·
        refine ⟨1439588882062040923964711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959725921374693949309807 1439588882062040923964711)
        ·
          refine ⟨2159383323093061385947067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439588882062040923964711 2159383323093061385947067)
          ·
            refine ⟨3239074984639592078920601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159383323093061385947067 3239074984639592078920601)
            ·
              refine ⟨2429306238479694059190451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239074984639592078920601 2429306238479694059190451)
              ·
                refine ⟨3643959357719541088785677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429306238479694059190451 3643959357719541088785677)
                ·
                  refine ⟨1366484759144827908294629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3643959357719541088785677 1366484759144827908294629)
                  ·
                    refine ⟨256215892339655232805243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366484759144827908294629 256215892339655232805243)
                    ·
                      rfl

theorem cell22_748468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_748468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748468 prefixEnd_748468 := by exact prefixLift 748468
  have htrace : WordTrace (prefixWord ++ tailWord_748468) baseStart_748468 baseEnd_748468 := by
    simpa [prefixWord, tailWord_748468, baseEnd_748468] using wordTrace_append hprefix tailTrace_748468
  have hstable : (prefixWord ++ tailWord_748468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748468).length < 2 ^ (prefixWord ++ tailWord_748468).sum := by decide
  have hdescent : baseEnd_748468 < baseStart_748468 := by decide
  rcases family_descends (prefixWord ++ tailWord_748468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748479 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_748479 : Nat := 118140960795 + 748479 * 2 ^ 59
def prefixEnd_748479 : Nat := 4983230072969 + 3 ^ 40 * 748479 * 2
def baseEnd_748479 : Nat := 256219657864454870780209

theorem tailTrace_748479 : CollatzResearch.WordTrace tailWord_748479 prefixEnd_748479 256219657864454870780209 := by
  unfold tailWord_748479
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299271855395887881240491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18199514570263925254160327 27299271855395887881240491)
  ·
    refine ⟨40948907783093831821860737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27299271855395887881240491 40948907783093831821860737)
    ·
      refine ⟨30711680837320373866395553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40948907783093831821860737 30711680837320373866395553)
      ·
        refine ⟨23033760627990280399796665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30711680837320373866395553 23033760627990280399796665)
        ·
          refine ⟨17275320470992710299847499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23033760627990280399796665 17275320470992710299847499)
          ·
            refine ⟨25912980706489065449771249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17275320470992710299847499 25912980706489065449771249)
            ·
              refine ⟨19434735529866799087328437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25912980706489065449771249 19434735529866799087328437)
              ·
                refine ⟨1822006455925012414437041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19434735529866799087328437 1822006455925012414437041)
                ·
                  refine ⟨1366504841943759310827781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822006455925012414437041 1366504841943759310827781)
                  ·
                    refine ⟨256219657864454870780209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366504841943759310827781 256219657864454870780209)
                    ·
                      rfl

theorem cell22_748479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_748479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748479 prefixEnd_748479 := by exact prefixLift 748479
  have htrace : WordTrace (prefixWord ++ tailWord_748479) baseStart_748479 baseEnd_748479 := by
    simpa [prefixWord, tailWord_748479, baseEnd_748479] using wordTrace_append hprefix tailTrace_748479
  have hstable : (prefixWord ++ tailWord_748479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748479).length < 2 ^ (prefixWord ++ tailWord_748479).sum := by decide
  have hdescent : baseEnd_748479 < baseStart_748479 := by decide
  rcases family_descends (prefixWord ++ tailWord_748479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748494 : List Nat := [4, 1, 1, 1, 2, 4, 9]
def baseStart_748494 : Nat := 118140960795 + 748494 * 2 ^ 59
def prefixEnd_748494 : Nat := 4983230072969 + 3 ^ 40 * 748494 * 2
def baseEnd_748494 : Nat := 9489807135962956727969

theorem tailTrace_748494 : CollatzResearch.WordTrace tailWord_748494 prefixEnd_748494 9489807135962956727969 := by
  unfold tailWord_748494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412477368792693180379567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18199879300227696962024357 3412477368792693180379567)
  ·
    refine ⟨5118716053189039770569351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412477368792693180379567 5118716053189039770569351)
    ·
      refine ⟨7678074079783559655854027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118716053189039770569351 7678074079783559655854027)
      ·
        refine ⟨11517111119675339483781041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678074079783559655854027 11517111119675339483781041)
        ·
          refine ⟨8637833339756504612835781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517111119675339483781041 8637833339756504612835781)
          ·
            refine ⟨1619593751204344614906709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8637833339756504612835781 1619593751204344614906709)
            ·
              refine ⟨9489807135962956727969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1619593751204344614906709 9489807135962956727969)
              ·
                rfl

theorem cell22_748494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 9].length) (baseStart_748494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748494 prefixEnd_748494 := by exact prefixLift 748494
  have htrace : WordTrace (prefixWord ++ tailWord_748494) baseStart_748494 baseEnd_748494 := by
    simpa [prefixWord, tailWord_748494, baseEnd_748494] using wordTrace_append hprefix tailTrace_748494
  have hstable : (prefixWord ++ tailWord_748494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748494).length < 2 ^ (prefixWord ++ tailWord_748494).sum := by decide
  have hdescent : baseEnd_748494 < baseStart_748494 := by decide
  rcases family_descends (prefixWord ++ tailWord_748494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748498 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_748498 : Nat := 118140960795 + 748498 * 2 ^ 59
def prefixEnd_748498 : Nat := 4983230072969 + 3 ^ 40 * 748498 * 2
def baseEnd_748498 : Nat := 256226161952745154555151

theorem tailTrace_748498 : CollatzResearch.WordTrace tailWord_748498 prefixEnd_748498 256226161952745154555151 := by
  unfold tailWord_748498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824991210581763531545537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18199976561551369417454765 6824991210581763531545537)
  ·
    refine ⟨5118743407936322648659153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6824991210581763531545537 5118743407936322648659153)
    ·
      refine ⟨3839057555952241986494365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118743407936322648659153 3839057555952241986494365)
      ·
        refine ⟨1439646583482090744935387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3839057555952241986494365 1439646583482090744935387)
        ·
          refine ⟨2159469875223136117403081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439646583482090744935387 2159469875223136117403081)
          ·
            refine ⟨1619602406417352088052311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159469875223136117403081 1619602406417352088052311)
            ·
              refine ⟨2429403609626028132078467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619602406417352088052311 2429403609626028132078467)
              ·
                refine ⟨3644105414439042198117701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429403609626028132078467 3644105414439042198117701)
                ·
                  refine ⟨683269765207320412147069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3644105414439042198117701 683269765207320412147069)
                  ·
                    refine ⟨256226161952745154555151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683269765207320412147069 256226161952745154555151)
                    ·
                      rfl

theorem cell22_748498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_748498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748498 prefixEnd_748498 := by exact prefixLift 748498
  have htrace : WordTrace (prefixWord ++ tailWord_748498) baseStart_748498 baseEnd_748498 := by
    simpa [prefixWord, tailWord_748498, baseEnd_748498] using wordTrace_append hprefix tailTrace_748498
  have hstable : (prefixWord ++ tailWord_748498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748498).length < 2 ^ (prefixWord ++ tailWord_748498).sum := by decide
  have hdescent : baseEnd_748498 < baseStart_748498 := by decide
  rcases family_descends (prefixWord ++ tailWord_748498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748573 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 5]
def baseStart_748573 : Nat := 118140960795 + 748573 * 2 ^ 59
def prefixEnd_748573 : Nat := 4983230072969 + 3 ^ 40 * 748573 * 2
def baseEnd_748573 : Nat := 85417278661823319643307

theorem tailTrace_748573 : CollatzResearch.WordTrace tailWord_748573 prefixEnd_748573 85417278661823319643307 := by
  unfold tailWord_748573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302700317055341935162373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18201800211370227956774915 27302700317055341935162373)
  ·
    refine ⟨5119256309447876612842945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27302700317055341935162373 5119256309447876612842945)
    ·
      refine ⟨3839442232085907459632209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5119256309447876612842945 3839442232085907459632209)
      ·
        refine ⟨2879581674064430594724157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3839442232085907459632209 2879581674064430594724157)
        ·
          refine ⟨1079843127774161473021559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2879581674064430594724157 1079843127774161473021559)
          ·
            refine ⟨1619764691661242209532339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079843127774161473021559 1619764691661242209532339)
            ·
              refine ⟨2429647037491863314298509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619764691661242209532339 2429647037491863314298509)
              ·
                refine ⟨911117639059448742861941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2429647037491863314298509 911117639059448742861941)
                ·
                  refine ⟨85417278661823319643307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 911117639059448742861941 85417278661823319643307)
                  ·
                    rfl

theorem cell22_748573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_748573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748573 prefixEnd_748573 := by exact prefixLift 748573
  have htrace : WordTrace (prefixWord ++ tailWord_748573) baseStart_748573 baseEnd_748573 := by
    simpa [prefixWord, tailWord_748573, baseEnd_748573] using wordTrace_append hprefix tailTrace_748573
  have hstable : (prefixWord ++ tailWord_748573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748573).length < 2 ^ (prefixWord ++ tailWord_748573).sum := by decide
  have hdescent : baseEnd_748573 < baseStart_748573 := by decide
  rcases family_descends (prefixWord ++ tailWord_748573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748691 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 5]
def baseStart_748691 : Nat := 118140960795 + 748691 * 2 ^ 59
def prefixEnd_748691 : Nat := 4983230072969 + 3 ^ 40 * 748691 * 2
def baseEnd_748691 : Nat := 85430743265652328159853

theorem tailTrace_748691 : CollatzResearch.WordTrace tailWord_748691 prefixEnd_748691 85430743265652328159853 := by
  unfold tailWord_748691
  simp only [CollatzResearch.WordTrace]
  refine ⟨27307004130627848087957927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18204669420418565391971951 27307004130627848087957927)
  ·
    refine ⟨40960506195941772131936891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27307004130627848087957927 40960506195941772131936891)
    ·
      refine ⟨61440759293912658197905337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40960506195941772131936891 61440759293912658197905337)
      ·
        refine ⟨46080569470434493648429003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61440759293912658197905337 46080569470434493648429003)
        ·
          refine ⟨69120854205651740472643505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46080569470434493648429003 69120854205651740472643505)
          ·
            refine ⟨51840640654238805354482629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69120854205651740472643505 51840640654238805354482629)
            ·
              refine ⟨9720120122669776003965493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51840640654238805354482629 9720120122669776003965493)
              ·
                refine ⟨911261261500291500371765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9720120122669776003965493 911261261500291500371765)
                ·
                  refine ⟨85430743265652328159853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 911261261500291500371765 85430743265652328159853)
                  ·
                    rfl

theorem cell22_748691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 5].length) (baseStart_748691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748691 prefixEnd_748691 := by exact prefixLift 748691
  have htrace : WordTrace (prefixWord ++ tailWord_748691) baseStart_748691 baseEnd_748691 := by
    simpa [prefixWord, tailWord_748691, baseEnd_748691] using wordTrace_append hprefix tailTrace_748691
  have hstable : (prefixWord ++ tailWord_748691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748691).length < 2 ^ (prefixWord ++ tailWord_748691).sum := by decide
  have hdescent : baseEnd_748691 < baseStart_748691 := by decide
  rcases family_descends (prefixWord ++ tailWord_748691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748768 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_748768 : Nat := 118140960795 + 748768 * 2 ^ 59
def prefixEnd_748768 : Nat := 4983230072969 + 3 ^ 40 * 748768 * 2
def baseEnd_748768 : Nat := 256318588470554450304323

theorem tailTrace_748768 : CollatzResearch.WordTrace tailWord_748768 prefixEnd_748768 256318588470554450304323 := by
  unfold tailWord_748768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654906275674445119255479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18206541700899260159007305 13654906275674445119255479)
  ·
    refine ⟨20482359413511667678883219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13654906275674445119255479 20482359413511667678883219)
    ·
      refine ⟨30723539120267501518324829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20482359413511667678883219 30723539120267501518324829)
      ·
        refine ⟨11521327170100313069371811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30723539120267501518324829 11521327170100313069371811)
        ·
          refine ⟨17281990755150469604057717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11521327170100313069371811 17281990755150469604057717)
          ·
            refine ⟨1620186633295356525380411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17281990755150469604057717 1620186633295356525380411)
            ·
              refine ⟨2430279949943034788070617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620186633295356525380411 2430279949943034788070617)
              ·
                refine ⟨1822709962457276091052963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430279949943034788070617 1822709962457276091052963)
                ·
                  refine ⟨2734064943685914136579445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822709962457276091052963 2734064943685914136579445)
                  ·
                    refine ⟨256318588470554450304323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2734064943685914136579445 256318588470554450304323)
                    ·
                      rfl

theorem cell22_748768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_748768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748768 prefixEnd_748768 := by exact prefixLift 748768
  have htrace : WordTrace (prefixWord ++ tailWord_748768) baseStart_748768 baseEnd_748768 := by
    simpa [prefixWord, tailWord_748768, baseEnd_748768] using wordTrace_append hprefix tailTrace_748768
  have hstable : (prefixWord ++ tailWord_748768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748768).length < 2 ^ (prefixWord ++ tailWord_748768).sum := by decide
  have hdescent : baseEnd_748768 < baseStart_748768 := by decide
  rcases family_descends (prefixWord ++ tailWord_748768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748787 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 4]
def baseStart_748787 : Nat := 118140960795 + 748787 * 2 ^ 59
def prefixEnd_748787 : Nat := 4983230072969 + 3 ^ 40 * 748787 * 2
def baseEnd_748787 : Nat := 85441697519614911359755

theorem tailTrace_748787 : CollatzResearch.WordTrace tailWord_748787 prefixEnd_748787 85441697519614911359755 := by
  unfold tailWord_748787
  simp only [CollatzResearch.WordTrace]
  refine ⟨27310505538280056483452615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18207003692186704322301743 27310505538280056483452615)
  ·
    refine ⟨40965758307420084725178923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27310505538280056483452615 40965758307420084725178923)
    ·
      refine ⟨61448637461130127087768385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40965758307420084725178923 61448637461130127087768385)
      ·
        refine ⟨46086478095847595315826289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61448637461130127087768385 46086478095847595315826289)
        ·
          refine ⟨34564858571885696486869717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46086478095847595315826289 34564858571885696486869717)
          ·
            refine ⟨810113872778571011411009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34564858571885696486869717 810113872778571011411009)
            ·
              refine ⟨607585404583928258558257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810113872778571011411009 607585404583928258558257)
              ·
                refine ⟨455689053437946193918693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607585404583928258558257 455689053437946193918693)
                ·
                  refine ⟨85441697519614911359755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455689053437946193918693 85441697519614911359755)
                  ·
                    rfl

theorem cell22_748787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 4].length) (baseStart_748787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748787 prefixEnd_748787 := by exact prefixLift 748787
  have htrace : WordTrace (prefixWord ++ tailWord_748787) baseStart_748787 baseEnd_748787 := by
    simpa [prefixWord, tailWord_748787, baseEnd_748787] using wordTrace_append hprefix tailTrace_748787
  have hstable : (prefixWord ++ tailWord_748787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748787).length < 2 ^ (prefixWord ++ tailWord_748787).sum := by decide
  have hdescent : baseEnd_748787 < baseStart_748787 := by decide
  rcases family_descends (prefixWord ++ tailWord_748787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748802 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_748802 : Nat := 118140960795 + 748802 * 2 ^ 59
def prefixEnd_748802 : Nat := 4983230072969 + 3 ^ 40 * 748802 * 2
def baseEnd_748802 : Nat := 256330227365389694954219

theorem tailTrace_748802 : CollatzResearch.WordTrace tailWord_748802 prefixEnd_748802 256330227365389694954219 := by
  unfold tailWord_748802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6827763158306428511312165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18207368422150476030165773 6827763158306428511312165)
  ·
    refine ⟨1280205592182455345871031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6827763158306428511312165 1280205592182455345871031)
    ·
      refine ⟨1920308388273683018806547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280205592182455345871031 1920308388273683018806547)
      ·
        refine ⟨2880462582410524528209821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920308388273683018806547 2880462582410524528209821)
        ·
          refine ⟨1080173468403946698078683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2880462582410524528209821 1080173468403946698078683)
          ·
            refine ⟨1620260202605920047118025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080173468403946698078683 1620260202605920047118025)
            ·
              refine ⟨1215195151954440035338519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620260202605920047118025 1215195151954440035338519)
              ·
                refine ⟨1822792727931660053007779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215195151954440035338519 1822792727931660053007779)
                ·
                  refine ⟨2734189091897490079511669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822792727931660053007779 2734189091897490079511669)
                  ·
                    refine ⟨256330227365389694954219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2734189091897490079511669 256330227365389694954219)
                    ·
                      rfl

theorem cell22_748802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_748802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748802 prefixEnd_748802 := by exact prefixLift 748802
  have htrace : WordTrace (prefixWord ++ tailWord_748802) baseStart_748802 baseEnd_748802 := by
    simpa [prefixWord, tailWord_748802, baseEnd_748802] using wordTrace_append hprefix tailTrace_748802
  have hstable : (prefixWord ++ tailWord_748802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748802).length < 2 ^ (prefixWord ++ tailWord_748802).sum := by decide
  have hdescent : baseEnd_748802 < baseStart_748802 := by decide
  rcases family_descends (prefixWord ++ tailWord_748802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748858 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_748858 : Nat := 118140960795 + 748858 * 2 ^ 59
def prefixEnd_748858 : Nat := 4983230072969 + 3 ^ 40 * 748858 * 2
def baseEnd_748858 : Nat := 256349397309824215554047

theorem tailTrace_748858 : CollatzResearch.WordTrace tailWord_748858 prefixEnd_748858 256349397309824215554047 := by
  unfold tailWord_748858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828273780255708902321807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18208730080681890406191485 6828273780255708902321807)
  ·
    refine ⟨10242410670383563353482711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6828273780255708902321807 10242410670383563353482711)
    ·
      refine ⟨15363616005575345030224067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242410670383563353482711 15363616005575345030224067)
      ·
        refine ⟨23045424008363017545336101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363616005575345030224067 23045424008363017545336101)
        ·
          refine ⟨4321017001568065789750519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23045424008363017545336101 4321017001568065789750519)
          ·
            refine ⟨6481525502352098684625779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321017001568065789750519 6481525502352098684625779)
            ·
              refine ⟨9722288253528148026938669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481525502352098684625779 9722288253528148026938669)
              ·
                refine ⟨3645858095073055510102001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9722288253528148026938669 3645858095073055510102001)
                ·
                  refine ⟨2734393571304791632576501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645858095073055510102001 2734393571304791632576501)
                  ·
                    refine ⟨256349397309824215554047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2734393571304791632576501 256349397309824215554047)
                    ·
                      rfl

theorem cell22_748858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_748858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748858 prefixEnd_748858 := by exact prefixLift 748858
  have htrace : WordTrace (prefixWord ++ tailWord_748858) baseStart_748858 baseEnd_748858 := by
    simpa [prefixWord, tailWord_748858, baseEnd_748858] using wordTrace_append hprefix tailTrace_748858
  have hstable : (prefixWord ++ tailWord_748858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748858).length < 2 ^ (prefixWord ++ tailWord_748858).sum := by decide
  have hdescent : baseEnd_748858 < baseStart_748858 := by decide
  rcases family_descends (prefixWord ++ tailWord_748858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748873 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_748873 : Nat := 118140960795 + 748873 * 2 ^ 59
def prefixEnd_748873 : Nat := 4983230072969 + 3 ^ 40 * 748873 * 2
def baseEnd_748873 : Nat := 256354532116369176429001

theorem tailTrace_748873 : CollatzResearch.WordTrace tailWord_748873 prefixEnd_748873 256354532116369176429001 := by
  unfold tailWord_748873
  simp only [CollatzResearch.WordTrace]
  refine ⟨27313642215968493171083273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18209094810645662114055515 27313642215968493171083273)
  ·
    refine ⟨20485231661976369878312455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27313642215968493171083273 20485231661976369878312455)
    ·
      refine ⟨30727847492964554817468683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20485231661976369878312455 30727847492964554817468683)
      ·
        refine ⟨46091771239446832226203025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30727847492964554817468683 46091771239446832226203025)
        ·
          refine ⟨34568828429585124169652269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46091771239446832226203025 34568828429585124169652269)
          ·
            refine ⟨12963310661094421563619601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34568828429585124169652269 12963310661094421563619601)
            ·
              refine ⟨9722482995820816172714701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12963310661094421563619601 9722482995820816172714701)
              ·
                refine ⟨3645931123432806064768013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9722482995820816172714701 3645931123432806064768013)
                ·
                  refine ⟨1367224171287302274288005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3645931123432806064768013 1367224171287302274288005)
                  ·
                    refine ⟨256354532116369176429001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1367224171287302274288005 256354532116369176429001)
                    ·
                      rfl

theorem cell22_748873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_748873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748873 prefixEnd_748873 := by exact prefixLift 748873
  have htrace : WordTrace (prefixWord ++ tailWord_748873) baseStart_748873 baseEnd_748873 := by
    simpa [prefixWord, tailWord_748873, baseEnd_748873] using wordTrace_append hprefix tailTrace_748873
  have hstable : (prefixWord ++ tailWord_748873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748873).length < 2 ^ (prefixWord ++ tailWord_748873).sum := by decide
  have hdescent : baseEnd_748873 < baseStart_748873 := by decide
  rcases family_descends (prefixWord ++ tailWord_748873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748890 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_748890 : Nat := 118140960795 + 748890 * 2 ^ 59
def prefixEnd_748890 : Nat := 4983230072969 + 3 ^ 40 * 748890 * 2
def baseEnd_748890 : Nat := 256360351563786798753949

theorem tailTrace_748890 : CollatzResearch.WordTrace tailWord_748890 prefixEnd_748890 256360351563786798753949 := by
  unfold tailWord_748890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828565564226726268613031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18209508171271270049634749 6828565564226726268613031)
  ·
    refine ⟨10242848346340089402919547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6828565564226726268613031 10242848346340089402919547)
    ·
      refine ⟨15364272519510134104379321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242848346340089402919547 15364272519510134104379321)
      ·
        refine ⟨11523204389632600578284491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15364272519510134104379321 11523204389632600578284491)
        ·
          refine ⟨17284806584448900867426737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523204389632600578284491 17284806584448900867426737)
          ·
            refine ⟨12963604938336675650570053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17284806584448900867426737 12963604938336675650570053)
            ·
              refine ⟨2430675925938126684481885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12963604938336675650570053 2430675925938126684481885)
              ·
                refine ⟨911503472226797506680707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430675925938126684481885 911503472226797506680707)
                ·
                  refine ⟨1367255208340196260021061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911503472226797506680707 1367255208340196260021061)
                  ·
                    refine ⟨256360351563786798753949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1367255208340196260021061 256360351563786798753949)
                    ·
                      rfl

theorem cell22_748890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_748890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748890 prefixEnd_748890 := by exact prefixLift 748890
  have htrace : WordTrace (prefixWord ++ tailWord_748890) baseStart_748890 baseEnd_748890 := by
    simpa [prefixWord, tailWord_748890, baseEnd_748890] using wordTrace_append hprefix tailTrace_748890
  have hstable : (prefixWord ++ tailWord_748890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748890).length < 2 ^ (prefixWord ++ tailWord_748890).sum := by decide
  have hdescent : baseEnd_748890 < baseStart_748890 := by decide
  rcases family_descends (prefixWord ++ tailWord_748890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748933 : List Nat := [1, 3, 1, 1, 3, 1, 4, 8]
def baseStart_748933 : Nat := 118140960795 + 748933 * 2 ^ 59
def prefixEnd_748933 : Nat := 4983230072969 + 3 ^ 40 * 748933 * 2
def baseEnd_748933 : Nat := 28486119038061002214313

theorem tailTrace_748933 : CollatzResearch.WordTrace tailWord_748933 prefixEnd_748933 28486119038061002214313 := by
  unfold tailWord_748933
  simp only [CollatzResearch.WordTrace]
  refine ⟨27315830595751123418267453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18210553730500748945511635 27315830595751123418267453)
  ·
    refine ⟨10243436473406671281850295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27315830595751123418267453 10243436473406671281850295)
    ·
      refine ⟨15365154710110006922775443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10243436473406671281850295 15365154710110006922775443)
      ·
        refine ⟨23047732065165010384163165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15365154710110006922775443 23047732065165010384163165)
        ·
          refine ⟨8642899524436878894061187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23047732065165010384163165 8642899524436878894061187)
          ·
            refine ⟨12964349286655318341091781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642899524436878894061187 12964349286655318341091781)
            ·
              refine ⟨2430815491247872188954709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12964349286655318341091781 2430815491247872188954709)
              ·
                refine ⟨28486119038061002214313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2430815491247872188954709 28486119038061002214313)
                ·
                  rfl

theorem cell22_748933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 8].length) (baseStart_748933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748933 prefixEnd_748933 := by exact prefixLift 748933
  have htrace : WordTrace (prefixWord ++ tailWord_748933) baseStart_748933 baseEnd_748933 := by
    simpa [prefixWord, tailWord_748933, baseEnd_748933] using wordTrace_append hprefix tailTrace_748933
  have hstable : (prefixWord ++ tailWord_748933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748933).length < 2 ^ (prefixWord ++ tailWord_748933).sum := by decide
  have hdescent : baseEnd_748933 < baseStart_748933 := by decide
  rcases family_descends (prefixWord ++ tailWord_748933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748935 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_748935 : Nat := 118140960795 + 748935 * 2 ^ 59
def prefixEnd_748935 : Nat := 4983230072969 + 3 ^ 40 * 748935 * 2
def baseEnd_748935 : Nat := 256375755983421681378811

theorem tailTrace_748935 : CollatzResearch.WordTrace tailWord_748935 prefixEnd_748935 256375755983421681378811 := by
  unfold tailWord_748935
  simp only [CollatzResearch.WordTrace]
  refine ⟨27315903541743877759840259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18210602361162585173226839 27315903541743877759840259)
  ·
    refine ⟨40973855312615816639760389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27315903541743877759840259 40973855312615816639760389)
    ·
      refine ⟨7682597871115465619955073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40973855312615816639760389 7682597871115465619955073)
      ·
        refine ⟨5761948403336599214966305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7682597871115465619955073 5761948403336599214966305)
        ·
          refine ⟨4321461302502449411224729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5761948403336599214966305 4321461302502449411224729)
          ·
            refine ⟨3241095976876837058418547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4321461302502449411224729 3241095976876837058418547)
            ·
              refine ⟨4861643965315255587627821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241095976876837058418547 4861643965315255587627821)
              ·
                refine ⟨1823116486993220845360433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4861643965315255587627821 1823116486993220845360433)
                ·
                  refine ⟨1367337365244915634020325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1823116486993220845360433 1367337365244915634020325)
                  ·
                    refine ⟨256375755983421681378811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1367337365244915634020325 256375755983421681378811)
                    ·
                      rfl

theorem cell22_748935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_748935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748935 prefixEnd_748935 := by exact prefixLift 748935
  have htrace : WordTrace (prefixWord ++ tailWord_748935) baseStart_748935 baseEnd_748935 := by
    simpa [prefixWord, tailWord_748935, baseEnd_748935] using wordTrace_append hprefix tailTrace_748935
  have hstable : (prefixWord ++ tailWord_748935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748935).length < 2 ^ (prefixWord ++ tailWord_748935).sum := by decide
  have hdescent : baseEnd_748935 < baseStart_748935 := by decide
  rcases family_descends (prefixWord ++ tailWord_748935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748963 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_748963 : Nat := 118140960795 + 748963 * 2 ^ 59
def prefixEnd_748963 : Nat := 4983230072969 + 3 ^ 40 * 748963 * 2
def baseEnd_748963 : Nat := 256385340955638941678725

theorem tailTrace_748963 : CollatzResearch.WordTrace tailWord_748963 prefixEnd_748963 256385340955638941678725 := by
  unfold tailWord_748963
  simp only [CollatzResearch.WordTrace]
  refine ⟨27316924785642438541859543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18211283190428292361239695 27316924785642438541859543)
  ·
    refine ⟨40975387178463657812789315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27316924785642438541859543 40975387178463657812789315)
    ·
      refine ⟨61463080767695486719183973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40975387178463657812789315 61463080767695486719183973)
      ·
        refine ⟨11524327643942903759846995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61463080767695486719183973 11524327643942903759846995)
        ·
          refine ⟨17286491465914355639770493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524327643942903759846995 17286491465914355639770493)
          ·
            refine ⟨6482434299717883364913935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17286491465914355639770493 6482434299717883364913935)
            ·
              refine ⟨9723651449576825047370903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6482434299717883364913935 9723651449576825047370903)
              ·
                refine ⟨14585477174365237571056355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723651449576825047370903 14585477174365237571056355)
                ·
                  refine ⟨21878215761547856356584533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14585477174365237571056355 21878215761547856356584533)
                  ·
                    refine ⟨256385340955638941678725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21878215761547856356584533 256385340955638941678725)
                    ·
                      rfl

theorem cell22_748963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_748963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748963 prefixEnd_748963 := by exact prefixLift 748963
  have htrace : WordTrace (prefixWord ++ tailWord_748963) baseStart_748963 baseEnd_748963 := by
    simpa [prefixWord, tailWord_748963, baseEnd_748963] using wordTrace_append hprefix tailTrace_748963
  have hstable : (prefixWord ++ tailWord_748963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748963).length < 2 ^ (prefixWord ++ tailWord_748963).sum := by decide
  have hdescent : baseEnd_748963 < baseStart_748963 := by decide
  rcases family_descends (prefixWord ++ tailWord_748963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748999 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 1, 3]
def baseStart_748999 : Nat := 118140960795 + 748999 * 2 ^ 59
def prefixEnd_748999 : Nat := 4983230072969 + 3 ^ 40 * 748999 * 2
def baseEnd_748999 : Nat := 256397664491346847778615

theorem tailTrace_748999 : CollatzResearch.WordTrace tailWord_748999 prefixEnd_748999 256397664491346847778615 := by
  unfold tailWord_748999
  simp only [CollatzResearch.WordTrace]
  refine ⟨27318237813512016690170051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18212158542341344460113367 27318237813512016690170051)
  ·
    refine ⟨40977356720268025035255077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27318237813512016690170051 40977356720268025035255077)
    ·
      refine ⟨7683254385050254694110327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40977356720268025035255077 7683254385050254694110327)
      ·
        refine ⟨11524881577575382041165491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7683254385050254694110327 11524881577575382041165491)
        ·
          refine ⟨17287322366363073061748237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524881577575382041165491 17287322366363073061748237)
          ·
            refine ⟨6482745887386152398155589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17287322366363073061748237 6482745887386152398155589)
            ·
              refine ⟨1215514853884903574654173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6482745887386152398155589 1215514853884903574654173)
              ·
                refine ⟨455818070206838840495315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1215514853884903574654173 455818070206838840495315)
                ·
                  refine ⟨683727105310258260742973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455818070206838840495315 683727105310258260742973)
                  ·
                    refine ⟨256397664491346847778615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683727105310258260742973 256397664491346847778615)
                    ·
                      rfl

theorem cell22_748999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_748999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_748999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_748999 prefixEnd_748999 := by exact prefixLift 748999
  have htrace : WordTrace (prefixWord ++ tailWord_748999) baseStart_748999 baseEnd_748999 := by
    simpa [prefixWord, tailWord_748999, baseEnd_748999] using wordTrace_append hprefix tailTrace_748999
  have hstable : (prefixWord ++ tailWord_748999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748999).length < 2 ^ (prefixWord ++ tailWord_748999).sum := by decide
  have hdescent : baseEnd_748999 < baseStart_748999 := by decide
  rcases family_descends (prefixWord ++ tailWord_748999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749012 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_749012 : Nat := 118140960795 + 749012 * 2 ^ 59
def prefixEnd_749012 : Nat := 4983230072969 + 3 ^ 40 * 749012 * 2
def baseEnd_749012 : Nat := 85467371552339715734525

theorem tailTrace_749012 : CollatzResearch.WordTrace tailWord_749012 prefixEnd_749012 85467371552339715734525 := by
  unfold tailWord_749012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659355981232459955196645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18212474641643279940262193 13659355981232459955196645)
  ·
    refine ⟨2561129246481086241599371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13659355981232459955196645 2561129246481086241599371)
    ·
      refine ⟨3841693869721629362399057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2561129246481086241599371 3841693869721629362399057)
      ·
        refine ⟨2881270402291222021799293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841693869721629362399057 2881270402291222021799293)
        ·
          refine ⟨1080476400859208258174735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2881270402291222021799293 1080476400859208258174735)
          ·
            refine ⟨1620714601288812387262103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080476400859208258174735 1620714601288812387262103)
            ·
              refine ⟨2431071901933218580893155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620714601288812387262103 2431071901933218580893155)
              ·
                refine ⟨3646607852899827871339733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431071901933218580893155 3646607852899827871339733)
                ·
                  refine ⟨85467371552339715734525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3646607852899827871339733 85467371552339715734525)
                  ·
                    rfl

theorem cell22_749012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_749012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749012 prefixEnd_749012 := by exact prefixLift 749012
  have htrace : WordTrace (prefixWord ++ tailWord_749012) baseStart_749012 baseEnd_749012 := by
    simpa [prefixWord, tailWord_749012, baseEnd_749012] using wordTrace_append hprefix tailTrace_749012
  have hstable : (prefixWord ++ tailWord_749012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749012).length < 2 ^ (prefixWord ++ tailWord_749012).sum := by decide
  have hdescent : baseEnd_749012 < baseStart_749012 := by decide
  rcases family_descends (prefixWord ++ tailWord_749012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749029 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 5]
def baseStart_749029 : Nat := 118140960795 + 749029 * 2 ^ 59
def prefixEnd_749029 : Nat := 4983230072969 + 3 ^ 40 * 749029 * 2
def baseEnd_749029 : Nat := 85469311368145589842841

theorem tailTrace_749029 : CollatzResearch.WordTrace tailWord_749029 prefixEnd_749029 85469311368145589842841 := by
  unfold tailWord_749029
  simp only [CollatzResearch.WordTrace]
  refine ⟨27319332003403331813762141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18212888002268887875841427 27319332003403331813762141)
  ·
    refine ⟨10244749501276249430160803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27319332003403331813762141 10244749501276249430160803)
    ·
      refine ⟨15367124251914374145241205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10244749501276249430160803 15367124251914374145241205)
      ·
        refine ⟨1440667898616972576116363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15367124251914374145241205 1440667898616972576116363)
        ·
          refine ⟨2161001847925458864174545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440667898616972576116363 2161001847925458864174545)
          ·
            refine ⟨1620751385944094148130909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161001847925458864174545 1620751385944094148130909)
            ·
              refine ⟨607781769729035305549091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1620751385944094148130909 607781769729035305549091)
              ·
                refine ⟨911672654593552958323637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607781769729035305549091 911672654593552958323637)
                ·
                  refine ⟨85469311368145589842841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 911672654593552958323637 85469311368145589842841)
                  ·
                    rfl

theorem cell22_749029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_749029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749029 prefixEnd_749029 := by exact prefixLift 749029
  have htrace : WordTrace (prefixWord ++ tailWord_749029) baseStart_749029 baseEnd_749029 := by
    simpa [prefixWord, tailWord_749029, baseEnd_749029] using wordTrace_append hprefix tailTrace_749029
  have hstable : (prefixWord ++ tailWord_749029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749029).length < 2 ^ (prefixWord ++ tailWord_749029).sum := by decide
  have hdescent : baseEnd_749029 < baseStart_749029 := by decide
  rcases family_descends (prefixWord ++ tailWord_749029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749040 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_749040 : Nat := 118140960795 + 749040 * 2 ^ 59
def prefixEnd_749040 : Nat := 4983230072969 + 3 ^ 40 * 749040 * 2
def baseEnd_749040 : Nat := 85470566543078802501163

theorem tailTrace_749040 : CollatzResearch.WordTrace tailWord_749040 prefixEnd_749040 85470566543078802501163 := by
  unfold tailWord_749040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659866603181740346206287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18213155470908987128275049 13659866603181740346206287)
  ·
    refine ⟨20489799904772610519309431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659866603181740346206287 20489799904772610519309431)
    ·
      refine ⟨30734699857158915778964147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20489799904772610519309431 30734699857158915778964147)
      ·
        refine ⟨46102049785738373668446221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30734699857158915778964147 46102049785738373668446221)
        ·
          refine ⟨17288268669651890125667333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46102049785738373668446221 17288268669651890125667333)
          ·
            refine ⟨3241550375559729398562625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17288268669651890125667333 3241550375559729398562625)
            ·
              refine ⟨2431162781669797048921969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241550375559729398562625 2431162781669797048921969)
              ·
                refine ⟨1823372086252347786691477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431162781669797048921969 1823372086252347786691477)
                ·
                  refine ⟨85470566543078802501163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1823372086252347786691477 85470566543078802501163)
                  ·
                    rfl

theorem cell22_749040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_749040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749040 prefixEnd_749040 := by exact prefixLift 749040
  have htrace : WordTrace (prefixWord ++ tailWord_749040) baseStart_749040 baseEnd_749040 := by
    simpa [prefixWord, tailWord_749040, baseEnd_749040] using wordTrace_append hprefix tailTrace_749040
  have hstable : (prefixWord ++ tailWord_749040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749040).length < 2 ^ (prefixWord ++ tailWord_749040).sum := by decide
  have hdescent : baseEnd_749040 < baseStart_749040 := by decide
  rcases family_descends (prefixWord ++ tailWord_749040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749089 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_749089 : Nat := 118140960795 + 749089 * 2 ^ 59
def prefixEnd_749089 : Nat := 4983230072969 + 3 ^ 40 * 749089 * 2
def baseEnd_749089 : Nat := 256428473330616613028339

theorem tailTrace_749089 : CollatzResearch.WordTrace tailWord_749089 prefixEnd_749089 256428473330616613028339 := by
  unfold tailWord_749089
  simp only [CollatzResearch.WordTrace]
  refine ⟨27321520383185962060946321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18214346922123974707297547 27321520383185962060946321)
  ·
    refine ⟨20491140287389471545709741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27321520383185962060946321 20491140287389471545709741)
    ·
      refine ⟨7684177607771051829641153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20491140287389471545709741 7684177607771051829641153)
      ·
        refine ⟨5763133205828288872230865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7684177607771051829641153 5763133205828288872230865)
        ·
          refine ⟨4322349904371216654173149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5763133205828288872230865 4322349904371216654173149)
          ·
            refine ⟨1620881214139206245314931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4322349904371216654173149 1620881214139206245314931)
            ·
              refine ⟨2431321821208809367972397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620881214139206245314931 2431321821208809367972397)
              ·
                refine ⟨911745682953303512989649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2431321821208809367972397 911745682953303512989649)
                ·
                  refine ⟨683809262214977634742237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911745682953303512989649 683809262214977634742237)
                  ·
                    refine ⟨256428473330616613028339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683809262214977634742237 256428473330616613028339)
                    ·
                      rfl

theorem cell22_749089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_749089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749089 prefixEnd_749089 := by exact prefixLift 749089
  have htrace : WordTrace (prefixWord ++ tailWord_749089) baseStart_749089 baseEnd_749089 := by
    simpa [prefixWord, tailWord_749089, baseEnd_749089] using wordTrace_append hprefix tailTrace_749089
  have hstable : (prefixWord ++ tailWord_749089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749089).length < 2 ^ (prefixWord ++ tailWord_749089).sum := by decide
  have hdescent : baseEnd_749089 < baseStart_749089 := by decide
  rcases family_descends (prefixWord ++ tailWord_749089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749102 : List Nat := [4, 1, 3, 1, 2, 1, 2, 8]
def baseStart_749102 : Nat := 118140960795 + 749102 * 2 ^ 59
def prefixEnd_749102 : Nat := 4983230072969 + 3 ^ 40 * 749102 * 2
def baseEnd_749102 : Nat := 28492547055143212494811

theorem tailTrace_749102 : CollatzResearch.WordTrace tailWord_749102 prefixEnd_749102 28492547055143212494811 := by
  unfold tailWord_749102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415249316517358160146195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18214663021425910187446373 3415249316517358160146195)
  ·
    refine ⟨5122873974776037240219293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3415249316517358160146195 5122873974776037240219293)
    ·
      refine ⟨1921077740541013965082235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5122873974776037240219293 1921077740541013965082235)
      ·
        refine ⟨2881616610811520947623353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921077740541013965082235 2881616610811520947623353)
        ·
          refine ⟨2161212458108640710717515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881616610811520947623353 2161212458108640710717515)
          ·
            refine ⟨3241818687162961066076273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161212458108640710717515 3241818687162961066076273)
            ·
              refine ⟨2431364015372220799557205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241818687162961066076273 2431364015372220799557205)
              ·
                refine ⟨28492547055143212494811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2431364015372220799557205 28492547055143212494811)
                ·
                  rfl

theorem cell22_749102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_749102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749102 prefixEnd_749102 := by exact prefixLift 749102
  have htrace : WordTrace (prefixWord ++ tailWord_749102) baseStart_749102 baseEnd_749102 := by
    simpa [prefixWord, tailWord_749102, baseEnd_749102] using wordTrace_append hprefix tailTrace_749102
  have hstable : (prefixWord ++ tailWord_749102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749102).length < 2 ^ (prefixWord ++ tailWord_749102).sum := by decide
  have hdescent : baseEnd_749102 < baseStart_749102 := by decide
  rcases family_descends (prefixWord ++ tailWord_749102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749175 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 10]
def baseStart_749175 : Nat := 118140960795 + 749175 * 2 ^ 59
def prefixEnd_749175 : Nat := 4983230072969 + 3 ^ 40 * 749175 * 2
def baseEnd_749175 : Nat := 85485970962713685126025

theorem tailTrace_749175 : CollatzResearch.WordTrace tailWord_749175 prefixEnd_749175 85485970962713685126025 := by
  unfold tailWord_749175
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324657060874398748576979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18216438040582932499051319 27324657060874398748576979)
  ·
    refine ⟨40986985591311598122865469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27324657060874398748576979 40986985591311598122865469)
    ·
      refine ⟨15370119596741849296074551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40986985591311598122865469 15370119596741849296074551)
      ·
        refine ⟨23055179395112773944111827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370119596741849296074551 23055179395112773944111827)
        ·
          refine ⟨34582769092669160916167741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23055179395112773944111827 34582769092669160916167741)
          ·
            refine ⟨12968538409750935343562903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34582769092669160916167741 12968538409750935343562903)
            ·
              refine ⟨19452807614626403015344355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968538409750935343562903 19452807614626403015344355)
              ·
                refine ⟨29179211421939604523016533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19452807614626403015344355 29179211421939604523016533)
                ·
                  refine ⟨85485970962713685126025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29179211421939604523016533 85485970962713685126025)
                  ·
                    rfl

theorem cell22_749175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_749175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749175 prefixEnd_749175 := by exact prefixLift 749175
  have htrace : WordTrace (prefixWord ++ tailWord_749175) baseStart_749175 baseEnd_749175 := by
    simpa [prefixWord, tailWord_749175, baseEnd_749175] using wordTrace_append hprefix tailTrace_749175
  have hstable : (prefixWord ++ tailWord_749175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749175).length < 2 ^ (prefixWord ++ tailWord_749175).sum := by decide
  have hdescent : baseEnd_749175 < baseStart_749175 := by decide
  rcases family_descends (prefixWord ++ tailWord_749175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749239 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_749239 : Nat := 118140960795 + 749239 * 2 ^ 59
def prefixEnd_749239 : Nat := 4983230072969 + 3 ^ 40 * 749239 * 2
def baseEnd_749239 : Nat := 256479821396066221777879

theorem tailTrace_749239 : CollatzResearch.WordTrace tailWord_749239 prefixEnd_749239 256479821396066221777879 := by
  unfold tailWord_749239
  simp only [CollatzResearch.WordTrace]
  refine ⟨27326991332642537678906771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18217994221761691785937847 27326991332642537678906771)
  ·
    refine ⟨40990486998963806518360157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27326991332642537678906771 40990486998963806518360157)
    ·
      refine ⟨15371432624611427444385059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40990486998963806518360157 15371432624611427444385059)
      ·
        refine ⟨23057148936917141166577589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15371432624611427444385059 23057148936917141166577589)
        ·
          refine ⟨2161607712835981984366649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23057148936917141166577589 2161607712835981984366649)
          ·
            refine ⟨1621205784626986488274987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161607712835981984366649 1621205784626986488274987)
            ·
              refine ⟨2431808676940479732412481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621205784626986488274987 2431808676940479732412481)
              ·
                refine ⟨1823856507705359799309361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431808676940479732412481 1823856507705359799309361)
                ·
                  refine ⟨1367892380779019849482021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1823856507705359799309361 1367892380779019849482021)
                  ·
                    refine ⟨256479821396066221777879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1367892380779019849482021 256479821396066221777879)
                    ·
                      rfl

theorem cell22_749239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_749239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749239 prefixEnd_749239 := by exact prefixLift 749239
  have htrace : WordTrace (prefixWord ++ tailWord_749239) baseStart_749239 baseEnd_749239 := by
    simpa [prefixWord, tailWord_749239, baseEnd_749239] using wordTrace_append hprefix tailTrace_749239
  have hstable : (prefixWord ++ tailWord_749239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749239).length < 2 ^ (prefixWord ++ tailWord_749239).sum := by decide
  have hdescent : baseEnd_749239 < baseStart_749239 := by decide
  rcases family_descends (prefixWord ++ tailWord_749239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749303 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 1, 3]
def baseStart_749303 : Nat := 118140960795 + 749303 * 2 ^ 59
def prefixEnd_749303 : Nat := 4983230072969 + 3 ^ 40 * 749303 * 2
def baseEnd_749303 : Nat := 256501729903991388177683

theorem tailTrace_749303 : CollatzResearch.WordTrace tailWord_749303 prefixEnd_749303 256501729903991388177683 := by
  unfold tailWord_749303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27329325604410676609236563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18219550402940451072824375 27329325604410676609236563)
  ·
    refine ⟨40993988406616014913854845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27329325604410676609236563 40993988406616014913854845)
    ·
      refine ⟨15372745652481005592695567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40993988406616014913854845 15372745652481005592695567)
      ·
        refine ⟨23059118478721508389043351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15372745652481005592695567 23059118478721508389043351)
        ·
          refine ⟨34588677718082262583565027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23059118478721508389043351 34588677718082262583565027)
          ·
            refine ⟨51883016577123393875347541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34588677718082262583565027 51883016577123393875347541)
            ·
              refine ⟨608004100513164771976729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 51883016577123393875347541 608004100513164771976729)
              ·
                refine ⟨456003075384873578982547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608004100513164771976729 456003075384873578982547)
                ·
                  refine ⟨684004613077310368473821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456003075384873578982547 684004613077310368473821)
                  ·
                    refine ⟨256501729903991388177683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684004613077310368473821 256501729903991388177683)
                    ·
                      rfl

theorem cell22_749303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_749303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749303 prefixEnd_749303 := by exact prefixLift 749303
  have htrace : WordTrace (prefixWord ++ tailWord_749303) baseStart_749303 baseEnd_749303 := by
    simpa [prefixWord, tailWord_749303, baseEnd_749303] using wordTrace_append hprefix tailTrace_749303
  have hstable : (prefixWord ++ tailWord_749303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749303).length < 2 ^ (prefixWord ++ tailWord_749303).sum := by decide
  have hdescent : baseEnd_749303 < baseStart_749303 := by decide
  rcases family_descends (prefixWord ++ tailWord_749303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749329 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_749329 : Nat := 118140960795 + 749329 * 2 ^ 59
def prefixEnd_749329 : Nat := 4983230072969 + 3 ^ 40 * 749329 * 2
def baseEnd_749329 : Nat := 256510630235335987027603

theorem tailTrace_749329 : CollatzResearch.WordTrace tailWord_749329 prefixEnd_749329 256510630235335987027603 := by
  unfold tailWord_749329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27330273902316483049683041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18220182601544322033122027 27330273902316483049683041)
  ·
    refine ⟨20497705426737362287262281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27330273902316483049683041 20497705426737362287262281)
    ·
      refine ⟨15373279070053021715446711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20497705426737362287262281 15373279070053021715446711)
      ·
        refine ⟨23059918605079532573170067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15373279070053021715446711 23059918605079532573170067)
        ·
          refine ⟨34589877907619298859755101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23059918605079532573170067 34589877907619298859755101)
          ·
            refine ⟨12971204215357237072408163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34589877907619298859755101 12971204215357237072408163)
            ·
              refine ⟨19456806323035855608612245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12971204215357237072408163 19456806323035855608612245)
              ·
                refine ⟨912037796392305731653699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19456806323035855608612245 912037796392305731653699)
                ·
                  refine ⟨1368056694588458597480549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912037796392305731653699 1368056694588458597480549)
                  ·
                    refine ⟨256510630235335987027603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368056694588458597480549 256510630235335987027603)
                    ·
                      rfl

theorem cell22_749329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_749329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749329 prefixEnd_749329 := by exact prefixLift 749329
  have htrace : WordTrace (prefixWord ++ tailWord_749329) baseStart_749329 baseEnd_749329 := by
    simpa [prefixWord, tailWord_749329, baseEnd_749329] using wordTrace_append hprefix tailTrace_749329
  have hstable : (prefixWord ++ tailWord_749329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749329).length < 2 ^ (prefixWord ++ tailWord_749329).sum := by decide
  have hdescent : baseEnd_749329 < baseStart_749329 := by decide
  rcases family_descends (prefixWord ++ tailWord_749329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749346 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_749346 : Nat := 118140960795 + 749346 * 2 ^ 59
def prefixEnd_749346 : Nat := 4983230072969 + 3 ^ 40 * 749346 * 2
def baseEnd_749346 : Nat := 256516449682753609352551

theorem tailTrace_749346 : CollatzResearch.WordTrace tailWord_749346 prefixEnd_749346 256516449682753609352551 := by
  unfold tailWord_749346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6832723485813723738262973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18220595962169929968701261 6832723485813723738262973)
  ·
    refine ⟨2562271307180146401848615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6832723485813723738262973 2562271307180146401848615)
    ·
      refine ⟨3843406960770219602772923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562271307180146401848615 3843406960770219602772923)
      ·
        refine ⟨5765110441155329404159385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843406960770219602772923 5765110441155329404159385)
        ·
          refine ⟨4323832830866497053119539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765110441155329404159385 4323832830866497053119539)
          ·
            refine ⟨6485749246299745579679309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323832830866497053119539 6485749246299745579679309)
            ·
              refine ⟨2432155967362404592379741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6485749246299745579679309 2432155967362404592379741)
              ·
                refine ⟨912058487760901722142403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2432155967362404592379741 912058487760901722142403)
                ·
                  refine ⟨1368087731641352583213605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912058487760901722142403 1368087731641352583213605)
                  ·
                    refine ⟨256516449682753609352551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368087731641352583213605 256516449682753609352551)
                    ·
                      rfl

theorem cell22_749346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_749346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749346 prefixEnd_749346 := by exact prefixLift 749346
  have htrace : WordTrace (prefixWord ++ tailWord_749346) baseStart_749346 baseEnd_749346 := by
    simpa [prefixWord, tailWord_749346, baseEnd_749346] using wordTrace_append hprefix tailTrace_749346
  have hstable : (prefixWord ++ tailWord_749346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749346).length < 2 ^ (prefixWord ++ tailWord_749346).sum := by decide
  have hdescent : baseEnd_749346 < baseStart_749346 := by decide
  rcases family_descends (prefixWord ++ tailWord_749346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749359 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 4, 3]
def baseStart_749359 : Nat := 118140960795 + 749359 * 2 ^ 59
def prefixEnd_749359 : Nat := 4983230072969 + 3 ^ 40 * 749359 * 2
def baseEnd_749359 : Nat := 256520899848425908777511

theorem tailTrace_749359 : CollatzResearch.WordTrace tailWord_749359 prefixEnd_749359 256520899848425908777511 := by
  unfold tailWord_749359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27331368092207798173275131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18220912061471865448850087 27331368092207798173275131)
  ·
    refine ⟨40997052138311697259912697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27331368092207798173275131 40997052138311697259912697)
    ·
      refine ⟨30747789103733772944934523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40997052138311697259912697 30747789103733772944934523)
      ·
        refine ⟨46121683655600659417401785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30747789103733772944934523 46121683655600659417401785)
        ·
          refine ⟨34591262741700494563051339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46121683655600659417401785 34591262741700494563051339)
          ·
            refine ⟨51886894112550741844577009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34591262741700494563051339 51886894112550741844577009)
            ·
              refine ⟨38915170584413056383432757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51886894112550741844577009 38915170584413056383432757)
              ·
                refine ⟨3648297242288724035946821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38915170584413056383432757 3648297242288724035946821)
                ·
                  refine ⟨684055732929135756740029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3648297242288724035946821 684055732929135756740029)
                  ·
                    refine ⟨256520899848425908777511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684055732929135756740029 256520899848425908777511)
                    ·
                      rfl

theorem cell22_749359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_749359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749359 prefixEnd_749359 := by exact prefixLift 749359
  have htrace : WordTrace (prefixWord ++ tailWord_749359) baseStart_749359 baseEnd_749359 := by
    simpa [prefixWord, tailWord_749359, baseEnd_749359] using wordTrace_append hprefix tailTrace_749359
  have hstable : (prefixWord ++ tailWord_749359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749359).length < 2 ^ (prefixWord ++ tailWord_749359).sum := by decide
  have hdescent : baseEnd_749359 < baseStart_749359 := by decide
  rcases family_descends (prefixWord ++ tailWord_749359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749361 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 4]
def baseStart_749361 : Nat := 118140960795 + 749361 * 2 ^ 59
def prefixEnd_749361 : Nat := 4983230072969 + 3 ^ 40 * 749361 * 2
def baseEnd_749361 : Nat := 85507194829766190075835

theorem tailTrace_749361 : CollatzResearch.WordTrace tailWord_749361 prefixEnd_749361 85507194829766190075835 := by
  unfold tailWord_749361
  simp only [CollatzResearch.WordTrace]
  refine ⟨27331441038200552514847937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18220960692133701676565291 27331441038200552514847937)
  ·
    refine ⟨20498580778650414386135953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27331441038200552514847937 20498580778650414386135953)
    ·
      refine ⟨15373935583987810789601965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20498580778650414386135953 15373935583987810789601965)
      ·
        refine ⟨5765225843995429046100737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15373935583987810789601965 5765225843995429046100737)
        ·
          refine ⟨4323919382996571784575553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765225843995429046100737 4323919382996571784575553)
          ·
            refine ⟨3242939537247428838431665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323919382996571784575553 3242939537247428838431665)
            ·
              refine ⟨2432204652935571628823749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242939537247428838431665 2432204652935571628823749)
              ·
                refine ⟨456038372425419680404453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2432204652935571628823749 456038372425419680404453)
                ·
                  refine ⟨85507194829766190075835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456038372425419680404453 85507194829766190075835)
                  ·
                    rfl

theorem cell22_749361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_749361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749361 prefixEnd_749361 := by exact prefixLift 749361
  have htrace : WordTrace (prefixWord ++ tailWord_749361) baseStart_749361 baseEnd_749361 := by
    simpa [prefixWord, tailWord_749361, baseEnd_749361] using wordTrace_append hprefix tailTrace_749361
  have hstable : (prefixWord ++ tailWord_749361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749361).length < 2 ^ (prefixWord ++ tailWord_749361).sum := by decide
  have hdescent : baseEnd_749361 < baseStart_749361 := by decide
  rcases family_descends (prefixWord ++ tailWord_749361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749468 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_749468 : Nat := 118140960795 + 749468 * 2 ^ 59
def prefixEnd_749468 : Nat := 4983230072969 + 3 ^ 40 * 749468 * 2
def baseEnd_749468 : Nat := 85519404258661985934059

theorem tailTrace_749468 : CollatzResearch.WordTrace tailWord_749468 prefixEnd_749468 85519404258661985934059 := by
  unfold tailWord_749468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13667671824406454894496529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18223562432541939859328705 13667671824406454894496529)
  ·
    refine ⟨10250753868304841170872397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13667671824406454894496529 10250753868304841170872397)
    ·
      refine ⟨3844032700614315439077149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10250753868304841170872397 3844032700614315439077149)
      ·
        refine ⟨1441512262730368289653931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3844032700614315439077149 1441512262730368289653931)
        ·
          refine ⟨2162268394095552434480897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441512262730368289653931 2162268394095552434480897)
          ·
            refine ⟨1621701295571664325860673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162268394095552434480897 1621701295571664325860673)
            ·
              refine ⟨1216275971678748244395505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621701295571664325860673 1216275971678748244395505)
              ·
                refine ⟨912206978759061183296629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216275971678748244395505 912206978759061183296629)
                ·
                  refine ⟨85519404258661985934059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 912206978759061183296629 85519404258661985934059)
                  ·
                    rfl

theorem cell22_749468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_749468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749468 prefixEnd_749468 := by exact prefixLift 749468
  have htrace : WordTrace (prefixWord ++ tailWord_749468) baseStart_749468 baseEnd_749468 := by
    simpa [prefixWord, tailWord_749468, baseEnd_749468] using wordTrace_append hprefix tailTrace_749468
  have hstable : (prefixWord ++ tailWord_749468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749468).length < 2 ^ (prefixWord ++ tailWord_749468).sum := by decide
  have hdescent : baseEnd_749468 < baseStart_749468 := by decide
  rcases family_descends (prefixWord ++ tailWord_749468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749511 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 4, 3]
def baseStart_749511 : Nat := 118140960795 + 749511 * 2 ^ 59
def prefixEnd_749511 : Nat := 4983230072969 + 3 ^ 40 * 749511 * 2
def baseEnd_749511 : Nat := 256572932554748178977045

theorem tailTrace_749511 : CollatzResearch.WordTrace tailWord_749511 prefixEnd_749511 256572932554748178977045 := by
  unfold tailWord_749511
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336911987657128132808387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224607991771418755205591 27336911987657128132808387)
  ·
    refine ⟨41005367981485692199212581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27336911987657128132808387 41005367981485692199212581)
    ·
      refine ⟨7688506496528567287352359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41005367981485692199212581 7688506496528567287352359)
      ·
        refine ⟨11532759744792850931028539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688506496528567287352359 11532759744792850931028539)
        ·
          refine ⟨17299139617189276396542809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532759744792850931028539 17299139617189276396542809)
          ·
            refine ⟨12974354712891957297407107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17299139617189276396542809 12974354712891957297407107)
            ·
              refine ⟨19461532069337935946110661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12974354712891957297407107 19461532069337935946110661)
              ·
                refine ⟨3649037263000862989895749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19461532069337935946110661 3649037263000862989895749)
                ·
                  refine ⟨684194486812661810605453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3649037263000862989895749 684194486812661810605453)
                  ·
                    refine ⟨256572932554748178977045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684194486812661810605453 256572932554748178977045)
                    ·
                      rfl

theorem cell22_749511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_749511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749511 prefixEnd_749511 := by exact prefixLift 749511
  have htrace : WordTrace (prefixWord ++ tailWord_749511) baseStart_749511 baseEnd_749511 := by
    simpa [prefixWord, tailWord_749511, baseEnd_749511] using wordTrace_append hprefix tailTrace_749511
  have hstable : (prefixWord ++ tailWord_749511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749511).length < 2 ^ (prefixWord ++ tailWord_749511).sum := by decide
  have hdescent : baseEnd_749511 < baseStart_749511 := by decide
  rcases family_descends (prefixWord ++ tailWord_749511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749558 : List Nat := [5, 1, 1, 1, 4, 1, 1, 8]
def baseStart_749558 : Nat := 118140960795 + 749558 * 2 ^ 59
def prefixEnd_749558 : Nat := 4983230072969 + 3 ^ 40 * 749558 * 2
def baseEnd_749558 : Nat := 28509891290583969227989

theorem tailTrace_749558 : CollatzResearch.WordTrace tailWord_749558 prefixEnd_749558 28509891290583969227989 := by
  unfold tailWord_749558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708664138655428447485583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18225750812324570106512885 1708664138655428447485583)
  ·
    refine ⟨2562996207983142671228375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708664138655428447485583 2562996207983142671228375)
    ·
      refine ⟨3844494311974714006842563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562996207983142671228375 3844494311974714006842563)
      ·
        refine ⟨5766741467962071010263845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844494311974714006842563 5766741467962071010263845)
        ·
          refine ⟨1081264025242888314424471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5766741467962071010263845 1081264025242888314424471)
          ·
            refine ⟨1621896037864332471636707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081264025242888314424471 1621896037864332471636707)
            ·
              refine ⟨2432844056796498707455061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621896037864332471636707 2432844056796498707455061)
              ·
                refine ⟨28509891290583969227989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2432844056796498707455061 28509891290583969227989)
                ·
                  rfl

theorem cell22_749558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_749558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749558 prefixEnd_749558 := by exact prefixLift 749558
  have htrace : WordTrace (prefixWord ++ tailWord_749558) baseStart_749558 baseEnd_749558 := by
    simpa [prefixWord, tailWord_749558, baseEnd_749558] using wordTrace_append hprefix tailTrace_749558
  have hstable : (prefixWord ++ tailWord_749558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749558).length < 2 ^ (prefixWord ++ tailWord_749558).sum := by decide
  have hdescent : baseEnd_749558 < baseStart_749558 := by decide
  rcases family_descends (prefixWord ++ tailWord_749558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749581 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 4]
def baseStart_749581 : Nat := 118140960795 + 749581 * 2 ^ 59
def prefixEnd_749581 : Nat := 4983230072969 + 3 ^ 40 * 749581 * 2
def baseEnd_749581 : Nat := 85532298328430443242277

theorem tailTrace_749581 : CollatzResearch.WordTrace tailWord_749581 prefixEnd_749581 85532298328430443242277 := by
  unfold tailWord_749581
  simp only [CollatzResearch.WordTrace]
  refine ⟨27339465097403530087856597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18226310064935686725237731 27339465097403530087856597)
  ·
    refine ⟨640768713220395236434139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27339465097403530087856597 640768713220395236434139)
    ·
      refine ⟨961153069830592854651209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640768713220395236434139 961153069830592854651209)
      ·
        refine ⟨720864802372944640988407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961153069830592854651209 720864802372944640988407)
        ·
          refine ⟨1081297203559416961482611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720864802372944640988407 1081297203559416961482611)
          ·
            refine ⟨1621945805339125442223917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081297203559416961482611 1621945805339125442223917)
            ·
              refine ⟨608229677002172040833969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621945805339125442223917 608229677002172040833969)
              ·
                refine ⟨456172257751629030625477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608229677002172040833969 456172257751629030625477)
                ·
                  refine ⟨85532298328430443242277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456172257751629030625477 85532298328430443242277)
                  ·
                    rfl

theorem cell22_749581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_749581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749581 prefixEnd_749581 := by exact prefixLift 749581
  have htrace : WordTrace (prefixWord ++ tailWord_749581) baseStart_749581 baseEnd_749581 := by
    simpa [prefixWord, tailWord_749581, baseEnd_749581] using wordTrace_append hprefix tailTrace_749581
  have hstable : (prefixWord ++ tailWord_749581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749581).length < 2 ^ (prefixWord ++ tailWord_749581).sum := by decide
  have hdescent : baseEnd_749581 < baseStart_749581 := by decide
  rcases family_descends (prefixWord ++ tailWord_749581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749678 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_749678 : Nat := 118140960795 + 749678 * 2 ^ 59
def prefixEnd_749678 : Nat := 4983230072969 + 3 ^ 40 * 749678 * 2
def baseEnd_749678 : Nat := 256630100067615410051533

theorem tailTrace_749678 : CollatzResearch.WordTrace tailWord_749678 prefixEnd_749678 256630100067615410051533 := by
  unfold tailWord_749678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417875372256514456767211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18228668652034743769425125 3417875372256514456767211)
  ·
    refine ⟨5126813058384771685150817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417875372256514456767211 5126813058384771685150817)
    ·
      refine ⟨3845109793788578763863113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5126813058384771685150817 3845109793788578763863113)
      ·
        refine ⟨2883832345341434072897335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845109793788578763863113 2883832345341434072897335)
        ·
          refine ⟨4325748518012151109346003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883832345341434072897335 4325748518012151109346003)
          ·
            refine ⟨6488622777018226664019005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325748518012151109346003 6488622777018226664019005)
            ·
              refine ⟨2433233541381834999007127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6488622777018226664019005 2433233541381834999007127)
              ·
                refine ⟨3649850312072752498510691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433233541381834999007127 3649850312072752498510691)
                ·
                  refine ⟨5474775468109128747766037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649850312072752498510691 5474775468109128747766037)
                  ·
                    refine ⟨256630100067615410051533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5474775468109128747766037 256630100067615410051533)
                    ·
                      rfl

theorem cell22_749678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_749678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749678 prefixEnd_749678 := by exact prefixLift 749678
  have htrace : WordTrace (prefixWord ++ tailWord_749678) baseStart_749678 baseEnd_749678 := by
    simpa [prefixWord, tailWord_749678, baseEnd_749678] using wordTrace_append hprefix tailTrace_749678
  have hstable : (prefixWord ++ tailWord_749678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749678).length < 2 ^ (prefixWord ++ tailWord_749678).sum := by decide
  have hdescent : baseEnd_749678 < baseStart_749678 := by decide
  rcases family_descends (prefixWord ++ tailWord_749678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749718 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_749718 : Nat := 118140960795 + 749718 * 2 ^ 59
def prefixEnd_749718 : Nat := 4983230072969 + 3 ^ 40 * 749718 * 2
def baseEnd_749718 : Nat := 256643792885068639051411

theorem tailTrace_749718 : CollatzResearch.WordTrace tailWord_749718 prefixEnd_749718 256643792885068639051411 := by
  unfold tailWord_749718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709028868619200155349613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18229641265271468323729205 1709028868619200155349613)
  ·
    refine ⟨640885825732200058256105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1709028868619200155349613 640885825732200058256105)
    ·
      refine ⟨480664369299150043692079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 640885825732200058256105 480664369299150043692079)
      ·
        refine ⟨720996553948725065538119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480664369299150043692079 720996553948725065538119)
        ·
          refine ⟨1081494830923087598307179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720996553948725065538119 1081494830923087598307179)
          ·
            refine ⟨1622242246384631397460769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081494830923087598307179 1622242246384631397460769)
            ·
              refine ⟨1216681684788473548095577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622242246384631397460769 1216681684788473548095577)
              ·
                refine ⟨912511263591355161071683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216681684788473548095577 912511263591355161071683)
                ·
                  refine ⟨1368766895387032741607525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912511263591355161071683 1368766895387032741607525)
                  ·
                    refine ⟨256643792885068639051411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368766895387032741607525 256643792885068639051411)
                    ·
                      rfl

theorem cell22_749718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_749718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749718 prefixEnd_749718 := by exact prefixLift 749718
  have htrace : WordTrace (prefixWord ++ tailWord_749718) baseStart_749718 baseEnd_749718 := by
    simpa [prefixWord, tailWord_749718, baseEnd_749718] using wordTrace_append hprefix tailTrace_749718
  have hstable : (prefixWord ++ tailWord_749718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749718).length < 2 ^ (prefixWord ++ tailWord_749718).sum := by decide
  have hdescent : baseEnd_749718 < baseStart_749718 := by decide
  rcases family_descends (prefixWord ++ tailWord_749718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749725 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_749725 : Nat := 118140960795 + 749725 * 2 ^ 59
def prefixEnd_749725 : Nat := 4983230072969 + 3 ^ 40 * 749725 * 2
def baseEnd_749725 : Nat := 256646189128122954126389

theorem tailTrace_749725 : CollatzResearch.WordTrace tailWord_749725 prefixEnd_749725 256646189128122954126389 := by
  unfold tailWord_749725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27344717208881842681098629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18229811472587895120732419 27344717208881842681098629)
  ·
    refine ⟨5127134476665345502705993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27344717208881842681098629 5127134476665345502705993)
    ·
      refine ⟨3845350857499009127029495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127134476665345502705993 3845350857499009127029495)
      ·
        refine ⟨5768026286248513690544243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845350857499009127029495 5768026286248513690544243)
        ·
          refine ⟨8652039429372770535816365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768026286248513690544243 8652039429372770535816365)
          ·
            refine ⟨3244514786014788950931137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8652039429372770535816365 3244514786014788950931137)
            ·
              refine ⟨2433386089511091713198353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244514786014788950931137 2433386089511091713198353)
              ·
                refine ⟨1825039567133318784898765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433386089511091713198353 1825039567133318784898765)
                ·
                  refine ⟨684389837674994544337037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1825039567133318784898765 684389837674994544337037)
                  ·
                    refine ⟨256646189128122954126389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684389837674994544337037 256646189128122954126389)
                    ·
                      rfl

theorem cell22_749725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_749725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749725 prefixEnd_749725 := by exact prefixLift 749725
  have htrace : WordTrace (prefixWord ++ tailWord_749725) baseStart_749725 baseEnd_749725 := by
    simpa [prefixWord, tailWord_749725, baseEnd_749725] using wordTrace_append hprefix tailTrace_749725
  have hstable : (prefixWord ++ tailWord_749725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749725).length < 2 ^ (prefixWord ++ tailWord_749725).sum := by decide
  have hdescent : baseEnd_749725 < baseStart_749725 := by decide
  rcases family_descends (prefixWord ++ tailWord_749725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749768 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_749768 : Nat := 118140960795 + 749768 * 2 ^ 59
def prefixEnd_749768 : Nat := 4983230072969 + 3 ^ 40 * 749768 * 2
def baseEnd_749768 : Nat := 256660908906885175301257

theorem tailTrace_749768 : CollatzResearch.WordTrace tailWord_749768 prefixEnd_749768 256660908906885175301257 := by
  unfold tailWord_749768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13673142773863030512456979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18230857031817374016609305 13673142773863030512456979)
  ·
    refine ⟨20509714160794545768685469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13673142773863030512456979 20509714160794545768685469)
    ·
      refine ⟨7691142810297954663257051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20509714160794545768685469 7691142810297954663257051)
      ·
        refine ⟨11536714215446931994885577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691142810297954663257051 11536714215446931994885577)
        ·
          refine ⟨8652535661585198996164183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11536714215446931994885577 8652535661585198996164183)
          ·
            refine ⟨12978803492377798494246275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652535661585198996164183 12978803492377798494246275)
            ·
              refine ⟨19468205238566697741369413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978803492377798494246275 19468205238566697741369413)
              ·
                refine ⟨3650288482231255826506765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19468205238566697741369413 3650288482231255826506765)
                ·
                  refine ⟨1368858180836720934940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3650288482231255826506765 1368858180836720934940037)
                  ·
                    refine ⟨256660908906885175301257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368858180836720934940037 256660908906885175301257)
                    ·
                      rfl

theorem cell22_749768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_749768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749768 prefixEnd_749768 := by exact prefixLift 749768
  have htrace : WordTrace (prefixWord ++ tailWord_749768) baseStart_749768 baseEnd_749768 := by
    simpa [prefixWord, tailWord_749768, baseEnd_749768] using wordTrace_append hprefix tailTrace_749768
  have hstable : (prefixWord ++ tailWord_749768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749768).length < 2 ^ (prefixWord ++ tailWord_749768).sum := by decide
  have hdescent : baseEnd_749768 < baseStart_749768 := by decide
  rcases family_descends (prefixWord ++ tailWord_749768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749772 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_749772 : Nat := 118140960795 + 749772 * 2 ^ 59
def prefixEnd_749772 : Nat := 4983230072969 + 3 ^ 40 * 749772 * 2
def baseEnd_749772 : Nat := 85554092729543499400415

theorem tailTrace_749772 : CollatzResearch.WordTrace tailWord_749772 prefixEnd_749772 85554092729543499400415 := by
  unfold tailWord_749772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13673215719855784854029785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18230954293141046472039713 13673215719855784854029785)
  ·
    refine ⟨10254911789891838640522339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13673215719855784854029785 10254911789891838640522339)
    ·
      refine ⟨15382367684837757960783509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254911789891838640522339 15382367684837757960783509)
      ·
        refine ⟨721048485226769904411727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15382367684837757960783509 721048485226769904411727)
        ·
          refine ⟨1081572727840154856617591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721048485226769904411727 1081572727840154856617591)
          ·
            refine ⟨1622359091760232284926387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081572727840154856617591 1622359091760232284926387)
            ·
              refine ⟨2433538637640348427389581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622359091760232284926387 2433538637640348427389581)
              ·
                refine ⟨912576989115130660271093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433538637640348427389581 912576989115130660271093)
                ·
                  refine ⟨85554092729543499400415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 912576989115130660271093 85554092729543499400415)
                  ·
                    rfl

theorem cell22_749772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_749772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749772 prefixEnd_749772 := by exact prefixLift 749772
  have htrace : WordTrace (prefixWord ++ tailWord_749772) baseStart_749772 baseEnd_749772 := by
    simpa [prefixWord, tailWord_749772, baseEnd_749772] using wordTrace_append hprefix tailTrace_749772
  have hstable : (prefixWord ++ tailWord_749772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749772).length < 2 ^ (prefixWord ++ tailWord_749772).sum := by decide
  have hdescent : baseEnd_749772 < baseStart_749772 := by decide
  rcases family_descends (prefixWord ++ tailWord_749772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749785 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_749785 : Nat := 118140960795 + 749785 * 2 ^ 59
def prefixEnd_749785 : Nat := 4983230072969 + 3 ^ 40 * 749785 * 2
def baseEnd_749785 : Nat := 256666728354302797626205

theorem tailTrace_749785 : CollatzResearch.WordTrace tailWord_749785 prefixEnd_749785 256666728354302797626205 := by
  unfold tailWord_749785
  simp only [CollatzResearch.WordTrace]
  refine ⟨27346905588664472928282809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18231270392442981952188539 27346905588664472928282809)
  ·
    refine ⟨20510179191498354696212107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27346905588664472928282809 20510179191498354696212107)
    ·
      refine ⟨30765268787247532044318161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20510179191498354696212107 30765268787247532044318161)
      ·
        refine ⟨23073951590435649033238621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30765268787247532044318161 23073951590435649033238621)
        ·
          refine ⟨8652731846413368387464483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23073951590435649033238621 8652731846413368387464483)
          ·
            refine ⟨12979097769620052581196725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652731846413368387464483 12979097769620052581196725)
            ·
              refine ⟨1216790415901879929487193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12979097769620052581196725 1216790415901879929487193)
              ·
                refine ⟨912592811926409947115395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216790415901879929487193 912592811926409947115395)
                ·
                  refine ⟨1368889217889614920673093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912592811926409947115395 1368889217889614920673093)
                  ·
                    refine ⟨256666728354302797626205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368889217889614920673093 256666728354302797626205)
                    ·
                      rfl

theorem cell22_749785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_749785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749785 prefixEnd_749785 := by exact prefixLift 749785
  have htrace : WordTrace (prefixWord ++ tailWord_749785) baseStart_749785 baseEnd_749785 := by
    simpa [prefixWord, tailWord_749785, baseEnd_749785] using wordTrace_append hprefix tailTrace_749785
  have hstable : (prefixWord ++ tailWord_749785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749785).length < 2 ^ (prefixWord ++ tailWord_749785).sum := by decide
  have hdescent : baseEnd_749785 < baseStart_749785 := by decide
  rcases family_descends (prefixWord ++ tailWord_749785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749802 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_749802 : Nat := 118140960795 + 749802 * 2 ^ 59
def prefixEnd_749802 : Nat := 4983230072969 + 3 ^ 40 * 749802 * 2
def baseEnd_749802 : Nat := 256672547801720419951153

theorem tailTrace_749802 : CollatzResearch.WordTrace tailWord_749802 prefixEnd_749802 256672547801720419951153 := by
  unfold tailWord_749802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836881407400721207912915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18231683753068589887767773 6836881407400721207912915)
  ·
    refine ⟨10255322111101081811869373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836881407400721207912915 10255322111101081811869373)
    ·
      refine ⟨3845745791662905679451015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10255322111101081811869373 3845745791662905679451015)
      ·
        refine ⟨5768618687494358519176523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845745791662905679451015 5768618687494358519176523)
        ·
          refine ⟨8652928031241537778764785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768618687494358519176523 8652928031241537778764785)
          ·
            refine ⟨6489696023431153334073589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8652928031241537778764785 6489696023431153334073589)
            ·
              refine ⟨608409002196670625069399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6489696023431153334073589 608409002196670625069399)
              ·
                refine ⟨912613503295005937604099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608409002196670625069399 912613503295005937604099)
                ·
                  refine ⟨1368920254942508906406149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912613503295005937604099 1368920254942508906406149)
                  ·
                    refine ⟨256672547801720419951153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368920254942508906406149 256672547801720419951153)
                    ·
                      rfl

theorem cell22_749802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_749802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749802 prefixEnd_749802 := by exact prefixLift 749802
  have htrace : WordTrace (prefixWord ++ tailWord_749802) baseStart_749802 baseEnd_749802 := by
    simpa [prefixWord, tailWord_749802, baseEnd_749802] using wordTrace_append hprefix tailTrace_749802
  have hstable : (prefixWord ++ tailWord_749802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749802).length < 2 ^ (prefixWord ++ tailWord_749802).sum := by decide
  have hdescent : baseEnd_749802 < baseStart_749802 := by decide
  rcases family_descends (prefixWord ++ tailWord_749802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749832 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_749832 : Nat := 118140960795 + 749832 * 2 ^ 59
def prefixEnd_749832 : Nat := 4983230072969 + 3 ^ 40 * 749832 * 2
def baseEnd_749832 : Nat := 256682817414810341701061

theorem tailTrace_749832 : CollatzResearch.WordTrace tailWord_749832 prefixEnd_749832 256682817414810341701061 := by
  unfold tailWord_749832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674309909747099977621875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18232413212996133303495833 13674309909747099977621875)
  ·
    refine ⟨20511464864620649966432813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13674309909747099977621875 20511464864620649966432813)
    ·
      refine ⟨7691799324232743737412305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20511464864620649966432813 7691799324232743737412305)
      ·
        refine ⟨5768849493174557803059229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691799324232743737412305 5768849493174557803059229)
        ·
          refine ⟨2163318559940459176147211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5768849493174557803059229 2163318559940459176147211)
          ·
            refine ⟨3244977839910688764220817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163318559940459176147211 3244977839910688764220817)
            ·
              refine ⟨2433733379933016573165613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244977839910688764220817 2433733379933016573165613)
              ·
                refine ⟨912650017474881214937105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433733379933016573165613 912650017474881214937105)
                ·
                  refine ⟨684487513106160911202829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912650017474881214937105 684487513106160911202829)
                  ·
                    refine ⟨256682817414810341701061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684487513106160911202829 256682817414810341701061)
                    ·
                      rfl

theorem cell22_749832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_749832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749832 prefixEnd_749832 := by exact prefixLift 749832
  have htrace : WordTrace (prefixWord ++ tailWord_749832) baseStart_749832 baseEnd_749832 := by
    simpa [prefixWord, tailWord_749832, baseEnd_749832] using wordTrace_append hprefix tailTrace_749832
  have hstable : (prefixWord ++ tailWord_749832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749832).length < 2 ^ (prefixWord ++ tailWord_749832).sum := by decide
  have hdescent : baseEnd_749832 < baseStart_749832 := by decide
  rcases family_descends (prefixWord ++ tailWord_749832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749847 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 2, 4]
def baseStart_749847 : Nat := 118140960795 + 749847 * 2 ^ 59
def prefixEnd_749847 : Nat := 4983230072969 + 3 ^ 40 * 749847 * 2
def baseEnd_749847 : Nat := 256687952221355302576015

theorem tailTrace_749847 : CollatzResearch.WordTrace tailWord_749847 prefixEnd_749847 256687952221355302576015 := by
  unfold tailWord_749847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27349166914439857517039795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18232777942959905011359863 27349166914439857517039795)
  ·
    refine ⟨41023750371659786275559693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27349166914439857517039795 41023750371659786275559693)
    ·
      refine ⟨15383906389372419853334885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41023750371659786275559693 15383906389372419853334885)
      ·
        refine ⟨2884482448007328722500291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15383906389372419853334885 2884482448007328722500291)
        ·
          refine ⟨4326723672010993083750437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884482448007328722500291 4326723672010993083750437)
          ·
            refine ⟨811260688502061203203207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4326723672010993083750437 811260688502061203203207)
            ·
              refine ⟨1216891032753091804804811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811260688502061203203207 1216891032753091804804811)
              ·
                refine ⟨1825336549129637707207217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216891032753091804804811 1825336549129637707207217)
                ·
                  refine ⟨1369002411847228280405413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825336549129637707207217 1369002411847228280405413)
                  ·
                    refine ⟨256687952221355302576015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1369002411847228280405413 256687952221355302576015)
                    ·
                      rfl

theorem cell22_749847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_749847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749847 prefixEnd_749847 := by exact prefixLift 749847
  have htrace : WordTrace (prefixWord ++ tailWord_749847) baseStart_749847 baseEnd_749847 := by
    simpa [prefixWord, tailWord_749847, baseEnd_749847] using wordTrace_append hprefix tailTrace_749847
  have hstable : (prefixWord ++ tailWord_749847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749847).length < 2 ^ (prefixWord ++ tailWord_749847).sum := by decide
  have hdescent : baseEnd_749847 < baseStart_749847 := by decide
  rcases family_descends (prefixWord ++ tailWord_749847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749866 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_749866 : Nat := 118140960795 + 749866 * 2 ^ 59
def prefixEnd_749866 : Nat := 4983230072969 + 3 ^ 40 * 749866 * 2
def baseEnd_749866 : Nat := 256694456309645586350957

theorem tailTrace_749866 : CollatzResearch.WordTrace tailWord_749866 prefixEnd_749866 256694456309645586350957 := by
  unfold tailWord_749866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837464975342755940495363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18233239934247349174654301 6837464975342755940495363)
  ·
    refine ⟨10256197463014133910743045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6837464975342755940495363 10256197463014133910743045)
    ·
      refine ⟨1923037024315150108264321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10256197463014133910743045 1923037024315150108264321)
      ·
        refine ⟨1442277768236362581198241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1923037024315150108264321 1442277768236362581198241)
        ·
          refine ⟨1081708326177271935898681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442277768236362581198241 1081708326177271935898681)
          ·
            refine ⟨811281244632953951924011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081708326177271935898681 811281244632953951924011)
            ·
              refine ⟨1216921866949430927886017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811281244632953951924011 1216921866949430927886017)
              ·
                refine ⟨912691400212073195914513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216921866949430927886017 912691400212073195914513)
                ·
                  refine ⟨684518550159054896935885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912691400212073195914513 684518550159054896935885)
                  ·
                    refine ⟨256694456309645586350957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684518550159054896935885 256694456309645586350957)
                    ·
                      rfl

theorem cell22_749866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_749866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749866 prefixEnd_749866 := by exact prefixLift 749866
  have htrace : WordTrace (prefixWord ++ tailWord_749866) baseStart_749866 baseEnd_749866 := by
    simpa [prefixWord, tailWord_749866, baseEnd_749866] using wordTrace_append hprefix tailTrace_749866
  have hstable : (prefixWord ++ tailWord_749866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749866).length < 2 ^ (prefixWord ++ tailWord_749866).sum := by decide
  have hdescent : baseEnd_749866 < baseStart_749866 := by decide
  rcases family_descends (prefixWord ++ tailWord_749866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749877 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_749877 : Nat := 118140960795 + 749877 * 2 ^ 59
def prefixEnd_749877 : Nat := 4983230072969 + 3 ^ 40 * 749877 * 2
def baseEnd_749877 : Nat := 256698221834445224325923

theorem tailTrace_749877 : CollatzResearch.WordTrace tailWord_749877 prefixEnd_749877 256698221834445224325923 := by
  unfold tailWord_749877
  simp only [CollatzResearch.WordTrace]
  refine ⟨27350261104331172640631885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18233507402887448427087923 27350261104331172640631885)
  ·
    refine ⟨10256347914124189740236957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27350261104331172640631885 10256347914124189740236957)
    ·
      refine ⟨3846130467796571152588859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10256347914124189740236957 3846130467796571152588859)
      ·
        refine ⟨5769195701694856728883289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846130467796571152588859 5769195701694856728883289)
        ·
          refine ⟨4326896776271142546662467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5769195701694856728883289 4326896776271142546662467)
          ·
            refine ⟨6490345164406713819993701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326896776271142546662467 6490345164406713819993701)
            ·
              refine ⟨1216939718326258841248819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6490345164406713819993701 1216939718326258841248819)
              ·
                refine ⟨1825409577489388261873229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216939718326258841248819 1825409577489388261873229)
                ·
                  refine ⟨684528591558520598202461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1825409577489388261873229 684528591558520598202461)
                  ·
                    refine ⟨256698221834445224325923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684528591558520598202461 256698221834445224325923)
                    ·
                      rfl

theorem cell22_749877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_749877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749877 prefixEnd_749877 := by exact prefixLift 749877
  have htrace : WordTrace (prefixWord ++ tailWord_749877) baseStart_749877 baseEnd_749877 := by
    simpa [prefixWord, tailWord_749877, baseEnd_749877] using wordTrace_append hprefix tailTrace_749877
  have hstable : (prefixWord ++ tailWord_749877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749877).length < 2 ^ (prefixWord ++ tailWord_749877).sum := by decide
  have hdescent : baseEnd_749877 < baseStart_749877 := by decide
  rcases family_descends (prefixWord ++ tailWord_749877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749888 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_749888 : Nat := 118140960795 + 749888 * 2 ^ 59
def prefixEnd_749888 : Nat := 4983230072969 + 3 ^ 40 * 749888 * 2
def baseEnd_749888 : Nat := 256701987359244862300889

theorem tailTrace_749888 : CollatzResearch.WordTrace tailWord_749888 prefixEnd_749888 256701987359244862300889 := by
  unfold tailWord_749888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675331153645660759641159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18233774871527547679521545 13675331153645660759641159)
  ·
    refine ⟨20512996730468491139461739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13675331153645660759641159 20512996730468491139461739)
    ·
      refine ⟨30769495095702736709192609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20512996730468491139461739 30769495095702736709192609)
      ·
        refine ⟨23077121321777052531894457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30769495095702736709192609 23077121321777052531894457)
        ·
          refine ⟨17307840991332789398920843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23077121321777052531894457 17307840991332789398920843)
          ·
            refine ⟨25961761486999184098381265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17307840991332789398920843 25961761486999184098381265)
            ·
              refine ⟨19471321115249388073785949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25961761486999184098381265 19471321115249388073785949)
              ·
                refine ⟨7301745418218520527669731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19471321115249388073785949 7301745418218520527669731)
                ·
                  refine ⟨10952618127327780791504597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301745418218520527669731 10952618127327780791504597)
                  ·
                    refine ⟨256701987359244862300889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10952618127327780791504597 256701987359244862300889)
                    ·
                      rfl

theorem cell22_749888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_749888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749888 prefixEnd_749888 := by exact prefixLift 749888
  have htrace : WordTrace (prefixWord ++ tailWord_749888) baseStart_749888 baseEnd_749888 := by
    simpa [prefixWord, tailWord_749888, baseEnd_749888] using wordTrace_append hprefix tailTrace_749888
  have hstable : (prefixWord ++ tailWord_749888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749888).length < 2 ^ (prefixWord ++ tailWord_749888).sum := by decide
  have hdescent : baseEnd_749888 < baseStart_749888 := by decide
  rcases family_descends (prefixWord ++ tailWord_749888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749984 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_749984 : Nat := 118140960795 + 749984 * 2 ^ 59
def prefixEnd_749984 : Nat := 4983230072969 + 3 ^ 40 * 749984 * 2
def baseEnd_749984 : Nat := 256734850121132611900595

theorem tailTrace_749984 : CollatzResearch.WordTrace tailWord_749984 prefixEnd_749984 256734850121132611900595 := by
  unfold tailWord_749984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677081857471764957388503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18236109143295686609851337 13677081857471764957388503)
  ·
    refine ⟨20515622786207647436082755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13677081857471764957388503 20515622786207647436082755)
    ·
      refine ⟨30773434179311471154124133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20515622786207647436082755 30773434179311471154124133)
      ·
        refine ⟨5770018908620900841398275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30773434179311471154124133 5770018908620900841398275)
        ·
          refine ⟨8655028362931351262097413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770018908620900841398275 8655028362931351262097413)
          ·
            refine ⟨1622817818049628361643265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8655028362931351262097413 1622817818049628361643265)
            ·
              refine ⟨1217113363537221271232449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622817818049628361643265 1217113363537221271232449)
              ·
                refine ⟨912835022652915953424337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217113363537221271232449 912835022652915953424337)
                ·
                  refine ⟨684626266989686965068253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912835022652915953424337 684626266989686965068253)
                  ·
                    refine ⟨256734850121132611900595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684626266989686965068253 256734850121132611900595)
                    ·
                      rfl

theorem cell22_749984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_749984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_749984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_749984 prefixEnd_749984 := by exact prefixLift 749984
  have htrace : WordTrace (prefixWord ++ tailWord_749984) baseStart_749984 baseEnd_749984 := by
    simpa [prefixWord, tailWord_749984, baseEnd_749984] using wordTrace_append hprefix tailTrace_749984
  have hstable : (prefixWord ++ tailWord_749984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749984).length < 2 ^ (prefixWord ++ tailWord_749984).sum := by decide
  have hdescent : baseEnd_749984 < baseStart_749984 := by decide
  rcases family_descends (prefixWord ++ tailWord_749984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750104 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_750104 : Nat := 118140960795 + 750104 * 2 ^ 59
def prefixEnd_750104 : Nat := 4983230072969 + 3 ^ 40 * 750104 * 2
def baseEnd_750104 : Nat := 85591976191164099633409

theorem tailTrace_750104 : CollatzResearch.WordTrace tailWord_750104 prefixEnd_750104 85591976191164099633409 := by
  unfold tailWord_750104
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679270237254395204572683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18239026983005860272763577 13679270237254395204572683)
  ·
    refine ⟨20518905355881592806859025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13679270237254395204572683 20518905355881592806859025)
    ·
      refine ⟨15389179016911194605144269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20518905355881592806859025 15389179016911194605144269)
      ·
        refine ⟨5770942131341697976929101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15389179016911194605144269 5770942131341697976929101)
        ·
          refine ⟨2164103299253136741348413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5770942131341697976929101 2164103299253136741348413)
          ·
            refine ⟨811538737219926278005655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2164103299253136741348413 811538737219926278005655)
            ·
              refine ⟨1217308105829889417008483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811538737219926278005655 1217308105829889417008483)
              ·
                refine ⟨1825962158744834125512725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217308105829889417008483 1825962158744834125512725)
                ·
                  refine ⟨85591976191164099633409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1825962158744834125512725 85591976191164099633409)
                  ·
                    rfl

theorem cell22_750104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_750104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750104 prefixEnd_750104 := by exact prefixLift 750104
  have htrace : WordTrace (prefixWord ++ tailWord_750104) baseStart_750104 baseEnd_750104 := by
    simpa [prefixWord, tailWord_750104, baseEnd_750104] using wordTrace_append hprefix tailTrace_750104
  have hstable : (prefixWord ++ tailWord_750104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750104).length < 2 ^ (prefixWord ++ tailWord_750104).sum := by decide
  have hdescent : baseEnd_750104 < baseStart_750104 := by decide
  rcases family_descends (prefixWord ++ tailWord_750104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750162 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_750162 : Nat := 118140960795 + 750162 * 2 ^ 59
def prefixEnd_750162 : Nat := 4983230072969 + 3 ^ 40 * 750162 * 2
def baseEnd_750162 : Nat := 256795783158799480950049

theorem tailTrace_750162 : CollatzResearch.WordTrace tailWord_750162 prefixEnd_750162 256795783158799480950049 := by
  unfold tailWord_750162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840163977074666578689185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18240437272199110876504493 6840163977074666578689185)
  ·
    refine ⟨5130122982805999934016889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6840163977074666578689185 5130122982805999934016889)
    ·
      refine ⟨3847592237104499950512667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5130122982805999934016889 3847592237104499950512667)
      ·
        refine ⟨5771388355656749925769001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847592237104499950512667 5771388355656749925769001)
        ·
          refine ⟨4328541266742562444326751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771388355656749925769001 4328541266742562444326751)
          ·
            refine ⟨6492811900113843666490127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328541266742562444326751 6492811900113843666490127)
            ·
              refine ⟨9739217850170765499735191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492811900113843666490127 9739217850170765499735191)
              ·
                refine ⟨14608826775256148249602787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739217850170765499735191 14608826775256148249602787)
                ·
                  refine ⟨21913240162884222374404181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14608826775256148249602787 21913240162884222374404181)
                  ·
                    refine ⟨256795783158799480950049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21913240162884222374404181 256795783158799480950049)
                    ·
                      rfl

theorem cell22_750162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_750162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750162 prefixEnd_750162 := by exact prefixLift 750162
  have htrace : WordTrace (prefixWord ++ tailWord_750162) baseStart_750162 baseEnd_750162 := by
    simpa [prefixWord, tailWord_750162, baseEnd_750162] using wordTrace_append hprefix tailTrace_750162
  have hstable : (prefixWord ++ tailWord_750162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750162).length < 2 ^ (prefixWord ++ tailWord_750162).sum := by decide
  have hdescent : baseEnd_750162 < baseStart_750162 := by decide
  rcases family_descends (prefixWord ++ tailWord_750162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750181 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_750181 : Nat := 118140960795 + 750181 * 2 ^ 59
def prefixEnd_750181 : Nat := 4983230072969 + 3 ^ 40 * 750181 * 2
def baseEnd_750181 : Nat := 256802287247089764724991

theorem tailTrace_750181 : CollatzResearch.WordTrace tailWord_750181 prefixEnd_750181 256802287247089764724991 := by
  unfold tailWord_750181
  simp only [CollatzResearch.WordTrace]
  refine ⟨27361348895229832559698397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18240899263486555039798931 27361348895229832559698397)
  ·
    refine ⟨10260505835711187209886899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27361348895229832559698397 10260505835711187209886899)
    ·
      refine ⟨15390758753566780814830349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10260505835711187209886899 15390758753566780814830349)
      ·
        refine ⟨5771534532587542805561381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15390758753566780814830349 5771534532587542805561381)
        ·
          refine ⟨1082162724860164276042759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5771534532587542805561381 1082162724860164276042759)
          ·
            refine ⟨1623244087290246414064139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082162724860164276042759 1623244087290246414064139)
            ·
              refine ⟨2434866130935369621096209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623244087290246414064139 2434866130935369621096209)
              ·
                refine ⟨1826149598201527215822157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434866130935369621096209 1826149598201527215822157)
                ·
                  refine ⟨684806099325572705933309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1826149598201527215822157 684806099325572705933309)
                  ·
                    refine ⟨256802287247089764724991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684806099325572705933309 256802287247089764724991)
                    ·
                      rfl

theorem cell22_750181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_750181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750181 prefixEnd_750181 := by exact prefixLift 750181
  have htrace : WordTrace (prefixWord ++ tailWord_750181) baseStart_750181 baseEnd_750181 := by
    simpa [prefixWord, tailWord_750181, baseEnd_750181] using wordTrace_append hprefix tailTrace_750181
  have hstable : (prefixWord ++ tailWord_750181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750181).length < 2 ^ (prefixWord ++ tailWord_750181).sum := by decide
  have hdescent : baseEnd_750181 < baseStart_750181 := by decide
  rcases family_descends (prefixWord ++ tailWord_750181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_750207 : Nat := 118140960795 + 750207 * 2 ^ 59
def prefixEnd_750207 : Nat := 4983230072969 + 3 ^ 40 * 750207 * 2
def baseEnd_750207 : Nat := 256811187578434363574911

theorem tailTrace_750207 : CollatzResearch.WordTrace tailWord_750207 prefixEnd_750207 256811187578434363574911 := by
  unfold tailWord_750207
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362297193135639000144875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18241531462090426000096583 27362297193135639000144875)
  ·
    refine ⟨41043445789703458500217313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27362297193135639000144875 41043445789703458500217313)
    ·
      refine ⟨30782584342277593875162985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41043445789703458500217313 30782584342277593875162985)
      ·
        refine ⟨23086938256708195406372239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30782584342277593875162985 23086938256708195406372239)
        ·
          refine ⟨34630407385062293109558359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23086938256708195406372239 34630407385062293109558359)
          ·
            refine ⟨51945611077593439664337539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34630407385062293109558359 51945611077593439664337539)
            ·
              refine ⟨77918416616390159496506309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51945611077593439664337539 77918416616390159496506309)
              ·
                refine ⟨14609703115573154905594933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77918416616390159496506309 14609703115573154905594933)
                ·
                  refine ⟨1369659667084983272399525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14609703115573154905594933 1369659667084983272399525)
                  ·
                    refine ⟨256811187578434363574911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1369659667084983272399525 256811187578434363574911)
                    ·
                      rfl

theorem cell22_750207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_750207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750207 prefixEnd_750207 := by exact prefixLift 750207
  have htrace : WordTrace (prefixWord ++ tailWord_750207) baseStart_750207 baseEnd_750207 := by
    simpa [prefixWord, tailWord_750207, baseEnd_750207] using wordTrace_append hprefix tailTrace_750207
  have hstable : (prefixWord ++ tailWord_750207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750207).length < 2 ^ (prefixWord ++ tailWord_750207).sum := by decide
  have hdescent : baseEnd_750207 < baseStart_750207 := by decide
  rcases family_descends (prefixWord ++ tailWord_750207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750228 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_750228 : Nat := 118140960795 + 750228 * 2 ^ 59
def prefixEnd_750228 : Nat := 4983230072969 + 3 ^ 40 * 750228 * 2
def baseEnd_750228 : Nat := 85606125435865769599949

theorem tailTrace_750228 : CollatzResearch.WordTrace tailWord_750228 prefixEnd_750228 85606125435865769599949 := by
  unfold tailWord_750228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13681531563029779793329669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18242042084039706391106225 13681531563029779793329669)
  ·
    refine ⟨2565287168068083711249313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13681531563029779793329669 2565287168068083711249313)
    ·
      refine ⟨1923965376051062783436985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2565287168068083711249313 1923965376051062783436985)
      ·
        refine ⟨1442974032038297087577739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1923965376051062783436985 1442974032038297087577739)
        ·
          refine ⟨2164461048057445631366609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442974032038297087577739 2164461048057445631366609)
          ·
            refine ⟨1623345786043084223524957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2164461048057445631366609 1623345786043084223524957)
            ·
              refine ⟨608754669766156583821859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1623345786043084223524957 608754669766156583821859)
              ·
                refine ⟨913132004649234875732789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608754669766156583821859 913132004649234875732789)
                ·
                  refine ⟨85606125435865769599949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913132004649234875732789 85606125435865769599949)
                  ·
                    rfl

theorem cell22_750228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_750228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750228 prefixEnd_750228 := by exact prefixLift 750228
  have htrace : WordTrace (prefixWord ++ tailWord_750228) baseStart_750228 baseEnd_750228 := by
    simpa [prefixWord, tailWord_750228, baseEnd_750228] using wordTrace_append hprefix tailTrace_750228
  have hstable : (prefixWord ++ tailWord_750228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750228).length < 2 ^ (prefixWord ++ tailWord_750228).sum := by decide
  have hdescent : baseEnd_750228 < baseStart_750228 := by decide
  rcases family_descends (prefixWord ++ tailWord_750228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750269 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_750269 : Nat := 118140960795 + 750269 * 2 ^ 59
def prefixEnd_750269 : Nat := 4983230072969 + 3 ^ 40 * 750269 * 2
def baseEnd_750269 : Nat := 256832411445486868524721

theorem tailTrace_750269 : CollatzResearch.WordTrace tailWord_750269 prefixEnd_750269 256832411445486868524721 := by
  unfold tailWord_750269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27364558518911023588901861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18243039012607349059267907 27364558518911023588901861)
  ·
    refine ⟨5130854722295816922919099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27364558518911023588901861 5130854722295816922919099)
    ·
      refine ⟨7696282083443725384378649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5130854722295816922919099 7696282083443725384378649)
      ·
        refine ⟨5772211562582794038283987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7696282083443725384378649 5772211562582794038283987)
        ·
          refine ⟨8658317343874191057425981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772211562582794038283987 8658317343874191057425981)
          ·
            refine ⟨3246869003952821646534743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8658317343874191057425981 3246869003952821646534743)
            ·
              refine ⟨4870303505929232469802115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246869003952821646534743 4870303505929232469802115)
              ·
                refine ⟨7305455258893848704703173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870303505929232469802115 7305455258893848704703173)
                ·
                  refine ⟨1369772861042596632131845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7305455258893848704703173 1369772861042596632131845)
                  ·
                    refine ⟨256832411445486868524721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1369772861042596632131845 256832411445486868524721)
                    ·
                      rfl

theorem cell22_750269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_750269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750269 prefixEnd_750269 := by exact prefixLift 750269
  have htrace : WordTrace (prefixWord ++ tailWord_750269) baseStart_750269 baseEnd_750269 := by
    simpa [prefixWord, tailWord_750269, baseEnd_750269] using wordTrace_append hprefix tailTrace_750269
  have hstable : (prefixWord ++ tailWord_750269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750269).length < 2 ^ (prefixWord ++ tailWord_750269).sum := by decide
  have hdescent : baseEnd_750269 < baseStart_750269 := by decide
  rcases family_descends (prefixWord ++ tailWord_750269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750284 : List Nat := [2, 2, 1, 5, 1, 1, 1, 9]
def baseStart_750284 : Nat := 118140960795 + 750284 * 2 ^ 59
def prefixEnd_750284 : Nat := 4983230072969 + 3 ^ 40 * 750284 * 2
def baseEnd_750284 : Nat := 28537505139114647711075

theorem tailTrace_750284 : CollatzResearch.WordTrace tailWord_750284 prefixEnd_750284 28537505139114647711075 := by
  unfold tailWord_750284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682552806928340575348953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18243403742571120767131937 13682552806928340575348953)
  ·
    refine ⟨10261914605196255431511715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13682552806928340575348953 10261914605196255431511715)
    ·
      refine ⟨15392871907794383147267573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10261914605196255431511715 15392871907794383147267573)
      ·
        refine ⟨1443081741355723420056335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15392871907794383147267573 1443081741355723420056335)
        ·
          refine ⟨2164622612033585130084503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443081741355723420056335 2164622612033585130084503)
          ·
            refine ⟨3246933918050377695126755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164622612033585130084503 3246933918050377695126755)
            ·
              refine ⟨4870400877075566542690133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246933918050377695126755 4870400877075566542690133)
              ·
                refine ⟨28537505139114647711075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4870400877075566542690133 28537505139114647711075)
                ·
                  rfl

theorem cell22_750284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_750284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750284 prefixEnd_750284 := by exact prefixLift 750284
  have htrace : WordTrace (prefixWord ++ tailWord_750284) baseStart_750284 baseEnd_750284 := by
    simpa [prefixWord, tailWord_750284, baseEnd_750284] using wordTrace_append hprefix tailTrace_750284
  have hstable : (prefixWord ++ tailWord_750284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750284).length < 2 ^ (prefixWord ++ tailWord_750284).sum := by decide
  have hdescent : baseEnd_750284 < baseStart_750284 := by decide
  rcases family_descends (prefixWord ++ tailWord_750284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750324 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_750324 : Nat := 118140960795 + 750324 * 2 ^ 59
def prefixEnd_750324 : Nat := 4983230072969 + 3 ^ 40 * 750324 * 2
def baseEnd_750324 : Nat := 85617079689828352799851

theorem tailTrace_750324 : CollatzResearch.WordTrace tailWord_750324 prefixEnd_750324 85617079689828352799851 := by
  unfold tailWord_750324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683282266855883991077013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18244376355807845321436017 13683282266855883991077013)
  ·
    refine ⟨641403856258869562081735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13683282266855883991077013 641403856258869562081735)
    ·
      refine ⟨962105784388304343122603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641403856258869562081735 962105784388304343122603)
      ·
        refine ⟨1443158676582456514683905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962105784388304343122603 1443158676582456514683905)
        ·
          refine ⟨1082369007436842386012929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1443158676582456514683905 1082369007436842386012929)
          ·
            refine ⟨811776755577631789509697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082369007436842386012929 811776755577631789509697)
            ·
              refine ⟨608832566683223842132273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811776755577631789509697 608832566683223842132273)
              ·
                refine ⟨456624425012417881599205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608832566683223842132273 456624425012417881599205)
                ·
                  refine ⟨85617079689828352799851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456624425012417881599205 85617079689828352799851)
                  ·
                    rfl

theorem cell22_750324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_750324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750324 prefixEnd_750324 := by exact prefixLift 750324
  have htrace : WordTrace (prefixWord ++ tailWord_750324) baseStart_750324 baseEnd_750324 := by
    simpa [prefixWord, tailWord_750324, baseEnd_750324] using wordTrace_append hprefix tailTrace_750324
  have hstable : (prefixWord ++ tailWord_750324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750324).length < 2 ^ (prefixWord ++ tailWord_750324).sum := by decide
  have hdescent : baseEnd_750324 < baseStart_750324 := by decide
  rcases family_descends (prefixWord ++ tailWord_750324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750333 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_750333 : Nat := 118140960795 + 750333 * 2 ^ 59
def prefixEnd_750333 : Nat := 4983230072969 + 3 ^ 40 * 750333 * 2
def baseEnd_750333 : Nat := 256854319953412034924525

theorem tailTrace_750333 : CollatzResearch.WordTrace tailWord_750333 prefixEnd_750333 256854319953412034924525 := by
  unfold tailWord_750333
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366892790679162519231653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18244595193786108346154435 27366892790679162519231653)
  ·
    refine ⟨5131292398252342972355935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27366892790679162519231653 5131292398252342972355935)
    ·
      refine ⟨7696938597378514458533903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5131292398252342972355935 7696938597378514458533903)
      ·
        refine ⟨11545407896067771687800855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696938597378514458533903 11545407896067771687800855)
        ·
          refine ⟨17318111844101657531701283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11545407896067771687800855 17318111844101657531701283)
          ·
            refine ⟨25977167766152486297551925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318111844101657531701283 25977167766152486297551925)
            ·
              refine ⟨2435359478076795590395493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25977167766152486297551925 2435359478076795590395493)
              ·
                refine ⟨456629902139399173199155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2435359478076795590395493 456629902139399173199155)
                ·
                  refine ⟨684944853209098759798733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456629902139399173199155 684944853209098759798733)
                  ·
                    refine ⟨256854319953412034924525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684944853209098759798733 256854319953412034924525)
                    ·
                      rfl

theorem cell22_750333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_750333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750333 prefixEnd_750333 := by exact prefixLift 750333
  have htrace : WordTrace (prefixWord ++ tailWord_750333) baseStart_750333 baseEnd_750333 := by
    simpa [prefixWord, tailWord_750333, baseEnd_750333] using wordTrace_append hprefix tailTrace_750333
  have hstable : (prefixWord ++ tailWord_750333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750333).length < 2 ^ (prefixWord ++ tailWord_750333).sum := by decide
  have hdescent : baseEnd_750333 < baseStart_750333 := by decide
  rcases family_descends (prefixWord ++ tailWord_750333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750344 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_750344 : Nat := 118140960795 + 750344 * 2 ^ 59
def prefixEnd_750344 : Nat := 4983230072969 + 3 ^ 40 * 750344 * 2
def baseEnd_750344 : Nat := 256858085478211672899491

theorem tailTrace_750344 : CollatzResearch.WordTrace tailWord_750344 prefixEnd_750344 256858085478211672899491 := by
  unfold tailWord_750344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683646996819655698941043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18244862662426207598588057 13683646996819655698941043)
  ·
    refine ⟨20525470495229483548411565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13683646996819655698941043 20525470495229483548411565)
    ·
      refine ⟨7697051435711056330654337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20525470495229483548411565 7697051435711056330654337)
      ·
        refine ⟨5772788576783292247990753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7697051435711056330654337 5772788576783292247990753)
        ·
          refine ⟨4329591432587469185993065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5772788576783292247990753 4329591432587469185993065)
          ·
            refine ⟨3247193574440601889494799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4329591432587469185993065 3247193574440601889494799)
            ·
              refine ⟨4870790361660902834242199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247193574440601889494799 4870790361660902834242199)
              ·
                refine ⟨7306185542491354251363299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870790361660902834242199 7306185542491354251363299)
                ·
                  refine ⟨10959278313737031377044949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306185542491354251363299 10959278313737031377044949)
                  ·
                    refine ⟨256858085478211672899491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10959278313737031377044949 256858085478211672899491)
                    ·
                      rfl

theorem cell22_750344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_750344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750344 prefixEnd_750344 := by exact prefixLift 750344
  have htrace : WordTrace (prefixWord ++ tailWord_750344) baseStart_750344 baseEnd_750344 := by
    simpa [prefixWord, tailWord_750344, baseEnd_750344] using wordTrace_append hprefix tailTrace_750344
  have hstable : (prefixWord ++ tailWord_750344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750344).length < 2 ^ (prefixWord ++ tailWord_750344).sum := by decide
  have hdescent : baseEnd_750344 < baseStart_750344 := by decide
  rcases family_descends (prefixWord ++ tailWord_750344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750391 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 4]
def baseStart_750391 : Nat := 118140960795 + 750391 * 2 ^ 59
def prefixEnd_750391 : Nat := 4983230072969 + 3 ^ 40 * 750391 * 2
def baseEnd_750391 : Nat := 85624724846239738991449

theorem tailTrace_750391 : CollatzResearch.WordTrace tailWord_750391 prefixEnd_750391 85624724846239738991449 := by
  unfold tailWord_750391
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369008224469038424843027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18246005482979358949895351 27369008224469038424843027)
  ·
    refine ⟨41053512336703557637264541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27369008224469038424843027 41053512336703557637264541)
    ·
      refine ⟨15395067126263834113974203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41053512336703557637264541 15395067126263834113974203)
      ·
        refine ⟨23092600689395751170961305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15395067126263834113974203 23092600689395751170961305)
        ·
          refine ⟨17319450517046813378220979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23092600689395751170961305 17319450517046813378220979)
          ·
            refine ⟨25979175775570220067331469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319450517046813378220979 25979175775570220067331469)
            ·
              refine ⟨9742190915838832525249301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25979175775570220067331469 9742190915838832525249301)
              ·
                refine ⟨456665199179945274621061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9742190915838832525249301 456665199179945274621061)
                ·
                  refine ⟨85624724846239738991449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456665199179945274621061 85624724846239738991449)
                  ·
                    rfl

theorem cell22_750391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 4].length) (baseStart_750391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750391 prefixEnd_750391 := by exact prefixLift 750391
  have htrace : WordTrace (prefixWord ++ tailWord_750391) baseStart_750391 baseEnd_750391 := by
    simpa [prefixWord, tailWord_750391, baseEnd_750391] using wordTrace_append hprefix tailTrace_750391
  have hstable : (prefixWord ++ tailWord_750391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750391).length < 2 ^ (prefixWord ++ tailWord_750391).sum := by decide
  have hdescent : baseEnd_750391 < baseStart_750391 := by decide
  rcases family_descends (prefixWord ++ tailWord_750391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750421 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_750421 : Nat := 118140960795 + 750421 * 2 ^ 59
def prefixEnd_750421 : Nat := 4983230072969 + 3 ^ 40 * 750421 * 2
def baseEnd_750421 : Nat := 256884444151809138724255

theorem tailTrace_750421 : CollatzResearch.WordTrace tailWord_750421 prefixEnd_750421 256884444151809138724255 := by
  unfold tailWord_750421
  simp only [CollatzResearch.WordTrace]
  refine ⟨27370102414360353548435117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18246734942906902365623411 27370102414360353548435117)
  ·
    refine ⟨10263788405385132580663169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27370102414360353548435117 10263788405385132580663169)
    ·
      refine ⟨7697841304038849435497377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10263788405385132580663169 7697841304038849435497377)
      ·
        refine ⟨5773380978029137076623033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7697841304038849435497377 5773380978029137076623033)
        ·
          refine ⟨4330035733521852807467275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773380978029137076623033 4330035733521852807467275)
          ·
            refine ⟨6495053600282779211200913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330035733521852807467275 6495053600282779211200913)
            ·
              refine ⟨4871290200212084408400685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495053600282779211200913 4871290200212084408400685)
              ·
                refine ⟨1826733825079531653150257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4871290200212084408400685 1826733825079531653150257)
                ·
                  refine ⟨1370050368809648739862693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1826733825079531653150257 1370050368809648739862693)
                  ·
                    refine ⟨256884444151809138724255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1370050368809648739862693 256884444151809138724255)
                    ·
                      rfl

theorem cell22_750421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_750421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750421 prefixEnd_750421 := by exact prefixLift 750421
  have htrace : WordTrace (prefixWord ++ tailWord_750421) baseStart_750421 baseEnd_750421 := by
    simpa [prefixWord, tailWord_750421, baseEnd_750421] using wordTrace_append hprefix tailTrace_750421
  have hstable : (prefixWord ++ tailWord_750421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750421).length < 2 ^ (prefixWord ++ tailWord_750421).sum := by decide
  have hdescent : baseEnd_750421 < baseStart_750421 := by decide
  rcases family_descends (prefixWord ++ tailWord_750421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750436 : List Nat := [2, 3, 1, 1, 4, 3, 8]
def baseStart_750436 : Nat := 118140960795 + 750436 * 2 ^ 59
def prefixEnd_750436 : Nat := 4983230072969 + 3 ^ 40 * 750436 * 2
def baseEnd_750436 : Nat := 9514428850309411096267

theorem tailTrace_750436 : CollatzResearch.WordTrace tailWord_750436 prefixEnd_750436 9514428850309411096267 := by
  unfold tailWord_750436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685324754653005555115581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18247099672870674073487441 13685324754653005555115581)
  ·
    refine ⟨5131996782994877083168343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13685324754653005555115581 5131996782994877083168343)
    ·
      refine ⟨7697995174492315624752515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5131996782994877083168343 7697995174492315624752515)
      ·
        refine ⟨11546992761738473437128773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697995174492315624752515 11546992761738473437128773)
        ·
          refine ⟨2165061142825963769461645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11546992761738473437128773 2165061142825963769461645)
          ·
            refine ⟨811897928559736413548117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2165061142825963769461645 811897928559736413548117)
            ·
              refine ⟨9514428850309411096267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 811897928559736413548117 9514428850309411096267)
              ·
                rfl

theorem cell22_750436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 8].length) (baseStart_750436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750436 prefixEnd_750436 := by exact prefixLift 750436
  have htrace : WordTrace (prefixWord ++ tailWord_750436) baseStart_750436 baseEnd_750436 := by
    simpa [prefixWord, tailWord_750436, baseEnd_750436] using wordTrace_append hprefix tailTrace_750436
  have hstable : (prefixWord ++ tailWord_750436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750436).length < 2 ^ (prefixWord ++ tailWord_750436).sum := by decide
  have hdescent : baseEnd_750436 < baseStart_750436 := by decide
  rcases family_descends (prefixWord ++ tailWord_750436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750464 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_750464 : Nat := 118140960795 + 750464 * 2 ^ 59
def prefixEnd_750464 : Nat := 4983230072969 + 3 ^ 40 * 750464 * 2
def baseEnd_750464 : Nat := 85633054643523786633041

theorem tailTrace_750464 : CollatzResearch.WordTrace tailWord_750464 prefixEnd_750464 85633054643523786633041 := by
  unfold tailWord_750464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685835376602285946125223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18247780502136381261500297 13685835376602285946125223)
  ·
    refine ⟨20528753064903428919187835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13685835376602285946125223 20528753064903428919187835)
    ·
      refine ⟨30793129597355143378781753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20528753064903428919187835 30793129597355143378781753)
      ·
        refine ⟨23094847198016357534086315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30793129597355143378781753 23094847198016357534086315)
        ·
          refine ⟨34642270797024536301129473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23094847198016357534086315 34642270797024536301129473)
          ·
            refine ⟨25981703097768402225847105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34642270797024536301129473 25981703097768402225847105)
            ·
              refine ⟨19486277323326301669385329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25981703097768402225847105 19486277323326301669385329)
              ·
                refine ⟨14614707992494726252038997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19486277323326301669385329 14614707992494726252038997)
                ·
                  refine ⟨85633054643523786633041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14614707992494726252038997 85633054643523786633041)
                  ·
                    rfl

theorem cell22_750464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_750464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750464 prefixEnd_750464 := by exact prefixLift 750464
  have htrace : WordTrace (prefixWord ++ tailWord_750464) baseStart_750464 baseEnd_750464 := by
    simpa [prefixWord, tailWord_750464, baseEnd_750464] using wordTrace_append hprefix tailTrace_750464
  have hstable : (prefixWord ++ tailWord_750464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750464).length < 2 ^ (prefixWord ++ tailWord_750464).sum := by decide
  have hdescent : baseEnd_750464 < baseStart_750464 := by decide
  rcases family_descends (prefixWord ++ tailWord_750464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750498 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_750498 : Nat := 118140960795 + 750498 * 2 ^ 59
def prefixEnd_750498 : Nat := 4983230072969 + 3 ^ 40 * 750498 * 2
def baseEnd_750498 : Nat := 85636934275135534849673

theorem tailTrace_750498 : CollatzResearch.WordTrace tailWord_750498 prefixEnd_750498 85636934275135534849673 := by
  unfold tailWord_750498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843227708770348924747037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18248607223387597132658765 6843227708770348924747037)
  ·
    refine ⟨2566210390788880846780139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6843227708770348924747037 2566210390788880846780139)
    ·
      refine ⟨3849315586183321270170209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566210390788880846780139 3849315586183321270170209)
      ·
        refine ⟨2886986689637490952627657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3849315586183321270170209 2886986689637490952627657)
        ·
          refine ⟨2165240017228118214470743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2886986689637490952627657 2165240017228118214470743)
          ·
            refine ⟨3247860025842177321706115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165240017228118214470743 3247860025842177321706115)
            ·
              refine ⟨4871790038763265982559173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247860025842177321706115 4871790038763265982559173)
              ·
                refine ⟨913460632268112371729845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4871790038763265982559173 913460632268112371729845)
                ·
                  refine ⟨85636934275135534849673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913460632268112371729845 85636934275135534849673)
                  ·
                    rfl

theorem cell22_750498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_750498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750498 prefixEnd_750498 := by exact prefixLift 750498
  have htrace : WordTrace (prefixWord ++ tailWord_750498) baseStart_750498 baseEnd_750498 := by
    simpa [prefixWord, tailWord_750498, baseEnd_750498] using wordTrace_append hprefix tailTrace_750498
  have hstable : (prefixWord ++ tailWord_750498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750498).length < 2 ^ (prefixWord ++ tailWord_750498).sum := by decide
  have hdescent : baseEnd_750498 < baseStart_750498 := by decide
  rcases family_descends (prefixWord ++ tailWord_750498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750513 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_750513 : Nat := 118140960795 + 750513 * 2 ^ 59
def prefixEnd_750513 : Nat := 4983230072969 + 3 ^ 40 * 750513 * 2
def baseEnd_750513 : Nat := 256915937631951565423973

theorem tailTrace_750513 : CollatzResearch.WordTrace tailWord_750513 prefixEnd_750513 256915937631951565423973 := by
  unfold tailWord_750513
  simp only [CollatzResearch.WordTrace]
  refine ⟨27373457930027053260784193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18248971953351368840522795 27373457930027053260784193)
  ·
    refine ⟨20530093447520289945588145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27373457930027053260784193 20530093447520289945588145)
    ·
      refine ⟨15397570085640217459191109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20530093447520289945588145 15397570085640217459191109)
      ·
        refine ⟨2887044391057540773598333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15397570085640217459191109 2887044391057540773598333)
        ·
          refine ⟨1082641646646577790099375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2887044391057540773598333 1082641646646577790099375)
          ·
            refine ⟨1623962469969866685149063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082641646646577790099375 1623962469969866685149063)
            ·
              refine ⟨2435943704954800027723595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623962469969866685149063 2435943704954800027723595)
              ·
                refine ⟨3653915557432200041585393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435943704954800027723595 3653915557432200041585393)
                ·
                  refine ⟨2740436668074150031189045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3653915557432200041585393 2740436668074150031189045)
                  ·
                    refine ⟨256915937631951565423973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2740436668074150031189045 256915937631951565423973)
                    ·
                      rfl

theorem cell22_750513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_750513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750513 prefixEnd_750513 := by exact prefixLift 750513
  have htrace : WordTrace (prefixWord ++ tailWord_750513) baseStart_750513 baseEnd_750513 := by
    simpa [prefixWord, tailWord_750513, baseEnd_750513] using wordTrace_append hprefix tailTrace_750513
  have hstable : (prefixWord ++ tailWord_750513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750513).length < 2 ^ (prefixWord ++ tailWord_750513).sum := by decide
  have hdescent : baseEnd_750513 < baseStart_750513 := by decide
  rcases family_descends (prefixWord ++ tailWord_750513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750543 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 4]
def baseStart_750543 : Nat := 118140960795 + 750543 * 2 ^ 59
def prefixEnd_750543 : Nat := 4983230072969 + 3 ^ 40 * 750543 * 2
def baseEnd_750543 : Nat := 85642069081680495724627

theorem tailTrace_750543 : CollatzResearch.WordTrace tailWord_750543 prefixEnd_750543 85642069081680495724627 := by
  unfold tailWord_750543
  simp only [CollatzResearch.WordTrace]
  refine ⟨27374552119918368384376283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18249701413278912256250855 27374552119918368384376283)
  ·
    refine ⟨41061828179877552576564425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27374552119918368384376283 41061828179877552576564425)
    ·
      refine ⟨30796371134908164432423319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41061828179877552576564425 30796371134908164432423319)
      ·
        refine ⟨46194556702362246648634979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30796371134908164432423319 46194556702362246648634979)
        ·
          refine ⟨69291835053543369972952469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46194556702362246648634979 69291835053543369972952469)
          ·
            refine ⟨3248054768134845467482147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69291835053543369972952469 3248054768134845467482147)
            ·
              refine ⟨4872082152202268201223221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248054768134845467482147 4872082152202268201223221)
              ·
                refine ⟨456757701768962643864677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4872082152202268201223221 456757701768962643864677)
                ·
                  refine ⟨85642069081680495724627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456757701768962643864677 85642069081680495724627)
                  ·
                    rfl

theorem cell22_750543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 4].length) (baseStart_750543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750543 prefixEnd_750543 := by exact prefixLift 750543
  have htrace : WordTrace (prefixWord ++ tailWord_750543) baseStart_750543 baseEnd_750543 := by
    simpa [prefixWord, tailWord_750543, baseEnd_750543] using wordTrace_append hprefix tailTrace_750543
  have hstable : (prefixWord ++ tailWord_750543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750543).length < 2 ^ (prefixWord ++ tailWord_750543).sum := by decide
  have hdescent : baseEnd_750543 < baseStart_750543 := by decide
  rcases family_descends (prefixWord ++ tailWord_750543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750588 : List Nat := [2, 2, 2, 1, 2, 3, 4, 6]
def baseStart_750588 : Nat := 118140960795 + 750588 * 2 ^ 59
def prefixEnd_750588 : Nat := 4983230072969 + 3 ^ 40 * 750588 * 2
def baseEnd_750588 : Nat := 28549067962741818866527

theorem tailTrace_750588 : CollatzResearch.WordTrace tailWord_750588 prefixEnd_750588 28549067962741818866527 := by
  unfold tailWord_750588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688096702377670534882209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18250795603170227379842945 13688096702377670534882209)
  ·
    refine ⟨10266072526783252901161657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13688096702377670534882209 10266072526783252901161657)
    ·
      refine ⟨7699554395087439675871243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266072526783252901161657 7699554395087439675871243)
      ·
        refine ⟨11549331592631159513806865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699554395087439675871243 11549331592631159513806865)
        ·
          refine ⟨8661998694473369635355149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11549331592631159513806865 8661998694473369635355149)
          ·
            refine ⟨3248249510427513613258181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8661998694473369635355149 3248249510427513613258181)
            ·
              refine ⟨609046783205158802485909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3248249510427513613258181 609046783205158802485909)
              ·
                refine ⟨28549067962741818866527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 609046783205158802485909 28549067962741818866527)
                ·
                  rfl

theorem cell22_750588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_750588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750588 prefixEnd_750588 := by exact prefixLift 750588
  have htrace : WordTrace (prefixWord ++ tailWord_750588) baseStart_750588 baseEnd_750588 := by
    simpa [prefixWord, tailWord_750588, baseEnd_750588] using wordTrace_append hprefix tailTrace_750588
  have hstable : (prefixWord ++ tailWord_750588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750588).length < 2 ^ (prefixWord ++ tailWord_750588).sum := by decide
  have hdescent : baseEnd_750588 < baseStart_750588 := by decide
  rcases family_descends (prefixWord ++ tailWord_750588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750710 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_750710 : Nat := 118140960795 + 750710 * 2 ^ 59
def prefixEnd_750710 : Nat := 4983230072969 + 3 ^ 40 * 750710 * 2
def baseEnd_750710 : Nat := 256983374757908718248369

theorem tailTrace_750710 : CollatzResearch.WordTrace tailWord_750710 prefixEnd_750710 256983374757908718248369 := by
  unfold tailWord_750710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711290194394584744106599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18253762073542237270470389 1711290194394584744106599)
  ·
    refine ⟨2566935291591877116159899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711290194394584744106599 2566935291591877116159899)
    ·
      refine ⟨3850402937387815674239849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566935291591877116159899 3850402937387815674239849)
      ·
        refine ⟨2887802203040861755679887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3850402937387815674239849 2887802203040861755679887)
        ·
          refine ⟨4331703304561292633519831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887802203040861755679887 4331703304561292633519831)
          ·
            refine ⟨6497554956841938950279747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331703304561292633519831 6497554956841938950279747)
            ·
              refine ⟨9746332435262908425419621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497554956841938950279747 9746332435262908425419621)
              ·
                refine ⟨1827437331611795329766179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9746332435262908425419621 1827437331611795329766179)
                ·
                  refine ⟨2741155997417692994649269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827437331611795329766179 2741155997417692994649269)
                  ·
                    refine ⟨256983374757908718248369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741155997417692994649269 256983374757908718248369)
                    ·
                      rfl

theorem cell22_750710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_750710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750710 prefixEnd_750710 := by exact prefixLift 750710
  have htrace : WordTrace (prefixWord ++ tailWord_750710) baseStart_750710 baseEnd_750710 := by
    simpa [prefixWord, tailWord_750710, baseEnd_750710] using wordTrace_append hprefix tailTrace_750710
  have hstable : (prefixWord ++ tailWord_750710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750710).length < 2 ^ (prefixWord ++ tailWord_750710).sum := by decide
  have hdescent : baseEnd_750710 < baseStart_750710 := by decide
  rcases family_descends (prefixWord ++ tailWord_750710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750718 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_750718 : Nat := 118140960795 + 750718 * 2 ^ 59
def prefixEnd_750718 : Nat := 4983230072969 + 3 ^ 40 * 750718 * 2
def baseEnd_750718 : Nat := 85662037773799788016115

theorem tailTrace_750718 : CollatzResearch.WordTrace tailWord_750718 prefixEnd_750718 85662037773799788016115 := by
  unfold tailWord_750718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3422616861785546658999601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18253956596189582181331205 3422616861785546658999601)
  ·
    refine ⟨2566962646339159994249701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3422616861785546658999601 2566962646339159994249701)
    ·
      refine ⟨481305496188592498921819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2566962646339159994249701 481305496188592498921819)
      ·
        refine ⟨721958244282888748382729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481305496188592498921819 721958244282888748382729)
        ·
          refine ⟨541468683212166561287047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721958244282888748382729 541468683212166561287047)
          ·
            refine ⟨812203024818249841930571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541468683212166561287047 812203024818249841930571)
            ·
              refine ⟨1218304537227374762895857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812203024818249841930571 1218304537227374762895857)
              ·
                refine ⟨913728402920531072171893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218304537227374762895857 913728402920531072171893)
                ·
                  refine ⟨85662037773799788016115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913728402920531072171893 85662037773799788016115)
                  ·
                    rfl

theorem cell22_750718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_750718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750718 prefixEnd_750718 := by exact prefixLift 750718
  have htrace : WordTrace (prefixWord ++ tailWord_750718) baseStart_750718 baseEnd_750718 := by
    simpa [prefixWord, tailWord_750718, baseEnd_750718] using wordTrace_append hprefix tailTrace_750718
  have hstable : (prefixWord ++ tailWord_750718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750718).length < 2 ^ (prefixWord ++ tailWord_750718).sum := by decide
  have hdescent : baseEnd_750718 < baseStart_750718 := by decide
  rcases family_descends (prefixWord ++ tailWord_750718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750744 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_750744 : Nat := 118140960795 + 750744 * 2 ^ 59
def prefixEnd_750744 : Nat := 4983230072969 + 3 ^ 40 * 750744 * 2
def baseEnd_750744 : Nat := 256995013652743962898265

theorem tailTrace_750744 : CollatzResearch.WordTrace tailWord_750744 prefixEnd_750744 256995013652743962898265 := by
  unfold tailWord_750744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690941596095089856221643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18254588794793453141628857 13690941596095089856221643)
  ·
    refine ⟨20536412394142634784332465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13690941596095089856221643 20536412394142634784332465)
    ·
      refine ⟨15402309295606976088249349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20536412394142634784332465 15402309295606976088249349)
      ·
        refine ⟨2887932992926308016546753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15402309295606976088249349 2887932992926308016546753)
        ·
          refine ⟨2165949744694731012410065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2887932992926308016546753 2165949744694731012410065)
          ·
            refine ⟨1624462308521048259307549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165949744694731012410065 1624462308521048259307549)
            ·
              refine ⟨609173365695393097240331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1624462308521048259307549 609173365695393097240331)
              ·
                refine ⟨913760048543089645860497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609173365695393097240331 913760048543089645860497)
                ·
                  refine ⟨685320036407317234395373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913760048543089645860497 685320036407317234395373)
                  ·
                    refine ⟨256995013652743962898265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685320036407317234395373 256995013652743962898265)
                    ·
                      rfl

theorem cell22_750744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_750744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750744 prefixEnd_750744 := by exact prefixLift 750744
  have htrace : WordTrace (prefixWord ++ tailWord_750744) baseStart_750744 baseEnd_750744 := by
    simpa [prefixWord, tailWord_750744, baseEnd_750744] using wordTrace_append hprefix tailTrace_750744
  have hstable : (prefixWord ++ tailWord_750744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750744).length < 2 ^ (prefixWord ++ tailWord_750744).sum := by decide
  have hdescent : baseEnd_750744 < baseStart_750744 := by decide
  rcases family_descends (prefixWord ++ tailWord_750744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750774 : List Nat := [5, 1, 3, 2, 1, 2, 8]
def baseStart_750774 : Nat := 118140960795 + 750774 * 2 ^ 59
def prefixEnd_750774 : Nat := 4983230072969 + 3 ^ 40 * 750774 * 2
def baseEnd_750774 : Nat := 9518714195030884616599

theorem tailTrace_750774 : CollatzResearch.WordTrace tailWord_750774 prefixEnd_750774 9518714195030884616599 := by
  unfold tailWord_750774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711436086380093427252211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18255318254720996557356917 1711436086380093427252211)
  ·
    refine ⟨2567154129570140140878317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711436086380093427252211 2567154129570140140878317)
    ·
      refine ⟨962682798588802552829369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2567154129570140140878317 962682798588802552829369)
      ·
        refine ⟨722012098941601914622027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962682798588802552829369 722012098941601914622027)
        ·
          refine ⟨1083018148412402871933041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722012098941601914622027 1083018148412402871933041)
          ·
            refine ⟨812263611309302153949781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083018148412402871933041 812263611309302153949781)
            ·
              refine ⟨9518714195030884616599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 812263611309302153949781 9518714195030884616599)
              ·
                rfl

theorem cell22_750774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 8].length) (baseStart_750774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750774 prefixEnd_750774 := by exact prefixLift 750774
  have htrace : WordTrace (prefixWord ++ tailWord_750774) baseStart_750774 baseEnd_750774 := by
    simpa [prefixWord, tailWord_750774, baseEnd_750774] using wordTrace_append hprefix tailTrace_750774
  have hstable : (prefixWord ++ tailWord_750774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750774).length < 2 ^ (prefixWord ++ tailWord_750774).sum := by decide
  have hdescent : baseEnd_750774 < baseStart_750774 := by decide
  rcases family_descends (prefixWord ++ tailWord_750774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750783 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_750783 : Nat := 118140960795 + 750783 * 2 ^ 59
def prefixEnd_750783 : Nat := 4983230072969 + 3 ^ 40 * 750783 * 2
def baseEnd_750783 : Nat := 257008364149760861173145

theorem tailTrace_750783 : CollatzResearch.WordTrace tailWord_750783 prefixEnd_750783 257008364149760861173145 := by
  unfold tailWord_750783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27383305639048889373113003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18255537092699259582075335 27383305639048889373113003)
  ·
    refine ⟨41074958458573334059669505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27383305639048889373113003 41074958458573334059669505)
    ·
      refine ⟨30806218843930000544752129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41074958458573334059669505 30806218843930000544752129)
      ·
        refine ⟨23104664132947500408564097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30806218843930000544752129 23104664132947500408564097)
        ·
          refine ⟨17328498099710625306423073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23104664132947500408564097 17328498099710625306423073)
          ·
            refine ⟨12996373574782968979817305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17328498099710625306423073 12996373574782968979817305)
            ·
              refine ⟨9747280181087226734862979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12996373574782968979817305 9747280181087226734862979)
              ·
                refine ⟨14620920271630840102294469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747280181087226734862979 14620920271630840102294469)
                ·
                  refine ⟨2741422550930782519180213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14620920271630840102294469 2741422550930782519180213)
                  ·
                    refine ⟨257008364149760861173145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741422550930782519180213 257008364149760861173145)
                    ·
                      rfl

theorem cell22_750783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_750783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750783 prefixEnd_750783 := by exact prefixLift 750783
  have htrace : WordTrace (prefixWord ++ tailWord_750783) baseStart_750783 baseEnd_750783 := by
    simpa [prefixWord, tailWord_750783, baseEnd_750783] using wordTrace_append hprefix tailTrace_750783
  have hstable : (prefixWord ++ tailWord_750783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750783).length < 2 ^ (prefixWord ++ tailWord_750783).sum := by decide
  have hdescent : baseEnd_750783 < baseStart_750783 := by decide
  rcases family_descends (prefixWord ++ tailWord_750783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750847 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 4]
def baseStart_750847 : Nat := 118140960795 + 750847 * 2 ^ 59
def prefixEnd_750847 : Nat := 4983230072969 + 3 ^ 40 * 750847 * 2
def baseEnd_750847 : Nat := 85676757552562009190983

theorem tailTrace_750847 : CollatzResearch.WordTrace tailWord_750847 prefixEnd_750847 85676757552562009190983 := by
  unfold tailWord_750847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27385639910817028303442795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18257093273878018868961863 27385639910817028303442795)
  ·
    refine ⟨41078459866225542455164193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27385639910817028303442795 41078459866225542455164193)
    ·
      refine ⟨30808844899669156841373145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41078459866225542455164193 30808844899669156841373145)
      ·
        refine ⟨23106633674751867631029859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30808844899669156841373145 23106633674751867631029859)
        ·
          refine ⟨34659950512127801446544789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23106633674751867631029859 34659950512127801446544789)
          ·
            refine ⟨1624685180255990692806787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34659950512127801446544789 1624685180255990692806787)
            ·
              refine ⟨2437027770383986039210181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624685180255990692806787 2437027770383986039210181)
              ·
                refine ⟨456942706946997382351909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2437027770383986039210181 456942706946997382351909)
                ·
                  refine ⟨85676757552562009190983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456942706946997382351909 85676757552562009190983)
                  ·
                    rfl

theorem cell22_750847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 4].length) (baseStart_750847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750847 prefixEnd_750847 := by exact prefixLift 750847
  have htrace : WordTrace (prefixWord ++ tailWord_750847) baseStart_750847 baseEnd_750847 := by
    simpa [prefixWord, tailWord_750847, baseEnd_750847] using wordTrace_append hprefix tailTrace_750847
  have hstable : (prefixWord ++ tailWord_750847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750847).length < 2 ^ (prefixWord ++ tailWord_750847).sum := by decide
  have hdescent : baseEnd_750847 < baseStart_750847 := by decide
  rcases family_descends (prefixWord ++ tailWord_750847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750862 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_750862 : Nat := 118140960795 + 750862 * 2 ^ 59
def prefixEnd_750862 : Nat := 4983230072969 + 3 ^ 40 * 750862 * 2
def baseEnd_750862 : Nat := 257035407464230988447903

theorem tailTrace_750862 : CollatzResearch.WordTrace tailWord_750862 prefixEnd_750862 257035407464230988447903 := by
  unfold tailWord_750862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423273375720335733154855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18257458003841790576825893 3423273375720335733154855)
  ·
    refine ⟨5134910063580503599732283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423273375720335733154855 5134910063580503599732283)
    ·
      refine ⟨7702365095370755399598425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134910063580503599732283 7702365095370755399598425)
      ·
        refine ⟨5776773821528066549698819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7702365095370755399598425 5776773821528066549698819)
        ·
          refine ⟨8665160732292099824548229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776773821528066549698819 8665160732292099824548229)
          ·
            refine ⟨1624717637304768717102793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8665160732292099824548229 1624717637304768717102793)
            ·
              refine ⟨1218538227978576537827095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624717637304768717102793 1218538227978576537827095)
              ·
                refine ⟨1827807341967864806740643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218538227978576537827095 1827807341967864806740643)
                ·
                  refine ⟨2741711012951797210110965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827807341967864806740643 2741711012951797210110965)
                  ·
                    refine ⟨257035407464230988447903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741711012951797210110965 257035407464230988447903)
                    ·
                      rfl

theorem cell22_750862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_750862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750862 prefixEnd_750862 := by exact prefixLift 750862
  have htrace : WordTrace (prefixWord ++ tailWord_750862) baseStart_750862 baseEnd_750862 := by
    simpa [prefixWord, tailWord_750862, baseEnd_750862] using wordTrace_append hprefix tailTrace_750862
  have hstable : (prefixWord ++ tailWord_750862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750862).length < 2 ^ (prefixWord ++ tailWord_750862).sum := by decide
  have hdescent : baseEnd_750862 < baseStart_750862 := by decide
  rcases family_descends (prefixWord ++ tailWord_750862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750877 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_750877 : Nat := 118140960795 + 750877 * 2 ^ 59
def prefixEnd_750877 : Nat := 4983230072969 + 3 ^ 40 * 750877 * 2
def baseEnd_750877 : Nat := 257040542270775949322857

theorem tailTrace_750877 : CollatzResearch.WordTrace tailWord_750877 prefixEnd_750877 257040542270775949322857 := by
  unfold tailWord_750877
  simp only [CollatzResearch.WordTrace]
  refine ⟨27386734100708343427034885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18257822733805562284689923 27386734100708343427034885)
  ·
    refine ⟨5135012643882814392569041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27386734100708343427034885 5135012643882814392569041)
    ·
      refine ⟨3851259482912110794426781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5135012643882814392569041 3851259482912110794426781)
      ·
        refine ⟨1444222306092041547910043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3851259482912110794426781 1444222306092041547910043)
        ·
          refine ⟨2166333459138062321865065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444222306092041547910043 2166333459138062321865065)
          ·
            refine ⟨1624750094353546741398799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2166333459138062321865065 1624750094353546741398799)
            ·
              refine ⟨2437125141530320112098199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624750094353546741398799 2437125141530320112098199)
              ·
                refine ⟨3655687712295480168147299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437125141530320112098199 3655687712295480168147299)
                ·
                  refine ⟨5483531568443220252220949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655687712295480168147299 5483531568443220252220949)
                  ·
                    refine ⟨257040542270775949322857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5483531568443220252220949 257040542270775949322857)
                    ·
                      rfl

theorem cell22_750877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_750877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750877 prefixEnd_750877 := by exact prefixLift 750877
  have htrace : WordTrace (prefixWord ++ tailWord_750877) baseStart_750877 baseEnd_750877 := by
    simpa [prefixWord, tailWord_750877, baseEnd_750877] using wordTrace_append hprefix tailTrace_750877
  have hstable : (prefixWord ++ tailWord_750877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750877).length < 2 ^ (prefixWord ++ tailWord_750877).sum := by decide
  have hdescent : baseEnd_750877 < baseStart_750877 := by decide
  rcases family_descends (prefixWord ++ tailWord_750877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750958 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_750958 : Nat := 118140960795 + 750958 * 2 ^ 59
def prefixEnd_750958 : Nat := 4983230072969 + 3 ^ 40 * 750958 * 2
def baseEnd_750958 : Nat := 257068270226118738047609

theorem tailTrace_750958 : CollatzResearch.WordTrace tailWord_750958 prefixEnd_750958 257068270226118738047609 := by
  unfold tailWord_750958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423711051676861782591691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18259792275609929507155685 3423711051676861782591691)
  ·
    refine ⟨5135566577515292673887537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423711051676861782591691 5135566577515292673887537)
    ·
      refine ⟨3851674933136469505415653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5135566577515292673887537 3851674933136469505415653)
      ·
        refine ⟨722189049963088032265435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3851674933136469505415653 722189049963088032265435)
        ·
          refine ⟨1083283574944632048398153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722189049963088032265435 1083283574944632048398153)
          ·
            refine ⟨812462681208474036298615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083283574944632048398153 812462681208474036298615)
            ·
              refine ⟨1218694021812711054447923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812462681208474036298615 1218694021812711054447923)
              ·
                refine ⟨1828041032719066581671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218694021812711054447923 1828041032719066581671885)
                ·
                  refine ⟨685515387269649968126957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1828041032719066581671885 685515387269649968126957)
                  ·
                    refine ⟨257068270226118738047609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685515387269649968126957 257068270226118738047609)
                    ·
                      rfl

theorem cell22_750958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_750958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750958 prefixEnd_750958 := by exact prefixLift 750958
  have htrace : WordTrace (prefixWord ++ tailWord_750958) baseStart_750958 baseEnd_750958 := by
    simpa [prefixWord, tailWord_750958, baseEnd_750958] using wordTrace_append hprefix tailTrace_750958
  have hstable : (prefixWord ++ tailWord_750958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750958).length < 2 ^ (prefixWord ++ tailWord_750958).sum := by decide
  have hdescent : baseEnd_750958 < baseStart_750958 := by decide
  rcases family_descends (prefixWord ++ tailWord_750958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750984 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_750984 : Nat := 118140960795 + 750984 * 2 ^ 59
def prefixEnd_750984 : Nat := 4983230072969 + 3 ^ 40 * 750984 * 2
def baseEnd_750984 : Nat := 257077170557463336897529

theorem tailTrace_750984 : CollatzResearch.WordTrace tailWord_750984 prefixEnd_750984 257077170557463336897529 := by
  unfold tailWord_750984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695318355660350350590003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18260424474213800467453337 13695318355660350350590003)
  ·
    refine ⟨20542977533490525525885005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13695318355660350350590003 20542977533490525525885005)
    ·
      refine ⟨7703616575058947072206877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20542977533490525525885005 7703616575058947072206877)
      ·
        refine ⟨2888856215647105152077579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7703616575058947072206877 2888856215647105152077579)
        ·
          refine ⟨4333284323470657728116369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888856215647105152077579 4333284323470657728116369)
          ·
            refine ⟨3249963242602993296087277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333284323470657728116369 3249963242602993296087277)
            ·
              refine ⟨1218736215976122486032729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3249963242602993296087277 1218736215976122486032729)
              ·
                refine ⟨914052161982091864524547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218736215976122486032729 914052161982091864524547)
                ·
                  refine ⟨1371078242973137796786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914052161982091864524547 1371078242973137796786821)
                  ·
                    refine ⟨257077170557463336897529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371078242973137796786821 257077170557463336897529)
                    ·
                      rfl

theorem cell22_750984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_750984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750984 prefixEnd_750984 := by exact prefixLift 750984
  have htrace : WordTrace (prefixWord ++ tailWord_750984) baseStart_750984 baseEnd_750984 := by
    simpa [prefixWord, tailWord_750984, baseEnd_750984] using wordTrace_append hprefix tailTrace_750984
  have hstable : (prefixWord ++ tailWord_750984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750984).length < 2 ^ (prefixWord ++ tailWord_750984).sum := by decide
  have hdescent : baseEnd_750984 < baseStart_750984 := by decide
  rcases family_descends (prefixWord ++ tailWord_750984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750997 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_750997 : Nat := 118140960795 + 750997 * 2 ^ 59
def prefixEnd_750997 : Nat := 4983230072969 + 3 ^ 40 * 750997 * 2
def baseEnd_750997 : Nat := 257081620723135636322489

theorem tailTrace_750997 : CollatzResearch.WordTrace tailWord_750997 prefixEnd_750997 257081620723135636322489 := by
  unfold tailWord_750997
  simp only [CollatzResearch.WordTrace]
  refine ⟨27391110860273603921403245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18260740573515735947602163 27391110860273603921403245)
  ·
    refine ⟨10271666572602601470526217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27391110860273603921403245 10271666572602601470526217)
    ·
      refine ⟨7703749929451951102894663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10271666572602601470526217 7703749929451951102894663)
      ·
        refine ⟨11555624894177926654341995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703749929451951102894663 11555624894177926654341995)
        ·
          refine ⟨17333437341266889981512993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555624894177926654341995 17333437341266889981512993)
          ·
            refine ⟨13000078005950167486134745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17333437341266889981512993 13000078005950167486134745)
            ·
              refine ⟨9750058504462625614601059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13000078005950167486134745 9750058504462625614601059)
              ·
                refine ⟨14625087756693938421901589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9750058504462625614601059 14625087756693938421901589)
                ·
                  refine ⟨685550988595028363526637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14625087756693938421901589 685550988595028363526637)
                  ·
                    refine ⟨257081620723135636322489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685550988595028363526637 257081620723135636322489)
                    ·
                      rfl

theorem cell22_750997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_750997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_750997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_750997 prefixEnd_750997 := by exact prefixLift 750997
  have htrace : WordTrace (prefixWord ++ tailWord_750997) baseStart_750997 baseEnd_750997 := by
    simpa [prefixWord, tailWord_750997, baseEnd_750997] using wordTrace_append hprefix tailTrace_750997
  have hstable : (prefixWord ++ tailWord_750997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750997).length < 2 ^ (prefixWord ++ tailWord_750997).sum := by decide
  have hdescent : baseEnd_750997 < baseStart_750997 := by decide
  rcases family_descends (prefixWord ++ tailWord_750997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751072 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_751072 : Nat := 118140960795 + 751072 * 2 ^ 59
def prefixEnd_751072 : Nat := 4983230072969 + 3 ^ 40 * 751072 * 2
def baseEnd_751072 : Nat := 85702431585286813565753

theorem tailTrace_751072 : CollatzResearch.WordTrace tailWord_751072 prefixEnd_751072 85702431585286813565753 := by
  unfold tailWord_751072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13696923167500945865191735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18262564223334594486922313 13696923167500945865191735)
  ·
    refine ⟨20545384751251418797787603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13696923167500945865191735 20545384751251418797787603)
    ·
      refine ⟨30818077126877128196681405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20545384751251418797787603 30818077126877128196681405)
      ·
        refine ⟨11556778922578923073755527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30818077126877128196681405 11556778922578923073755527)
        ·
          refine ⟨17335168383868384610633291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11556778922578923073755527 17335168383868384610633291)
          ·
            refine ⟨26002752575802576915949937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17335168383868384610633291 26002752575802576915949937)
            ·
              refine ⟨19502064431851932686962453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26002752575802576915949937 19502064431851932686962453)
              ·
                refine ⟨914159270243059344701365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19502064431851932686962453 914159270243059344701365)
                ·
                  refine ⟨85702431585286813565753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 914159270243059344701365 85702431585286813565753)
                  ·
                    rfl

theorem cell22_751072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_751072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751072 prefixEnd_751072 := by exact prefixLift 751072
  have htrace : WordTrace (prefixWord ++ tailWord_751072) baseStart_751072 baseEnd_751072 := by
    simpa [prefixWord, tailWord_751072, baseEnd_751072] using wordTrace_append hprefix tailTrace_751072
  have hstable : (prefixWord ++ tailWord_751072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751072).length < 2 ^ (prefixWord ++ tailWord_751072).sum := by decide
  have hdescent : baseEnd_751072 < baseStart_751072 := by decide
  rcases family_descends (prefixWord ++ tailWord_751072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751087 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_751087 : Nat := 118140960795 + 751087 * 2 ^ 59
def prefixEnd_751087 : Nat := 4983230072969 + 3 ^ 40 * 751087 * 2
def baseEnd_751087 : Nat := 257112429562405401572213

theorem tailTrace_751087 : CollatzResearch.WordTrace tailWord_751087 prefixEnd_751087 257112429562405401572213 := by
  unfold tailWord_751087
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394393429947549292179515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18262928953298366194786343 27394393429947549292179515)
  ·
    refine ⟨41091590144921323938269273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27394393429947549292179515 41091590144921323938269273)
    ·
      refine ⟨30818692608690992953701955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41091590144921323938269273 30818692608690992953701955)
      ·
        refine ⟨46228038913036489430552933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30818692608690992953701955 46228038913036489430552933)
        ·
          refine ⟨8667757296194341768228675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46228038913036489430552933 8667757296194341768228675)
          ·
            refine ⟨13001635944291512652343013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667757296194341768228675 13001635944291512652343013)
            ·
              refine ⟨2437806739554658622314315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13001635944291512652343013 2437806739554658622314315)
              ·
                refine ⟨3656710109331987933471473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437806739554658622314315 3656710109331987933471473)
                ·
                  refine ⟨2742532581998990950103605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656710109331987933471473 2742532581998990950103605)
                  ·
                    refine ⟨257112429562405401572213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2742532581998990950103605 257112429562405401572213)
                    ·
                      rfl

theorem cell22_751087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_751087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751087 prefixEnd_751087 := by exact prefixLift 751087
  have htrace : WordTrace (prefixWord ++ tailWord_751087) baseStart_751087 baseEnd_751087 := by
    simpa [prefixWord, tailWord_751087, baseEnd_751087] using wordTrace_append hprefix tailTrace_751087
  have hstable : (prefixWord ++ tailWord_751087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751087).length < 2 ^ (prefixWord ++ tailWord_751087).sum := by decide
  have hdescent : baseEnd_751087 < baseStart_751087 := by decide
  rcases family_descends (prefixWord ++ tailWord_751087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751162 : List Nat := [3, 1, 1, 1, 3, 2, 1, 10]
def baseStart_751162 : Nat := 118140960795 + 751162 * 2 ^ 59
def prefixEnd_751162 : Nat := 4983230072969 + 3 ^ 40 * 751162 * 2
def baseEnd_751162 : Nat := 28570900399458911771887

theorem tailTrace_751162 : CollatzResearch.WordTrace tailWord_751162 prefixEnd_751162 28570900399458911771887 := by
  unfold tailWord_751162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849282226168959275289935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18264752603117224734106493 6849282226168959275289935)
  ·
    refine ⟨10273923339253438912934903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6849282226168959275289935 10273923339253438912934903)
    ·
      refine ⟨15410885008880158369402355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273923339253438912934903 15410885008880158369402355)
      ·
        refine ⟨23116327513320237554103533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410885008880158369402355 23116327513320237554103533)
        ·
          refine ⟨8668622817495089082788825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23116327513320237554103533 8668622817495089082788825)
          ·
            refine ⟨6501467113121316812091619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8668622817495089082788825 6501467113121316812091619)
            ·
              refine ⟨9752200669681975218137429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501467113121316812091619 9752200669681975218137429)
              ·
                refine ⟨28570900399458911771887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9752200669681975218137429 28570900399458911771887)
                ·
                  rfl

theorem cell22_751162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_751162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751162 prefixEnd_751162 := by exact prefixLift 751162
  have htrace : WordTrace (prefixWord ++ tailWord_751162) baseStart_751162 baseEnd_751162 := by
    simpa [prefixWord, tailWord_751162, baseEnd_751162] using wordTrace_append hprefix tailTrace_751162
  have hstable : (prefixWord ++ tailWord_751162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751162).length < 2 ^ (prefixWord ++ tailWord_751162).sum := by decide
  have hdescent : baseEnd_751162 < baseStart_751162 := by decide
  rcases family_descends (prefixWord ++ tailWord_751162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751194 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_751194 : Nat := 118140960795 + 751194 * 2 ^ 59
def prefixEnd_751194 : Nat := 4983230072969 + 3 ^ 40 * 751194 * 2
def baseEnd_751194 : Nat := 257149057849092789146885

theorem tailTrace_751194 : CollatzResearch.WordTrace tailWord_751194 prefixEnd_751194 257149057849092789146885 := by
  unfold tailWord_751194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849574010139976641581159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18265530693706604377549757 6849574010139976641581159)
  ·
    refine ⟨10274361015209964962371739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6849574010139976641581159 10274361015209964962371739)
    ·
      refine ⟨15411541522814947443557609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10274361015209964962371739 15411541522814947443557609)
      ·
        refine ⟨11558656142111210582668207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15411541522814947443557609 11558656142111210582668207)
        ·
          refine ⟨17337984213166815874002311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11558656142111210582668207 17337984213166815874002311)
          ·
            refine ⟨26006976319750223811003467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17337984213166815874002311 26006976319750223811003467)
            ·
              refine ⟨39010464479625335716505201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26006976319750223811003467 39010464479625335716505201)
              ·
                refine ⟨29257848359719001787378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39010464479625335716505201 29257848359719001787378901)
                ·
                  refine ⟨685730820930914104391693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29257848359719001787378901 685730820930914104391693)
                  ·
                    refine ⟨257149057849092789146885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685730820930914104391693 257149057849092789146885)
                    ·
                      rfl

theorem cell22_751194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_751194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751194 prefixEnd_751194 := by exact prefixLift 751194
  have htrace : WordTrace (prefixWord ++ tailWord_751194) baseStart_751194 baseEnd_751194 := by
    simpa [prefixWord, tailWord_751194, baseEnd_751194] using wordTrace_append hprefix tailTrace_751194
  have hstable : (prefixWord ++ tailWord_751194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751194).length < 2 ^ (prefixWord ++ tailWord_751194).sum := by decide
  have hdescent : baseEnd_751194 < baseStart_751194 := by decide
  rcases family_descends (prefixWord ++ tailWord_751194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751196 : List Nat := [2, 2, 4, 1, 2, 3, 1, 7]
def baseStart_751196 : Nat := 118140960795 + 751196 * 2 ^ 59
def prefixEnd_751196 : Nat := 4983230072969 + 3 ^ 40 * 751196 * 2
def baseEnd_751196 : Nat := 28572193609996161177431

theorem tailTrace_751196 : CollatzResearch.WordTrace tailWord_751196 prefixEnd_751196 28572193609996161177431 := by
  unfold tailWord_751196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699184493276330453948721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18265579324368440605264961 13699184493276330453948721)
  ·
    refine ⟨10274388369957247840461541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13699184493276330453948721 10274388369957247840461541)
    ·
      refine ⟨1926447819366983970086539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10274388369957247840461541 1926447819366983970086539)
      ·
        refine ⟨2889671729050475955129809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926447819366983970086539 2889671729050475955129809)
        ·
          refine ⟨2167253796787856966347357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889671729050475955129809 2167253796787856966347357)
          ·
            refine ⟨812720173795446362380259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2167253796787856966347357 812720173795446362380259)
            ·
              refine ⟨1219080260693169543570389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812720173795446362380259 1219080260693169543570389)
              ·
                refine ⟨28572193609996161177431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1219080260693169543570389 28572193609996161177431)
                ·
                  rfl

theorem cell22_751196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_751196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751196 prefixEnd_751196 := by exact prefixLift 751196
  have htrace : WordTrace (prefixWord ++ tailWord_751196) baseStart_751196 baseEnd_751196 := by
    simpa [prefixWord, tailWord_751196, baseEnd_751196] using wordTrace_append hprefix tailTrace_751196
  have hstable : (prefixWord ++ tailWord_751196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751196).length < 2 ^ (prefixWord ++ tailWord_751196).sum := by decide
  have hdescent : baseEnd_751196 < baseStart_751196 := by decide
  rcases family_descends (prefixWord ++ tailWord_751196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751239 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_751239 : Nat := 118140960795 + 751239 * 2 ^ 59
def prefixEnd_751239 : Nat := 4983230072969 + 3 ^ 40 * 751239 * 2
def baseEnd_751239 : Nat := 257164462268727671771747

theorem tailTrace_751239 : CollatzResearch.WordTrace tailWord_751239 prefixEnd_751239 257164462268727671771747 := by
  unfold tailWord_751239
  simp only [CollatzResearch.WordTrace]
  refine ⟨27399937325396879251712771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18266624883597919501141847 27399937325396879251712771)
  ·
    refine ⟨41099905988095318877569157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27399937325396879251712771 41099905988095318877569157)
    ·
      refine ⟨7706232372767872289544217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41099905988095318877569157 7706232372767872289544217)
      ·
        refine ⟨5779674279575904217158163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7706232372767872289544217 5779674279575904217158163)
        ·
          refine ⟨8669511419363856325737245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779674279575904217158163 8669511419363856325737245)
          ·
            refine ⟨3251066782261446122151467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8669511419363856325737245 3251066782261446122151467)
            ·
              refine ⟨4876600173392169183227201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251066782261446122151467 4876600173392169183227201)
              ·
                refine ⟨3657450130044126887420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876600173392169183227201 3657450130044126887420401)
                ·
                  refine ⟨2743087597533095165565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3657450130044126887420401 2743087597533095165565301)
                  ·
                    refine ⟨257164462268727671771747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2743087597533095165565301 257164462268727671771747)
                    ·
                      rfl

theorem cell22_751239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_751239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751239 prefixEnd_751239 := by exact prefixLift 751239
  have htrace : WordTrace (prefixWord ++ tailWord_751239) baseStart_751239 baseEnd_751239 := by
    simpa [prefixWord, tailWord_751239, baseEnd_751239] using wordTrace_append hprefix tailTrace_751239
  have hstable : (prefixWord ++ tailWord_751239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751239).length < 2 ^ (prefixWord ++ tailWord_751239).sum := by decide
  have hdescent : baseEnd_751239 < baseStart_751239 := by decide
  rcases family_descends (prefixWord ++ tailWord_751239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751269 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 6]
def baseStart_751269 : Nat := 118140960795 + 751269 * 2 ^ 59
def prefixEnd_751269 : Nat := 4983230072969 + 3 ^ 40 * 751269 * 2
def baseEnd_751269 : Nat := 85724910627272531173885

theorem tailTrace_751269 : CollatzResearch.WordTrace tailWord_751269 prefixEnd_751269 85724910627272531173885 := by
  unfold tailWord_751269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27401031515288194375304861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18267354343525462916869907 27401031515288194375304861)
  ·
    refine ⟨10275386818233072890739323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27401031515288194375304861 10275386818233072890739323)
    ·
      refine ⟨15413080227349609336108985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10275386818233072890739323 15413080227349609336108985)
      ·
        refine ⟨11559810170512207002081739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15413080227349609336108985 11559810170512207002081739)
        ·
          refine ⟨17339715255768310503122609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11559810170512207002081739 17339715255768310503122609)
          ·
            refine ⟨13004786441826232877341957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17339715255768310503122609 13004786441826232877341957)
            ·
              refine ⟨2438397457842418664501617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13004786441826232877341957 2438397457842418664501617)
              ·
                refine ⟨1828798093381813998376213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438397457842418664501617 1828798093381813998376213)
                ·
                  refine ⟨85724910627272531173885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1828798093381813998376213 85724910627272531173885)
                  ·
                    rfl

theorem cell22_751269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_751269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751269 prefixEnd_751269 := by exact prefixLift 751269
  have htrace : WordTrace (prefixWord ++ tailWord_751269) baseStart_751269 baseEnd_751269 := by
    simpa [prefixWord, tailWord_751269, baseEnd_751269] using wordTrace_append hprefix tailTrace_751269
  have hstable : (prefixWord ++ tailWord_751269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751269).length < 2 ^ (prefixWord ++ tailWord_751269).sum := by decide
  have hdescent : baseEnd_751269 < baseStart_751269 := by decide
  rcases family_descends (prefixWord ++ tailWord_751269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751303 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 4]
def baseStart_751303 : Nat := 118140960795 + 751303 * 2 ^ 59
def prefixEnd_751303 : Nat := 4983230072969 + 3 ^ 40 * 751303 * 2
def baseEnd_751303 : Nat := 85728790258884279390517

theorem tailTrace_751303 : CollatzResearch.WordTrace tailWord_751303 prefixEnd_751303 85728790258884279390517 := by
  unfold tailWord_751303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27402271597165018182042563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18268181064776678788028375 27402271597165018182042563)
  ·
    refine ⟨41103407395747527273063845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27402271597165018182042563 41103407395747527273063845)
    ·
      refine ⟨7706888886702661363699471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41103407395747527273063845 7706888886702661363699471)
      ·
        refine ⟨11560333330053992045549207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706888886702661363699471 11560333330053992045549207)
        ·
          refine ⟨17340499995080988068323811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11560333330053992045549207 17340499995080988068323811)
          ·
            refine ⟨26010749992621482102485717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17340499995080988068323811 26010749992621482102485717)
            ·
              refine ⟨609626952952065986777009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26010749992621482102485717 609626952952065986777009)
              ·
                refine ⟨457220214714049490082757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609626952952065986777009 457220214714049490082757)
                ·
                  refine ⟨85728790258884279390517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457220214714049490082757 85728790258884279390517)
                  ·
                    rfl

theorem cell22_751303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 4].length) (baseStart_751303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751303 prefixEnd_751303 := by exact prefixLift 751303
  have htrace : WordTrace (prefixWord ++ tailWord_751303) baseStart_751303 baseEnd_751303 := by
    simpa [prefixWord, tailWord_751303, baseEnd_751303] using wordTrace_append hprefix tailTrace_751303
  have hstable : (prefixWord ++ tailWord_751303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751303).length < 2 ^ (prefixWord ++ tailWord_751303).sum := by decide
  have hdescent : baseEnd_751303 < baseStart_751303 := by decide
  rcases family_descends (prefixWord ++ tailWord_751303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751348 : List Nat := [2, 6, 1, 1, 1, 11]
def baseStart_751348 : Nat := 118140960795 + 751348 * 2 ^ 59
def prefixEnd_751348 : Nat := 4983230072969 + 3 ^ 40 * 751348 * 2
def baseEnd_751348 : Nat := 3175330557978860750573

theorem tailTrace_751348 : CollatzResearch.WordTrace tailWord_751348 prefixEnd_751348 3175330557978860750573 := by
  unfold tailWord_751348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701956441000995433715349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18269275254667993911620465 13701956441000995433715349)
  ·
    refine ⟨642279208171921660955407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13701956441000995433715349 642279208171921660955407)
    ·
      refine ⟨963418812257882491433111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642279208171921660955407 963418812257882491433111)
      ·
        refine ⟨1445128218386823737149667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963418812257882491433111 1445128218386823737149667)
        ·
          refine ⟨2167692327580235605724501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445128218386823737149667 2167692327580235605724501)
          ·
            refine ⟨3175330557978860750573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2167692327580235605724501 3175330557978860750573)
            ·
              rfl

theorem cell22_751348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 11].length) (baseStart_751348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751348 prefixEnd_751348 := by exact prefixLift 751348
  have htrace : WordTrace (prefixWord ++ tailWord_751348) baseStart_751348 baseEnd_751348 := by
    simpa [prefixWord, tailWord_751348, baseEnd_751348] using wordTrace_append hprefix tailTrace_751348
  have hstable : (prefixWord ++ tailWord_751348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751348).length < 2 ^ (prefixWord ++ tailWord_751348).sum := by decide
  have hdescent : baseEnd_751348 < baseStart_751348 := by decide
  rcases family_descends (prefixWord ++ tailWord_751348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751359 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 7]
def baseStart_751359 : Nat := 118140960795 + 751359 * 2 ^ 59
def prefixEnd_751359 : Nat := 4983230072969 + 3 ^ 40 * 751359 * 2
def baseEnd_751359 : Nat := 85735180240362452923793

theorem tailTrace_751359 : CollatzResearch.WordTrace tailWord_751359 prefixEnd_751359 85735180240362452923793 := by
  unfold tailWord_751359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27404314084962139746081131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18269542723308093164054087 27404314084962139746081131)
  ·
    refine ⟨41106471127443209619121697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27404314084962139746081131 41106471127443209619121697)
    ·
      refine ⟨30829853345582407214341273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41106471127443209619121697 30829853345582407214341273)
      ·
        refine ⟨23122390009186805410755955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30829853345582407214341273 23122390009186805410755955)
        ·
          refine ⟨34683585013780208116133933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23122390009186805410755955 34683585013780208116133933)
          ·
            refine ⟨13006344380167578043550225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34683585013780208116133933 13006344380167578043550225)
            ·
              refine ⟨9754758285125683532662669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13006344380167578043550225 9754758285125683532662669)
              ·
                refine ⟨3658034356922131324748501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9754758285125683532662669 3658034356922131324748501)
                ·
                  refine ⟨85735180240362452923793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3658034356922131324748501 85735180240362452923793)
                  ·
                    rfl

theorem cell22_751359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_751359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751359 prefixEnd_751359 := by exact prefixLift 751359
  have htrace : WordTrace (prefixWord ++ tailWord_751359) baseStart_751359 baseEnd_751359 := by
    simpa [prefixWord, tailWord_751359, baseEnd_751359] using wordTrace_append hprefix tailTrace_751359
  have hstable : (prefixWord ++ tailWord_751359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751359).length < 2 ^ (prefixWord ++ tailWord_751359).sum := by decide
  have hdescent : baseEnd_751359 < baseStart_751359 := by decide
  rcases family_descends (prefixWord ++ tailWord_751359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751455 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 4]
def baseStart_751455 : Nat := 118140960795 + 751455 * 2 ^ 59
def prefixEnd_751455 : Nat := 4983230072969 + 3 ^ 40 * 751455 * 2
def baseEnd_751455 : Nat := 85746134494325036123695

theorem tailTrace_751455 : CollatzResearch.WordTrace tailWord_751455 prefixEnd_751455 85746134494325036123695 := by
  unfold tailWord_751455
  simp only [CollatzResearch.WordTrace]
  refine ⟨27407815492614348141575819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18271876995076232094383879 27407815492614348141575819)
  ·
    refine ⟨41111723238921522212363729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27407815492614348141575819 41111723238921522212363729)
    ·
      refine ⟨30833792429191141659272797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41111723238921522212363729 30833792429191141659272797)
      ·
        refine ⟨11562672160946678122227299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30833792429191141659272797 11562672160946678122227299)
        ·
          refine ⟨17344008241420017183340949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562672160946678122227299 17344008241420017183340949)
          ·
            refine ⟨813000386316563305469107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17344008241420017183340949 813000386316563305469107)
            ·
              refine ⟨1219500579474844958203661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813000386316563305469107 1219500579474844958203661)
              ·
                refine ⟨457312717303066859326373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1219500579474844958203661 457312717303066859326373)
                ·
                  refine ⟨85746134494325036123695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457312717303066859326373 85746134494325036123695)
                  ·
                    rfl

theorem cell22_751455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 4].length) (baseStart_751455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751455 prefixEnd_751455 := by exact prefixLift 751455
  have htrace : WordTrace (prefixWord ++ tailWord_751455) baseStart_751455 baseEnd_751455 := by
    simpa [prefixWord, tailWord_751455, baseEnd_751455] using wordTrace_append hprefix tailTrace_751455
  have hstable : (prefixWord ++ tailWord_751455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751455).length < 2 ^ (prefixWord ++ tailWord_751455).sum := by decide
  have hdescent : baseEnd_751455 < baseStart_751455 := by decide
  rcases family_descends (prefixWord ++ tailWord_751455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751468 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_751468 : Nat := 118140960795 + 751468 * 2 ^ 59
def prefixEnd_751468 : Nat := 4983230072969 + 3 ^ 40 * 751468 * 2
def baseEnd_751468 : Nat := 257242853648647407796045

theorem tailTrace_751468 : CollatzResearch.WordTrace tailWord_751468 prefixEnd_751468 257242853648647407796045 := by
  unfold tailWord_751468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13704144820783625680899529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18272193094378167574532705 13704144820783625680899529)
  ·
    refine ⟨10278108615587719260674647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13704144820783625680899529 10278108615587719260674647)
    ·
      refine ⟨15417162923381578891011971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10278108615587719260674647 15417162923381578891011971)
      ·
        refine ⟨23125744385072368336517957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15417162923381578891011971 23125744385072368336517957)
        ·
          refine ⟨4336077072201069063097117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23125744385072368336517957 4336077072201069063097117)
          ·
            refine ⟨1626028902075400898661419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4336077072201069063097117 1626028902075400898661419)
            ·
              refine ⟨2439043353113101347992129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626028902075400898661419 2439043353113101347992129)
              ·
                refine ⟨1829282514834826010994097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439043353113101347992129 1829282514834826010994097)
                ·
                  refine ⟨1371961886126119508245573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829282514834826010994097 1371961886126119508245573)
                  ·
                    refine ⟨257242853648647407796045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371961886126119508245573 257242853648647407796045)
                    ·
                      rfl

theorem cell22_751468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_751468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751468 prefixEnd_751468 := by exact prefixLift 751468
  have htrace : WordTrace (prefixWord ++ tailWord_751468) baseStart_751468 baseEnd_751468 := by
    simpa [prefixWord, tailWord_751468, baseEnd_751468] using wordTrace_append hprefix tailTrace_751468
  have hstable : (prefixWord ++ tailWord_751468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751468).length < 2 ^ (prefixWord ++ tailWord_751468).sum := by decide
  have hdescent : baseEnd_751468 < baseStart_751468 := by decide
  rcases family_descends (prefixWord ++ tailWord_751468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751470 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_751470 : Nat := 118140960795 + 751470 * 2 ^ 59
def prefixEnd_751470 : Nat := 4983230072969 + 3 ^ 40 * 751470 * 2
def baseEnd_751470 : Nat := 257243538289520069246039

theorem tailTrace_751470 : CollatzResearch.WordTrace tailWord_751470 prefixEnd_751470 257243538289520069246039 := by
  unfold tailWord_751470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426045323445000712921483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18272241725040003802247909 3426045323445000712921483)
  ·
    refine ⟨5139067985167501069382225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426045323445000712921483 5139067985167501069382225)
    ·
      refine ⟨3854300988875625802036669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5139067985167501069382225 3854300988875625802036669)
      ·
        refine ⟨1445362870828359675763751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3854300988875625802036669 1445362870828359675763751)
        ·
          refine ⟨2168044306242539513645627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445362870828359675763751 2168044306242539513645627)
          ·
            refine ⟨3252066459363809270468441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168044306242539513645627 3252066459363809270468441)
            ·
              refine ⟨2439049844522856952851331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3252066459363809270468441 2439049844522856952851331)
              ·
                refine ⟨3658574766784285429276997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439049844522856952851331 3658574766784285429276997)
                ·
                  refine ⟨685982768772053517989437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3658574766784285429276997 685982768772053517989437)
                  ·
                    refine ⟨257243538289520069246039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685982768772053517989437 257243538289520069246039)
                    ·
                      rfl

theorem cell22_751470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_751470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751470 prefixEnd_751470 := by exact prefixLift 751470
  have htrace : WordTrace (prefixWord ++ tailWord_751470) baseStart_751470 baseEnd_751470 := by
    simpa [prefixWord, tailWord_751470, baseEnd_751470] using wordTrace_append hprefix tailTrace_751470
  have hstable : (prefixWord ++ tailWord_751470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751470).length < 2 ^ (prefixWord ++ tailWord_751470).sum := by decide
  have hdescent : baseEnd_751470 < baseStart_751470 := by decide
  rcases family_descends (prefixWord ++ tailWord_751470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751502 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_751502 : Nat := 118140960795 + 751502 * 2 ^ 59
def prefixEnd_751502 : Nat := 4983230072969 + 3 ^ 40 * 751502 * 2
def baseEnd_751502 : Nat := 257254492543482652445941

theorem tailTrace_751502 : CollatzResearch.WordTrace tailWord_751502 prefixEnd_751502 257254492543482652445941 := by
  unfold tailWord_751502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426191215430509396067095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18273019815629383445691173 3426191215430509396067095)
  ·
    refine ⟨5139286823145764094100643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426191215430509396067095 5139286823145764094100643)
    ·
      refine ⟨7708930234718646141150965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139286823145764094100643 7708930234718646141150965)
      ·
        refine ⟨722712209504873075732903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7708930234718646141150965 722712209504873075732903)
        ·
          refine ⟨1084068314257309613599355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722712209504873075732903 1084068314257309613599355)
          ·
            refine ⟨1626102471385964420399033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084068314257309613599355 1626102471385964420399033)
            ·
              refine ⟨1219576853539473315299275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626102471385964420399033 1219576853539473315299275)
              ·
                refine ⟨1829365280309209972948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219576853539473315299275 1829365280309209972948913)
                ·
                  refine ⟨1372023960231907479711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829365280309209972948913 1372023960231907479711685)
                  ·
                    refine ⟨257254492543482652445941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372023960231907479711685 257254492543482652445941)
                    ·
                      rfl

theorem cell22_751502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_751502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751502 prefixEnd_751502 := by exact prefixLift 751502
  have htrace : WordTrace (prefixWord ++ tailWord_751502) baseStart_751502 baseEnd_751502 := by
    simpa [prefixWord, tailWord_751502, baseEnd_751502] using wordTrace_append hprefix tailTrace_751502
  have hstable : (prefixWord ++ tailWord_751502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751502).length < 2 ^ (prefixWord ++ tailWord_751502).sum := by decide
  have hdescent : baseEnd_751502 < baseStart_751502 := by decide
  rcases family_descends (prefixWord ++ tailWord_751502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751534 : List Nat := [4, 1, 5, 1, 1, 2, 1, 7]
def baseStart_751534 : Nat := 118140960795 + 751534 * 2 ^ 59
def prefixEnd_751534 : Nat := 4983230072969 + 3 ^ 40 * 751534 * 2
def baseEnd_751534 : Nat := 28585049644160581738427

theorem tailTrace_751534 : CollatzResearch.WordTrace tailWord_751534 prefixEnd_751534 28585049644160581738427 := by
  unfold tailWord_751534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426337107416018079212707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18273797906218763089134437 3426337107416018079212707)
  ·
    refine ⟨5139505661124027118819061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426337107416018079212707 5139505661124027118819061)
    ·
      refine ⟨481828655730377542389287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5139505661124027118819061 481828655730377542389287)
      ·
        refine ⟨722742983595566313583931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481828655730377542389287 722742983595566313583931)
        ·
          refine ⟨1084114475393349470375897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722742983595566313583931 1084114475393349470375897)
          ·
            refine ⟨813085856545012102781923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084114475393349470375897 813085856545012102781923)
            ·
              refine ⟨1219628784817518154172885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813085856545012102781923 1219628784817518154172885)
              ·
                refine ⟨28585049644160581738427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1219628784817518154172885 28585049644160581738427)
                ·
                  rfl

theorem cell22_751534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_751534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751534 prefixEnd_751534 := by exact prefixLift 751534
  have htrace : WordTrace (prefixWord ++ tailWord_751534) baseStart_751534 baseEnd_751534 := by
    simpa [prefixWord, tailWord_751534, baseEnd_751534] using wordTrace_append hprefix tailTrace_751534
  have hstable : (prefixWord ++ tailWord_751534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751534).length < 2 ^ (prefixWord ++ tailWord_751534).sum := by decide
  have hdescent : baseEnd_751534 < baseStart_751534 := by decide
  rcases family_descends (prefixWord ++ tailWord_751534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751701 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_751701 : Nat := 118140960795 + 751701 * 2 ^ 59
def prefixEnd_751701 : Nat := 4983230072969 + 3 ^ 40 * 751701 * 2
def baseEnd_751701 : Nat := 257322614310312466720331

theorem tailTrace_751701 : CollatzResearch.WordTrace tailWord_751701 prefixEnd_751701 257322614310312466720331 := by
  unfold tailWord_751701
  simp only [CollatzResearch.WordTrace]
  refine ⟨27416787849723132155030957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18277858566482088103353971 27416787849723132155030957)
  ·
    refine ⟨10281295443646174558136609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27416787849723132155030957 10281295443646174558136609)
    ·
      refine ⟨7710971582734630918602457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10281295443646174558136609 7710971582734630918602457)
      ·
        refine ⟨5783228687050973188951843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7710971582734630918602457 5783228687050973188951843)
        ·
          refine ⟨8674843030576459783427765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783228687050973188951843 8674843030576459783427765)
          ·
            refine ⟨813266534116543104696353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8674843030576459783427765 813266534116543104696353)
            ·
              refine ⟨609949900587407328522265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813266534116543104696353 609949900587407328522265)
              ·
                refine ⟨457462425440555496391699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609949900587407328522265 457462425440555496391699)
                ·
                  refine ⟨686193638160833244587549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457462425440555496391699 686193638160833244587549)
                  ·
                    refine ⟨257322614310312466720331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686193638160833244587549 257322614310312466720331)
                    ·
                      rfl

theorem cell22_751701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_751701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751701 prefixEnd_751701 := by exact prefixLift 751701
  have htrace : WordTrace (prefixWord ++ tailWord_751701) baseStart_751701 baseEnd_751701 := by
    simpa [prefixWord, tailWord_751701, baseEnd_751701] using wordTrace_append hprefix tailTrace_751701
  have hstable : (prefixWord ++ tailWord_751701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751701).length < 2 ^ (prefixWord ++ tailWord_751701).sum := by decide
  have hdescent : baseEnd_751701 < baseStart_751701 := by decide
  rcases family_descends (prefixWord ++ tailWord_751701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751725 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 6]
def baseStart_751725 : Nat := 118140960795 + 751725 * 2 ^ 59
def prefixEnd_751725 : Nat := 4983230072969 + 3 ^ 40 * 751725 * 2
def baseEnd_751725 : Nat := 85776943333594801373419

theorem tailTrace_751725 : CollatzResearch.WordTrace tailWord_751725 prefixEnd_751725 85776943333594801373419 := by
  unfold tailWord_751725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27417663201636184253904629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18278442134424122835936419 27417663201636184253904629)
  ·
    refine ⟨2570405925153392273803559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27417663201636184253904629 2570405925153392273803559)
    ·
      refine ⟨3855608887730088410705339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2570405925153392273803559 3855608887730088410705339)
      ·
        refine ⟨5783413331595132616058009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855608887730088410705339 5783413331595132616058009)
        ·
          refine ⟨4337559998696349462043507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5783413331595132616058009 4337559998696349462043507)
          ·
            refine ⟨6506339998044524193065261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337559998696349462043507 6506339998044524193065261)
            ·
              refine ⟨2439877499266696572399473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6506339998044524193065261 2439877499266696572399473)
              ·
                refine ⟨1829908124450022429299605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439877499266696572399473 1829908124450022429299605)
                ·
                  refine ⟨85776943333594801373419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1829908124450022429299605 85776943333594801373419)
                  ·
                    rfl

theorem cell22_751725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_751725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751725 prefixEnd_751725 := by exact prefixLift 751725
  have htrace : WordTrace (prefixWord ++ tailWord_751725) baseStart_751725 baseEnd_751725 := by
    simpa [prefixWord, tailWord_751725, baseEnd_751725] using wordTrace_append hprefix tailTrace_751725
  have hstable : (prefixWord ++ tailWord_751725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751725).length < 2 ^ (prefixWord ++ tailWord_751725).sum := by decide
  have hdescent : baseEnd_751725 < baseStart_751725 := by decide
  rcases family_descends (prefixWord ++ tailWord_751725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751740 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_751740 : Nat := 118140960795 + 751740 * 2 ^ 59
def prefixEnd_751740 : Nat := 4983230072969 + 3 ^ 40 * 751740 * 2
def baseEnd_751740 : Nat := 257335964807329364995211

theorem tailTrace_751740 : CollatzResearch.WordTrace tailWord_751740 prefixEnd_751740 257335964807329364995211 := by
  unfold tailWord_751740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13709105148290920907850337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18278806864387894543800449 13709105148290920907850337)
  ·
    refine ⟨10281828861218190680887753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13709105148290920907850337 10281828861218190680887753)
    ·
      refine ⟨7711371645913643010665815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10281828861218190680887753 7711371645913643010665815)
      ·
        refine ⟨11567057468870464515998723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711371645913643010665815 11567057468870464515998723)
        ·
          refine ⟨17350586203305696773998085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11567057468870464515998723 17350586203305696773998085)
          ·
            refine ⟨3253234913119818145124641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17350586203305696773998085 3253234913119818145124641)
            ·
              refine ⟨2439926184839863608843481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253234913119818145124641 2439926184839863608843481)
              ·
                refine ⟨1829944638629897706632611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439926184839863608843481 1829944638629897706632611)
                ·
                  refine ⟨2744916957944846559948917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829944638629897706632611 2744916957944846559948917)
                  ·
                    refine ⟨257335964807329364995211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2744916957944846559948917 257335964807329364995211)
                    ·
                      rfl

theorem cell22_751740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_751740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751740 prefixEnd_751740 := by exact prefixLift 751740
  have htrace : WordTrace (prefixWord ++ tailWord_751740) baseStart_751740 baseEnd_751740 := by
    simpa [prefixWord, tailWord_751740, baseEnd_751740] using wordTrace_append hprefix tailTrace_751740
  have hstable : (prefixWord ++ tailWord_751740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751740).length < 2 ^ (prefixWord ++ tailWord_751740).sum := by decide
  have hdescent : baseEnd_751740 < baseStart_751740 := by decide
  rcases family_descends (prefixWord ++ tailWord_751740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751753 : List Nat := [1, 2, 1, 1, 4, 2, 11]
def baseStart_751753 : Nat := 118140960795 + 751753 * 2 ^ 59
def prefixEnd_751753 : Nat := 4983230072969 + 3 ^ 40 * 751753 * 2
def baseEnd_751753 : Nat := 9531126480481543126673

theorem tailTrace_751753 : CollatzResearch.WordTrace tailWord_751753 prefixEnd_751753 9531126480481543126673 := by
  unfold tailWord_751753
  simp only [CollatzResearch.WordTrace]
  refine ⟨27418684445534745035923913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18279122963689830023949275 27418684445534745035923913)
  ·
    refine ⟨20564013334151058776942935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27418684445534745035923913 20564013334151058776942935)
    ·
      refine ⟨30846020001226588165414403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20564013334151058776942935 30846020001226588165414403)
      ·
        refine ⟨46269030001839882248121605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30846020001226588165414403 46269030001839882248121605)
        ·
          refine ⟨8675443125344977921522801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46269030001839882248121605 8675443125344977921522801)
          ·
            refine ⟨6506582344008733441142101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8675443125344977921522801 6506582344008733441142101)
            ·
              refine ⟨9531126480481543126673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6506582344008733441142101 9531126480481543126673)
              ·
                rfl

theorem cell22_751753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 11].length) (baseStart_751753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751753 prefixEnd_751753 := by exact prefixLift 751753
  have htrace : WordTrace (prefixWord ++ tailWord_751753) baseStart_751753 baseEnd_751753 := by
    simpa [prefixWord, tailWord_751753, baseEnd_751753] using wordTrace_append hprefix tailTrace_751753
  have hstable : (prefixWord ++ tailWord_751753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751753).length < 2 ^ (prefixWord ++ tailWord_751753).sum := by decide
  have hdescent : baseEnd_751753 < baseStart_751753 := by decide
  rcases family_descends (prefixWord ++ tailWord_751753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751832 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_751832 : Nat := 118140960795 + 751832 * 2 ^ 59
def prefixEnd_751832 : Nat := 4983230072969 + 3 ^ 40 * 751832 * 2
def baseEnd_751832 : Nat := 85789152762490597231643

theorem tailTrace_751832 : CollatzResearch.WordTrace tailWord_751832 prefixEnd_751832 85789152762490597231643 := by
  unfold tailWord_751832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710782906124270764024875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18281043874832361018699833 13710782906124270764024875)
  ·
    refine ⟨20566174359186406146037313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13710782906124270764024875 20566174359186406146037313)
    ·
      refine ⟨15424630769389804609527985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20566174359186406146037313 15424630769389804609527985)
      ·
        refine ⟨11568473077042353457145989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15424630769389804609527985 11568473077042353457145989)
        ·
          refine ⟨2169088701945441273214873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11568473077042353457145989 2169088701945441273214873)
          ·
            refine ⟨1626816526459080954911155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2169088701945441273214873 1626816526459080954911155)
            ·
              refine ⟨2440224789688621432366733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626816526459080954911155 2440224789688621432366733)
              ·
                refine ⟨915084296133233037137525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440224789688621432366733 915084296133233037137525)
                ·
                  refine ⟨85789152762490597231643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 915084296133233037137525 85789152762490597231643)
                  ·
                    rfl

theorem cell22_751832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_751832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751832 prefixEnd_751832 := by exact prefixLift 751832
  have htrace : WordTrace (prefixWord ++ tailWord_751832) baseStart_751832 baseEnd_751832 := by
    simpa [prefixWord, tailWord_751832, baseEnd_751832] using wordTrace_append hprefix tailTrace_751832
  have hstable : (prefixWord ++ tailWord_751832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751832).length < 2 ^ (prefixWord ++ tailWord_751832).sum := by decide
  have hdescent : baseEnd_751832 < baseStart_751832 := by decide
  rcases family_descends (prefixWord ++ tailWord_751832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751875 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_751875 : Nat := 118140960795 + 751875 * 2 ^ 59
def prefixEnd_751875 : Nat := 4983230072969 + 3 ^ 40 * 751875 * 2
def baseEnd_751875 : Nat := 257382178066234012869797

theorem tailTrace_751875 : CollatzResearch.WordTrace tailWord_751875 prefixEnd_751875 257382178066234012869797 := by
  unfold tailWord_751875
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423134151092759871865079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18282089434061839914576719 27423134151092759871865079)
  ·
    refine ⟨41134701226639139807797619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27423134151092759871865079 41134701226639139807797619)
    ·
      refine ⟨61702051839958709711696429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41134701226639139807797619 61702051839958709711696429)
      ·
        refine ⟨23138269439984516141886161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61702051839958709711696429 23138269439984516141886161)
        ·
          refine ⟨17353702079988387106414621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23138269439984516141886161 17353702079988387106414621)
          ·
            refine ⟨6507638279995645164905483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17353702079988387106414621 6507638279995645164905483)
            ·
              refine ⟨9761457419993467747358225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507638279995645164905483 9761457419993467747358225)
              ·
                refine ⟨7321093064995100810518669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761457419993467747358225 7321093064995100810518669)
                ·
                  refine ⟨2745409899373162803944501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7321093064995100810518669 2745409899373162803944501)
                  ·
                    refine ⟨257382178066234012869797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2745409899373162803944501 257382178066234012869797)
                    ·
                      rfl

theorem cell22_751875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_751875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751875 prefixEnd_751875 := by exact prefixLift 751875
  have htrace : WordTrace (prefixWord ++ tailWord_751875) baseStart_751875 baseEnd_751875 := by
    simpa [prefixWord, tailWord_751875, baseEnd_751875] using wordTrace_append hprefix tailTrace_751875
  have hstable : (prefixWord ++ tailWord_751875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751875).length < 2 ^ (prefixWord ++ tailWord_751875).sum := by decide
  have hdescent : baseEnd_751875 < baseStart_751875 := by decide
  rcases family_descends (prefixWord ++ tailWord_751875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751905 : List Nat := [1, 2, 3, 2, 1, 1, 2, 10]
def baseStart_751905 : Nat := 118140960795 + 751905 * 2 ^ 59
def prefixEnd_751905 : Nat := 4983230072969 + 3 ^ 40 * 751905 * 2
def baseEnd_751905 : Nat := 28599160853258214957745

theorem tailTrace_751905 : CollatzResearch.WordTrace tailWord_751905 prefixEnd_751905 28599160853258214957745 := by
  unfold tailWord_751905
  simp only [CollatzResearch.WordTrace]
  refine ⟨27424228340984074995457169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18282818893989383330304779 27424228340984074995457169)
  ·
    refine ⟨20568171255738056246592877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27424228340984074995457169 20568171255738056246592877)
    ·
      refine ⟨7713064220901771092472329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20568171255738056246592877 7713064220901771092472329)
      ·
        refine ⟨5784798165676328319354247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7713064220901771092472329 5784798165676328319354247)
        ·
          refine ⟨8677197248514492479031371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784798165676328319354247 8677197248514492479031371)
          ·
            refine ⟨13015795872771738718547057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677197248514492479031371 13015795872771738718547057)
            ·
              refine ⟨9761846904578804038910293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13015795872771738718547057 9761846904578804038910293)
              ·
                refine ⟨28599160853258214957745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9761846904578804038910293 28599160853258214957745)
                ·
                  rfl

theorem cell22_751905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 10].length) (baseStart_751905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751905 prefixEnd_751905 := by exact prefixLift 751905
  have htrace : WordTrace (prefixWord ++ tailWord_751905) baseStart_751905 baseEnd_751905 := by
    simpa [prefixWord, tailWord_751905, baseEnd_751905] using wordTrace_append hprefix tailTrace_751905
  have hstable : (prefixWord ++ tailWord_751905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751905).length < 2 ^ (prefixWord ++ tailWord_751905).sum := by decide
  have hdescent : baseEnd_751905 < baseStart_751905 := by decide
  rcases family_descends (prefixWord ++ tailWord_751905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751922 : List Nat := [3, 2, 1, 1, 5, 1, 9]
def baseStart_751922 : Nat := 118140960795 + 751922 * 2 ^ 59
def prefixEnd_751922 : Nat := 4983230072969 + 3 ^ 40 * 751922 * 2
def baseEnd_751922 : Nat := 9533269152842279886839

theorem tailTrace_751922 : CollatzResearch.WordTrace tailWord_751922 prefixEnd_751922 9533269152842279886839 := by
  unfold tailWord_751922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856212095480621724706505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18283232254614991265884013 6856212095480621724706505)
  ·
    refine ⟨5142159071610466293529879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6856212095480621724706505 5142159071610466293529879)
    ·
      refine ⟨7713238607415699440294819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142159071610466293529879 7713238607415699440294819)
      ·
        refine ⟨11569857911123549160442229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713238607415699440294819 11569857911123549160442229)
        ·
          refine ⟨1084674179167832733791459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11569857911123549160442229 1084674179167832733791459)
          ·
            refine ⟨1627011268751749100687189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084674179167832733791459 1627011268751749100687189)
            ·
              refine ⟨9533269152842279886839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1627011268751749100687189 9533269152842279886839)
              ·
                rfl

theorem cell22_751922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 9].length) (baseStart_751922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751922 prefixEnd_751922 := by exact prefixLift 751922
  have htrace : WordTrace (prefixWord ++ tailWord_751922) baseStart_751922 baseEnd_751922 := by
    simpa [prefixWord, tailWord_751922, baseEnd_751922] using wordTrace_append hprefix tailTrace_751922
  have hstable : (prefixWord ++ tailWord_751922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751922).length < 2 ^ (prefixWord ++ tailWord_751922).sum := by decide
  have hdescent : baseEnd_751922 < baseStart_751922 := by decide
  rcases family_descends (prefixWord ++ tailWord_751922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751954 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_751954 : Nat := 118140960795 + 751954 * 2 ^ 59
def prefixEnd_751954 : Nat := 4983230072969 + 3 ^ 40 * 751954 * 2
def baseEnd_751954 : Nat := 257409221380704140144555

theorem tailTrace_751954 : CollatzResearch.WordTrace tailWord_751954 prefixEnd_751954 257409221380704140144555 := by
  unfold tailWord_751954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856503879451639090997729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18284010345204370909327277 6856503879451639090997729)
  ·
    refine ⟨5142377909588729318248297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6856503879451639090997729 5142377909588729318248297)
    ·
      refine ⟨3856783432191546988686223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5142377909588729318248297 3856783432191546988686223)
      ·
        refine ⟨5785175148287320483029335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856783432191546988686223 5785175148287320483029335)
        ·
          refine ⟨8677762722430980724544003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785175148287320483029335 8677762722430980724544003)
          ·
            refine ⟨13016644083646471086816005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677762722430980724544003 13016644083646471086816005)
            ·
              refine ⟨2440620765683713328778001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13016644083646471086816005 2440620765683713328778001)
              ·
                refine ⟨1830465574262784996583501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440620765683713328778001 1830465574262784996583501)
                ·
                  refine ⟨686424590348544373718813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1830465574262784996583501 686424590348544373718813)
                  ·
                    refine ⟨257409221380704140144555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686424590348544373718813 257409221380704140144555)
                    ·
                      rfl

theorem cell22_751954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_751954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_751954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_751954 prefixEnd_751954 := by exact prefixLift 751954
  have htrace : WordTrace (prefixWord ++ tailWord_751954) baseStart_751954 baseEnd_751954 := by
    simpa [prefixWord, tailWord_751954, baseEnd_751954] using wordTrace_append hprefix tailTrace_751954
  have hstable : (prefixWord ++ tailWord_751954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751954).length < 2 ^ (prefixWord ++ tailWord_751954).sum := by decide
  have hdescent : baseEnd_751954 < baseStart_751954 := by decide
  rcases family_descends (prefixWord ++ tailWord_751954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752001 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 5]
def baseStart_752001 : Nat := 118140960795 + 752001 * 2 ^ 59
def prefixEnd_752001 : Nat := 4983230072969 + 3 ^ 40 * 752001 * 2
def baseEnd_752001 : Nat := 85808436813737228073137

theorem tailTrace_752001 : CollatzResearch.WordTrace tailWord_752001 prefixEnd_752001 85808436813737228073137 := by
  unfold tailWord_752001
  simp only [CollatzResearch.WordTrace]
  refine ⟨27427729748636283390951857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18285153165757522260634571 27427729748636283390951857)
  ·
    refine ⟨20570797311477212543213893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27427729748636283390951857 20570797311477212543213893)
    ·
      refine ⟨3857024495901977351852605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20570797311477212543213893 3857024495901977351852605)
      ·
        refine ⟨1446384185963241506944727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3857024495901977351852605 1446384185963241506944727)
        ·
          refine ⟨2169576278944862260417091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446384185963241506944727 2169576278944862260417091)
          ·
            refine ⟨3254364418417293390625637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169576278944862260417091 3254364418417293390625637)
            ·
              refine ⟨610193328453242510742307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3254364418417293390625637 610193328453242510742307)
              ·
                refine ⟨915289992679863766113461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610193328453242510742307 915289992679863766113461)
                ·
                  refine ⟨85808436813737228073137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 915289992679863766113461 85808436813737228073137)
                  ·
                    rfl

theorem cell22_752001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_752001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752001 prefixEnd_752001 := by exact prefixLift 752001
  have htrace : WordTrace (prefixWord ++ tailWord_752001) baseStart_752001 baseEnd_752001 := by
    simpa [prefixWord, tailWord_752001, baseEnd_752001] using wordTrace_append hprefix tailTrace_752001
  have hstable : (prefixWord ++ tailWord_752001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752001).length < 2 ^ (prefixWord ++ tailWord_752001).sum := by decide
  have hdescent : baseEnd_752001 < baseStart_752001 := by decide
  rcases family_descends (prefixWord ++ tailWord_752001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752031 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 1, 4]
def baseStart_752031 : Nat := 118140960795 + 752031 * 2 ^ 59
def prefixEnd_752031 : Nat := 4983230072969 + 3 ^ 40 * 752031 * 2
def baseEnd_752031 : Nat := 257435580054301605969319

theorem tailTrace_752031 : CollatzResearch.WordTrace tailWord_752031 prefixEnd_752031 257435580054301605969319 := by
  unfold tailWord_752031
  simp only [CollatzResearch.WordTrace]
  refine ⟨27428823938527598514543947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18285882625685065676362631 27428823938527598514543947)
  ·
    refine ⟨41143235907791397771815921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27428823938527598514543947 41143235907791397771815921)
    ·
      refine ⟨30857426930843548328861941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41143235907791397771815921 30857426930843548328861941)
      ·
        refine ⟨2892883774766582655830807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30857426930843548328861941 2892883774766582655830807)
        ·
          refine ⟨4339325662149873983746211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892883774766582655830807 4339325662149873983746211)
          ·
            refine ⟨6508988493224810975619317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339325662149873983746211 6508988493224810975619317)
            ·
              refine ⟨610217671239826028964311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6508988493224810975619317 610217671239826028964311)
              ·
                refine ⟨915326506859739043446467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610217671239826028964311 915326506859739043446467)
                ·
                  refine ⟨1372989760289608565169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915326506859739043446467 1372989760289608565169701)
                  ·
                    refine ⟨257435580054301605969319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372989760289608565169701 257435580054301605969319)
                    ·
                      rfl

theorem cell22_752031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_752031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752031 prefixEnd_752031 := by exact prefixLift 752031
  have htrace : WordTrace (prefixWord ++ tailWord_752031) baseStart_752031 baseEnd_752031 := by
    simpa [prefixWord, tailWord_752031, baseEnd_752031] using wordTrace_append hprefix tailTrace_752031
  have hstable : (prefixWord ++ tailWord_752031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752031).length < 2 ^ (prefixWord ++ tailWord_752031).sum := by decide
  have hdescent : baseEnd_752031 < baseStart_752031 := by decide
  rcases family_descends (prefixWord ++ tailWord_752031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752061 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_752061 : Nat := 118140960795 + 752061 * 2 ^ 59
def prefixEnd_752061 : Nat := 4983230072969 + 3 ^ 40 * 752061 * 2
def baseEnd_752061 : Nat := 257445849667391527719227

theorem tailTrace_752061 : CollatzResearch.WordTrace tailWord_752061 prefixEnd_752061 257445849667391527719227 := by
  unfold tailWord_752061
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429918128418913638136037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18286612085612609092090691 27429918128418913638136037)
  ·
    refine ⟨5143109649078546307150507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27429918128418913638136037 5143109649078546307150507)
    ·
      refine ⟨7714664473617819460725761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143109649078546307150507 7714664473617819460725761)
      ·
        refine ⟨5785998355213364595544321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7714664473617819460725761 5785998355213364595544321)
        ·
          refine ⟨4339498766410023446658241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5785998355213364595544321 4339498766410023446658241)
          ·
            refine ⟨3254624074807517584993681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4339498766410023446658241 3254624074807517584993681)
            ·
              refine ⟨2440968056105638188745261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254624074807517584993681 2440968056105638188745261)
              ·
                refine ⟨915363021039614320779473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440968056105638188745261 915363021039614320779473)
                ·
                  refine ⟨686522265779710740584605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915363021039614320779473 686522265779710740584605)
                  ·
                    refine ⟨257445849667391527719227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686522265779710740584605 257445849667391527719227)
                    ·
                      rfl

theorem cell22_752061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_752061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752061 prefixEnd_752061 := by exact prefixLift 752061
  have htrace : WordTrace (prefixWord ++ tailWord_752061) baseStart_752061 baseEnd_752061 := by
    simpa [prefixWord, tailWord_752061, baseEnd_752061] using wordTrace_append hprefix tailTrace_752061
  have hstable : (prefixWord ++ tailWord_752061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752061).length < 2 ^ (prefixWord ++ tailWord_752061).sum := by decide
  have hdescent : baseEnd_752061 < baseStart_752061 := by decide
  rcases family_descends (prefixWord ++ tailWord_752061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752074 : List Nat := [3, 1, 2, 1, 2, 2, 5, 6]
def baseStart_752074 : Nat := 118140960795 + 752074 * 2 ^ 59
def prefixEnd_752074 : Nat := 4983230072969 + 3 ^ 40 * 752074 * 2
def baseEnd_752074 : Nat := 28605588870340425238243

theorem tailTrace_752074 : CollatzResearch.WordTrace tailWord_752074 prefixEnd_752074 28605588870340425238243 := by
  unfold tailWord_752074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857598069342954214589819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18286928184914544572239517 6857598069342954214589819)
  ·
    refine ⟨10286397104014431321884729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6857598069342954214589819 10286397104014431321884729)
    ·
      refine ⟨7714797828010823491413547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10286397104014431321884729 7714797828010823491413547)
      ·
        refine ⟨11572196742016235237120321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714797828010823491413547 11572196742016235237120321)
        ·
          refine ⟨8679147556512176427840241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11572196742016235237120321 8679147556512176427840241)
          ·
            refine ⟨6509360667384132320880181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8679147556512176427840241 6509360667384132320880181)
            ·
              refine ⟨610252562567262405082517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6509360667384132320880181 610252562567262405082517)
              ·
                refine ⟨28605588870340425238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 610252562567262405082517 28605588870340425238243)
                ·
                  rfl

theorem cell22_752074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_752074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752074 prefixEnd_752074 := by exact prefixLift 752074
  have htrace : WordTrace (prefixWord ++ tailWord_752074) baseStart_752074 baseEnd_752074 := by
    simpa [prefixWord, tailWord_752074, baseEnd_752074] using wordTrace_append hprefix tailTrace_752074
  have hstable : (prefixWord ++ tailWord_752074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752074).length < 2 ^ (prefixWord ++ tailWord_752074).sum := by decide
  have hdescent : baseEnd_752074 < baseStart_752074 := by decide
  rcases family_descends (prefixWord ++ tailWord_752074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752082 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_752082 : Nat := 118140960795 + 752082 * 2 ^ 59
def prefixEnd_752082 : Nat := 4983230072969 + 3 ^ 40 * 752082 * 2
def baseEnd_752082 : Nat := 257453038396554472944163

theorem tailTrace_752082 : CollatzResearch.WordTrace tailWord_752082 prefixEnd_752082 257453038396554472944163 := by
  unfold tailWord_752082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857671015335708556162625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18287122707561889483100333 6857671015335708556162625)
  ·
    refine ⟨5143253261501781417121969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6857671015335708556162625 5143253261501781417121969)
    ·
      refine ⟨3857439946126336062841477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5143253261501781417121969 3857439946126336062841477)
      ·
        refine ⟨723269989898688011782777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3857439946126336062841477 723269989898688011782777)
        ·
          refine ⟨542452492424016008837083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723269989898688011782777 542452492424016008837083)
          ·
            refine ⟨813678738636024013255625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542452492424016008837083 813678738636024013255625)
            ·
              refine ⟨610259053977018009941719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813678738636024013255625 610259053977018009941719)
              ·
                refine ⟨915388580965527014912579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610259053977018009941719 915388580965527014912579)
                ·
                  refine ⟨1373082871448290522368869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915388580965527014912579 1373082871448290522368869)
                  ·
                    refine ⟨257453038396554472944163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373082871448290522368869 257453038396554472944163)
                    ·
                      rfl

theorem cell22_752082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_752082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752082 prefixEnd_752082 := by exact prefixLift 752082
  have htrace : WordTrace (prefixWord ++ tailWord_752082) baseStart_752082 baseEnd_752082 := by
    simpa [prefixWord, tailWord_752082, baseEnd_752082] using wordTrace_append hprefix tailTrace_752082
  have hstable : (prefixWord ++ tailWord_752082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752082).length < 2 ^ (prefixWord ++ tailWord_752082).sum := by decide
  have hdescent : baseEnd_752082 < baseStart_752082 := by decide
  rcases family_descends (prefixWord ++ tailWord_752082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752089 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_752089 : Nat := 118140960795 + 752089 * 2 ^ 59
def prefixEnd_752089 : Nat := 4983230072969 + 3 ^ 40 * 752089 * 2
def baseEnd_752089 : Nat := 257455434639608788019141

theorem tailTrace_752089 : CollatzResearch.WordTrace tailWord_752089 prefixEnd_752089 257455434639608788019141 := by
  unfold tailWord_752089
  simp only [CollatzResearch.WordTrace]
  refine ⟨27430939372317474420155321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18287292914878316280103547 27430939372317474420155321)
  ·
    refine ⟨20573204529238105815116491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27430939372317474420155321 20573204529238105815116491)
    ·
      refine ⟨30859806793857158722674737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20573204529238105815116491 30859806793857158722674737)
      ·
        refine ⟨23144855095392869042006053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30859806793857158722674737 23144855095392869042006053)
        ·
          refine ⟨4339660330386162945376135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23144855095392869042006053 4339660330386162945376135)
          ·
            refine ⟨6509490495579244418064203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339660330386162945376135 6509490495579244418064203)
            ·
              refine ⟨9764235743368866627096305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509490495579244418064203 9764235743368866627096305)
              ·
                refine ⟨7323176807526649970322229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9764235743368866627096305 7323176807526649970322229)
                ·
                  refine ⟨686547825705623434717709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7323176807526649970322229 686547825705623434717709)
                  ·
                    refine ⟨257455434639608788019141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686547825705623434717709 257455434639608788019141)
                    ·
                      rfl

theorem cell22_752089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_752089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752089 prefixEnd_752089 := by exact prefixLift 752089
  have htrace : WordTrace (prefixWord ++ tailWord_752089) baseStart_752089 baseEnd_752089 := by
    simpa [prefixWord, tailWord_752089, baseEnd_752089] using wordTrace_append hprefix tailTrace_752089
  have hstable : (prefixWord ++ tailWord_752089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752089).length < 2 ^ (prefixWord ++ tailWord_752089).sum := by decide
  have hdescent : baseEnd_752089 < baseStart_752089 := by decide
  rcases family_descends (prefixWord ++ tailWord_752089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752106 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_752106 : Nat := 118140960795 + 752106 * 2 ^ 59
def prefixEnd_752106 : Nat := 4983230072969 + 3 ^ 40 * 752106 * 2
def baseEnd_752106 : Nat := 257461254087026410344089

theorem tailTrace_752106 : CollatzResearch.WordTrace tailWord_752106 prefixEnd_752106 257461254087026410344089 := by
  unfold tailWord_752106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857889853313971580881043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18287706275503924215682781 6857889853313971580881043)
  ·
    refine ⟨10286834779970957371321565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6857889853313971580881043 10286834779970957371321565)
    ·
      refine ⟨3857563042489109014245587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10286834779970957371321565 3857563042489109014245587)
      ·
        refine ⟨5786344563733663521368381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857563042489109014245587 5786344563733663521368381)
        ·
          refine ⟨2169879211400123820513143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5786344563733663521368381 2169879211400123820513143)
          ·
            refine ⟨3254818817100185730769715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169879211400123820513143 3254818817100185730769715)
            ·
              refine ⟨4882228225650278596154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254818817100185730769715 4882228225650278596154573)
              ·
                refine ⟨1830835584618854473557965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4882228225650278596154573 1830835584618854473557965)
                ·
                  refine ⟨686563344232070427584237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1830835584618854473557965 686563344232070427584237)
                  ·
                    refine ⟨257461254087026410344089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686563344232070427584237 257461254087026410344089)
                    ·
                      rfl

theorem cell22_752106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_752106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752106 prefixEnd_752106 := by exact prefixLift 752106
  have htrace : WordTrace (prefixWord ++ tailWord_752106) baseStart_752106 baseEnd_752106 := by
    simpa [prefixWord, tailWord_752106, baseEnd_752106] using wordTrace_append hprefix tailTrace_752106
  have hstable : (prefixWord ++ tailWord_752106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752106).length < 2 ^ (prefixWord ++ tailWord_752106).sum := by decide
  have hdescent : baseEnd_752106 < baseStart_752106 := by decide
  rcases family_descends (prefixWord ++ tailWord_752106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752140 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_752140 : Nat := 118140960795 + 752140 * 2 ^ 59
def prefixEnd_752140 : Nat := 4983230072969 + 3 ^ 40 * 752140 * 2
def baseEnd_752140 : Nat := 257472892981861654993985

theorem tailTrace_752140 : CollatzResearch.WordTrace tailWord_752140 prefixEnd_752140 257472892981861654993985 := by
  unfold tailWord_752140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716399747566355065130937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18288532996755140086841249 13716399747566355065130937)
  ·
    refine ⟨10287299810674766298848203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13716399747566355065130937 10287299810674766298848203)
    ·
      refine ⟨15430949716012149448272305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10287299810674766298848203 15430949716012149448272305)
      ·
        refine ⟨11573212287009112086204229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15430949716012149448272305 11573212287009112086204229)
        ·
          refine ⟨2169977303814208516163293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11573212287009112086204229 2169977303814208516163293)
          ·
            refine ⟨813741488930328193561235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2169977303814208516163293 813741488930328193561235)
            ·
              refine ⟨1220612233395492290341853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813741488930328193561235 1220612233395492290341853)
              ·
                refine ⟨457729587523309608878195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1220612233395492290341853 457729587523309608878195)
                ·
                  refine ⟨686594381284964413317293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457729587523309608878195 686594381284964413317293)
                  ·
                    refine ⟨257472892981861654993985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686594381284964413317293 257472892981861654993985)
                    ·
                      rfl

theorem cell22_752140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_752140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752140 prefixEnd_752140 := by exact prefixLift 752140
  have htrace : WordTrace (prefixWord ++ tailWord_752140) baseStart_752140 baseEnd_752140 := by
    simpa [prefixWord, tailWord_752140, baseEnd_752140] using wordTrace_append hprefix tailTrace_752140
  have hstable : (prefixWord ++ tailWord_752140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752140).length < 2 ^ (prefixWord ++ tailWord_752140).sum := by decide
  have hdescent : baseEnd_752140 < baseStart_752140 := by decide
  rcases family_descends (prefixWord ++ tailWord_752140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752179 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_752179 : Nat := 118140960795 + 752179 * 2 ^ 59
def prefixEnd_752179 : Nat := 4983230072969 + 3 ^ 40 * 752179 * 2
def baseEnd_752179 : Nat := 257486243478878553268865

theorem tailTrace_752179 : CollatzResearch.WordTrace tailWord_752179 prefixEnd_752179 257486243478878553268865 := by
  unfold tailWord_752179
  simp only [CollatzResearch.WordTrace]
  refine ⟨27434221941991419790931591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18289481294660946527287727 27434221941991419790931591)
  ·
    refine ⟨41151332912987129686397387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27434221941991419790931591 41151332912987129686397387)
    ·
      refine ⟨61726999369480694529596081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41151332912987129686397387 61726999369480694529596081)
      ·
        refine ⟨46295249527110520897197061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61726999369480694529596081 46295249527110520897197061)
        ·
          refine ⟨8680359286333222668224449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46295249527110520897197061 8680359286333222668224449)
          ·
            refine ⟨6510269464749917001168337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8680359286333222668224449 6510269464749917001168337)
            ·
              refine ⟨4882702098562437750876253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6510269464749917001168337 4882702098562437750876253)
              ·
                refine ⟨1831013286960914156578595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4882702098562437750876253 1831013286960914156578595)
                ·
                  refine ⟨2746519930441371234867893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831013286960914156578595 2746519930441371234867893)
                  ·
                    refine ⟨257486243478878553268865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2746519930441371234867893 257486243478878553268865)
                    ·
                      rfl

theorem cell22_752179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_752179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752179 prefixEnd_752179 := by exact prefixLift 752179
  have htrace : WordTrace (prefixWord ++ tailWord_752179) baseStart_752179 baseEnd_752179 := by
    simpa [prefixWord, tailWord_752179, baseEnd_752179] using wordTrace_append hprefix tailTrace_752179
  have hstable : (prefixWord ++ tailWord_752179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752179).length < 2 ^ (prefixWord ++ tailWord_752179).sum := by decide
  have hdescent : baseEnd_752179 < baseStart_752179 := by decide
  rcases family_descends (prefixWord ++ tailWord_752179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752245 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_752245 : Nat := 118140960795 + 752245 * 2 ^ 59
def prefixEnd_752245 : Nat := 4983230072969 + 3 ^ 40 * 752245 * 2
def baseEnd_752245 : Nat := 257508836627676381118663

theorem tailTrace_752245 : CollatzResearch.WordTrace tailWord_752245 prefixEnd_752245 257508836627676381118663 := by
  unfold tailWord_752245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27436629159752313062834189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18291086106501542041889459 27436629159752313062834189)
  ·
    refine ⟨10288735934907117398562821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27436629159752313062834189 10288735934907117398562821)
    ·
      refine ⟨1929137987795084512230529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10288735934907117398562821 1929137987795084512230529)
      ·
        refine ⟨1446853490846313384172897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929137987795084512230529 1446853490846313384172897)
        ·
          refine ⟨1085140118134735038129673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446853490846313384172897 1085140118134735038129673)
          ·
            refine ⟨813855088601051278597255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085140118134735038129673 813855088601051278597255)
            ·
              refine ⟨1220782632901576917895883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813855088601051278597255 1220782632901576917895883)
              ·
                refine ⟨1831173949352365376843825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220782632901576917895883 1831173949352365376843825)
                ·
                  refine ⟨1373380462014274032632869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831173949352365376843825 1373380462014274032632869)
                  ·
                    refine ⟨257508836627676381118663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373380462014274032632869 257508836627676381118663)
                    ·
                      rfl

theorem cell22_752245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_752245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752245 prefixEnd_752245 := by exact prefixLift 752245
  have htrace : WordTrace (prefixWord ++ tailWord_752245) baseStart_752245 baseEnd_752245 := by
    simpa [prefixWord, tailWord_752245, baseEnd_752245] using wordTrace_append hprefix tailTrace_752245
  have hstable : (prefixWord ++ tailWord_752245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752245).length < 2 ^ (prefixWord ++ tailWord_752245).sum := by decide
  have hdescent : baseEnd_752245 < baseStart_752245 := by decide
  rcases family_descends (prefixWord ++ tailWord_752245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752318 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_752318 : Nat := 118140960795 + 752318 * 2 ^ 59
def prefixEnd_752318 : Nat := 4983230072969 + 3 ^ 40 * 752318 * 2
def baseEnd_752318 : Nat := 257533826019528524043439

theorem tailTrace_752318 : CollatzResearch.WordTrace tailWord_752318 prefixEnd_752318 257533826019528524043439 := by
  unfold tailWord_752318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429911461060980816280201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18292861125658564353494405 3429911461060980816280201)
  ·
    refine ⟨2572433595795735612210151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3429911461060980816280201 2572433595795735612210151)
    ·
      refine ⟨3858650393693603418315227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572433595795735612210151 3858650393693603418315227)
      ·
        refine ⟨5787975590540405127472841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858650393693603418315227 5787975590540405127472841)
        ·
          refine ⟨4340981692905303845604631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787975590540405127472841 4340981692905303845604631)
          ·
            refine ⟨6511472539357955768406947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340981692905303845604631 6511472539357955768406947)
            ·
              refine ⟨9767208809036933652610421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511472539357955768406947 9767208809036933652610421)
              ·
                refine ⟨915675825847212529932227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9767208809036933652610421 915675825847212529932227)
                ·
                  refine ⟨1373513738770818794898341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915675825847212529932227 1373513738770818794898341)
                  ·
                    refine ⟨257533826019528524043439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373513738770818794898341 257533826019528524043439)
                    ·
                      rfl

theorem cell22_752318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_752318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752318 prefixEnd_752318 := by exact prefixLift 752318
  have htrace : WordTrace (prefixWord ++ tailWord_752318) baseStart_752318 baseEnd_752318 := by
    simpa [prefixWord, tailWord_752318, baseEnd_752318] using wordTrace_append hprefix tailTrace_752318
  have hstable : (prefixWord ++ tailWord_752318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752318).length < 2 ^ (prefixWord ++ tailWord_752318).sum := by decide
  have hdescent : baseEnd_752318 < baseStart_752318 := by decide
  rcases family_descends (prefixWord ++ tailWord_752318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752326 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_752326 : Nat := 118140960795 + 752326 * 2 ^ 59
def prefixEnd_752326 : Nat := 4983230072969 + 3 ^ 40 * 752326 * 2
def baseEnd_752326 : Nat := 257536564583019169843415

theorem tailTrace_752326 : CollatzResearch.WordTrace tailWord_752326 prefixEnd_752326 257536564583019169843415 := by
  unfold tailWord_752326
  simp only [CollatzResearch.WordTrace]
  refine ⟨857486983514339496766651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18293055648305909264355221 857486983514339496766651)
  ·
    refine ⟨1286230475271509245149977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 857486983514339496766651 1286230475271509245149977)
    ·
      refine ⟨964672856453631933862483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1286230475271509245149977 964672856453631933862483)
      ·
        refine ⟨1447009284680447900793725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964672856453631933862483 1447009284680447900793725)
        ·
          refine ⟨542628481755167962797647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1447009284680447900793725 542628481755167962797647)
          ·
            refine ⟨813942722632751944196471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542628481755167962797647 813942722632751944196471)
            ·
              refine ⟨1220914083949127916294707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813942722632751944196471 1220914083949127916294707)
              ·
                refine ⟨1831371125923691874442061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220914083949127916294707 1831371125923691874442061)
                ·
                  refine ⟨686764172221384452915773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1831371125923691874442061 686764172221384452915773)
                  ·
                    refine ⟨257536564583019169843415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686764172221384452915773 257536564583019169843415)
                    ·
                      rfl

theorem cell22_752326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_752326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752326 prefixEnd_752326 := by exact prefixLift 752326
  have htrace : WordTrace (prefixWord ++ tailWord_752326) baseStart_752326 baseEnd_752326 := by
    simpa [prefixWord, tailWord_752326, baseEnd_752326] using wordTrace_append hprefix tailTrace_752326
  have hstable : (prefixWord ++ tailWord_752326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752326).length < 2 ^ (prefixWord ++ tailWord_752326).sum := by decide
  have hdescent : baseEnd_752326 < baseStart_752326 := by decide
  rcases family_descends (prefixWord ++ tailWord_752326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752329 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_752329 : Nat := 118140960795 + 752329 * 2 ^ 59
def prefixEnd_752329 : Nat := 4983230072969 + 3 ^ 40 * 752329 * 2
def baseEnd_752329 : Nat := 257537591544328162018405

theorem tailTrace_752329 : CollatzResearch.WordTrace tailWord_752329 prefixEnd_752329 257537591544328162018405 := by
  unfold tailWord_752329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439692891447995408892041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18293128594298663605928027 27439692891447995408892041)
  ·
    refine ⟨20579769668585996556669031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27439692891447995408892041 20579769668585996556669031)
    ·
      refine ⟨30869654502878994835003547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20579769668585996556669031 30869654502878994835003547)
      ·
        refine ⟨46304481754318492252505321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30869654502878994835003547 46304481754318492252505321)
        ·
          refine ⟨34728361315738869189378991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46304481754318492252505321 34728361315738869189378991)
          ·
            refine ⟨52092541973608303784068487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34728361315738869189378991 52092541973608303784068487)
            ·
              refine ⟨78138812960412455676102731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52092541973608303784068487 78138812960412455676102731)
              ·
                refine ⟨117208219440618683514154097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78138812960412455676102731 117208219440618683514154097)
                ·
                  refine ⟨87906164580464012635615573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117208219440618683514154097 87906164580464012635615573)
                  ·
                    refine ⟨257537591544328162018405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 87906164580464012635615573 257537591544328162018405)
                    ·
                      rfl

theorem cell22_752329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_752329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752329 prefixEnd_752329 := by exact prefixLift 752329
  have htrace : WordTrace (prefixWord ++ tailWord_752329) baseStart_752329 baseEnd_752329 := by
    simpa [prefixWord, tailWord_752329, baseEnd_752329] using wordTrace_append hprefix tailTrace_752329
  have hstable : (prefixWord ++ tailWord_752329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752329).length < 2 ^ (prefixWord ++ tailWord_752329).sum := by decide
  have hdescent : baseEnd_752329 < baseStart_752329 := by decide
  rcases family_descends (prefixWord ++ tailWord_752329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752346 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_752346 : Nat := 118140960795 + 752346 * 2 ^ 59
def prefixEnd_752346 : Nat := 4983230072969 + 3 ^ 40 * 752346 * 2
def baseEnd_752346 : Nat := 257543410991745784343353

theorem tailTrace_752346 : CollatzResearch.WordTrace tailWord_752346 prefixEnd_752346 257543410991745784343353 := by
  unfold tailWord_752346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860078233096601828065223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18293541954924271541507261 6860078233096601828065223)
  ·
    refine ⟨10290117349644902742097835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860078233096601828065223 10290117349644902742097835)
    ·
      refine ⟨15435176024467354113146753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290117349644902742097835 15435176024467354113146753)
      ·
        refine ⟨11576382018350515584860065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15435176024467354113146753 11576382018350515584860065)
        ·
          refine ⟨8682286513762886688645049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11576382018350515584860065 8682286513762886688645049)
          ·
            refine ⟨6511714885322165016483787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682286513762886688645049 6511714885322165016483787)
            ·
              refine ⟨9767572327983247524725681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511714885322165016483787 9767572327983247524725681)
              ·
                refine ⟨7325679245987435643544261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767572327983247524725681 7325679245987435643544261)
                ·
                  refine ⟨1373564858622644183164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7325679245987435643544261 1373564858622644183164549)
                  ·
                    refine ⟨257543410991745784343353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373564858622644183164549 257543410991745784343353)
                    ·
                      rfl

theorem cell22_752346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_752346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752346 prefixEnd_752346 := by exact prefixLift 752346
  have htrace : WordTrace (prefixWord ++ tailWord_752346) baseStart_752346 baseEnd_752346 := by
    simpa [prefixWord, tailWord_752346, baseEnd_752346] using wordTrace_append hprefix tailTrace_752346
  have hstable : (prefixWord ++ tailWord_752346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752346).length < 2 ^ (prefixWord ++ tailWord_752346).sum := by decide
  have hdescent : baseEnd_752346 < baseStart_752346 := by decide
  rcases family_descends (prefixWord ++ tailWord_752346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752382 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_752382 : Nat := 118140960795 + 752382 * 2 ^ 59
def prefixEnd_752382 : Nat := 4983230072969 + 3 ^ 40 * 752382 * 2
def baseEnd_752382 : Nat := 257555734527453690443243

theorem tailTrace_752382 : CollatzResearch.WordTrace tailWord_752382 prefixEnd_752382 257555734527453690443243 := by
  unfold tailWord_752382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430203245031998182571425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18294417306837323640380933 3430203245031998182571425)
  ·
    refine ⟨2572652433773998636928569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3430203245031998182571425 2572652433773998636928569)
    ·
      refine ⟨1929489325330498977696427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2572652433773998636928569 1929489325330498977696427)
      ·
        refine ⟨2894233987995748466544641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929489325330498977696427 2894233987995748466544641)
        ·
          refine ⟨2170675490996811349908481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2894233987995748466544641 2170675490996811349908481)
          ·
            refine ⟨1628006618247608512431361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170675490996811349908481 1628006618247608512431361)
            ·
              refine ⟨1221004963685706384323521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628006618247608512431361 1221004963685706384323521)
              ·
                refine ⟨915753722764279788242641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221004963685706384323521 915753722764279788242641)
                ·
                  refine ⟨686815292073209841181981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915753722764279788242641 686815292073209841181981)
                  ·
                    refine ⟨257555734527453690443243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686815292073209841181981 257555734527453690443243)
                    ·
                      rfl

theorem cell22_752382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_752382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752382 prefixEnd_752382 := by exact prefixLift 752382
  have htrace : WordTrace (prefixWord ++ tailWord_752382) baseStart_752382 baseEnd_752382 := by
    simpa [prefixWord, tailWord_752382, baseEnd_752382] using wordTrace_append hprefix tailTrace_752382
  have hstable : (prefixWord ++ tailWord_752382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752382).length < 2 ^ (prefixWord ++ tailWord_752382).sum := by decide
  have hdescent : baseEnd_752382 < baseStart_752382 := by decide
  rcases family_descends (prefixWord ++ tailWord_752382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752421 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_752421 : Nat := 118140960795 + 752421 * 2 ^ 59
def prefixEnd_752421 : Nat := 4983230072969 + 3 ^ 40 * 752421 * 2
def baseEnd_752421 : Nat := 257569085024470588718123

theorem tailTrace_752421 : CollatzResearch.WordTrace tailWord_752421 prefixEnd_752421 257569085024470588718123 := by
  unfold tailWord_752421
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443048407114695121241117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18295365604743130080827411 27443048407114695121241117)
  ·
    refine ⟨10291143152668010670465419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27443048407114695121241117 10291143152668010670465419)
    ·
      refine ⟨15436714729002016005698129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10291143152668010670465419 15436714729002016005698129)
      ·
        refine ⟨11577536046751512004273597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15436714729002016005698129 11577536046751512004273597)
        ·
          refine ⟨4341576017531817001602599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11577536046751512004273597 4341576017531817001602599)
          ·
            refine ⟨6512364026297725502403899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341576017531817001602599 6512364026297725502403899)
            ·
              refine ⟨9768546039446588253605849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512364026297725502403899 9768546039446588253605849)
              ·
                refine ⟨7326409529584941190204387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9768546039446588253605849 7326409529584941190204387)
                ·
                  refine ⟨10989614294377411785306581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326409529584941190204387 10989614294377411785306581)
                  ·
                    refine ⟨257569085024470588718123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10989614294377411785306581 257569085024470588718123)
                    ·
                      rfl

theorem cell22_752421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_752421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752421 prefixEnd_752421 := by exact prefixLift 752421
  have htrace : WordTrace (prefixWord ++ tailWord_752421) baseStart_752421 baseEnd_752421 := by
    simpa [prefixWord, tailWord_752421, baseEnd_752421] using wordTrace_append hprefix tailTrace_752421
  have hstable : (prefixWord ++ tailWord_752421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752421).length < 2 ^ (prefixWord ++ tailWord_752421).sum := by decide
  have hdescent : baseEnd_752421 < baseStart_752421 := by decide
  rcases family_descends (prefixWord ++ tailWord_752421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752485 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 4]
def baseStart_752485 : Nat := 118140960795 + 752485 * 2 ^ 59
def prefixEnd_752485 : Nat := 4983230072969 + 3 ^ 40 * 752485 * 2
def baseEnd_752485 : Nat := 85863664510798585039309

theorem tailTrace_752485 : CollatzResearch.WordTrace tailWord_752485 prefixEnd_752485 85863664510798585039309 := by
  unfold tailWord_752485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27445382678882834051570909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18296921785921889367713939 27445382678882834051570909)
  ·
    refine ⟨10292018504581062769339091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27445382678882834051570909 10292018504581062769339091)
    ·
      refine ⟨15438027756871594154008637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10292018504581062769339091 15438027756871594154008637)
      ·
        refine ⟨5789260408826847807753239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15438027756871594154008637 5789260408826847807753239)
        ·
          refine ⟨8683890613240271711629859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789260408826847807753239 8683890613240271711629859)
          ·
            refine ⟨13025835919860407567444789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8683890613240271711629859 13025835919860407567444789)
            ·
              refine ⟨1221172117486913209447949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13025835919860407567444789 1221172117486913209447949)
              ·
                refine ⟨457939544057592453542981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221172117486913209447949 457939544057592453542981)
                ·
                  refine ⟨85863664510798585039309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457939544057592453542981 85863664510798585039309)
                  ·
                    rfl

theorem cell22_752485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_752485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752485 prefixEnd_752485 := by exact prefixLift 752485
  have htrace : WordTrace (prefixWord ++ tailWord_752485) baseStart_752485 baseEnd_752485 := by
    simpa [prefixWord, tailWord_752485, baseEnd_752485] using wordTrace_append hprefix tailTrace_752485
  have hstable : (prefixWord ++ tailWord_752485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752485).length < 2 ^ (prefixWord ++ tailWord_752485).sum := by decide
  have hdescent : baseEnd_752485 < baseStart_752485 := by decide
  rcases family_descends (prefixWord ++ tailWord_752485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752496 : List Nat := [2, 1, 1, 1, 4, 1, 12]
def baseStart_752496 : Nat := 118140960795 + 752496 * 2 ^ 59
def prefixEnd_752496 : Nat := 4983230072969 + 3 ^ 40 * 752496 * 2
def baseEnd_752496 : Nat := 9540546631747977521959

theorem tailTrace_752496 : CollatzResearch.WordTrace tailWord_752496 prefixEnd_752496 9540546631747977521959 := by
  unfold tailWord_752496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722891940921491465110671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18297189254561988620147561 13722891940921491465110671)
  ·
    refine ⟨20584337911382237197666007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13722891940921491465110671 20584337911382237197666007)
    ·
      refine ⟨30876506867073355796499011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20584337911382237197666007 30876506867073355796499011)
      ·
        refine ⟨46314760300610033694748517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30876506867073355796499011 46314760300610033694748517)
        ·
          refine ⟨8684017556364381317765347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46314760300610033694748517 8684017556364381317765347)
          ·
            refine ⟨13026026334546571976648021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684017556364381317765347 13026026334546571976648021)
            ·
              refine ⟨9540546631747977521959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13026026334546571976648021 9540546631747977521959)
              ·
                rfl

theorem cell22_752496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 12].length) (baseStart_752496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752496 prefixEnd_752496 := by exact prefixLift 752496
  have htrace : WordTrace (prefixWord ++ tailWord_752496) baseStart_752496 baseEnd_752496 := by
    simpa [prefixWord, tailWord_752496, baseEnd_752496] using wordTrace_append hprefix tailTrace_752496
  have hstable : (prefixWord ++ tailWord_752496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752496).length < 2 ^ (prefixWord ++ tailWord_752496).sum := by decide
  have hdescent : baseEnd_752496 < baseStart_752496 := by decide
  rcases family_descends (prefixWord ++ tailWord_752496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752498 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_752498 : Nat := 118140960795 + 752498 * 2 ^ 59
def prefixEnd_752498 : Nat := 4983230072969 + 3 ^ 40 * 752498 * 2
def baseEnd_752498 : Nat := 257595443698068054542887

theorem tailTrace_752498 : CollatzResearch.WordTrace tailWord_752498 prefixEnd_752498 257595443698068054542887 := by
  unfold tailWord_752498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861464206958934317948537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18297237885223824847862765 6861464206958934317948537)
  ·
    refine ⟨5146098155219200738461403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6861464206958934317948537 5146098155219200738461403)
    ·
      refine ⟨7719147232828801107692105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5146098155219200738461403 7719147232828801107692105)
      ·
        refine ⟨5789360424621600830769079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7719147232828801107692105 5789360424621600830769079)
        ·
          refine ⟨8684040636932401246153619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789360424621600830769079 8684040636932401246153619)
          ·
            refine ⟨13026060955398601869230429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684040636932401246153619 13026060955398601869230429)
            ·
              refine ⟨4884772858274475700961411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13026060955398601869230429 4884772858274475700961411)
              ·
                refine ⟨7327159287411713551442117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884772858274475700961411 7327159287411713551442117)
                ·
                  refine ⟨1373842366389696290895397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7327159287411713551442117 1373842366389696290895397)
                  ·
                    refine ⟨257595443698068054542887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373842366389696290895397 257595443698068054542887)
                    ·
                      rfl

theorem cell22_752498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_752498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752498 prefixEnd_752498 := by exact prefixLift 752498
  have htrace : WordTrace (prefixWord ++ tailWord_752498) baseStart_752498 baseEnd_752498 := by
    simpa [prefixWord, tailWord_752498, baseEnd_752498] using wordTrace_append hprefix tailTrace_752498
  have hstable : (prefixWord ++ tailWord_752498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752498).length < 2 ^ (prefixWord ++ tailWord_752498).sum := by decide
  have hdescent : baseEnd_752498 < baseStart_752498 := by decide
  rcases family_descends (prefixWord ++ tailWord_752498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752502 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_752502 : Nat := 118140960795 + 752502 * 2 ^ 59
def prefixEnd_752502 : Nat := 4983230072969 + 3 ^ 40 * 752502 * 2
def baseEnd_752502 : Nat := 85865604326604459147625

theorem tailTrace_752502 : CollatzResearch.WordTrace tailWord_752502 prefixEnd_752502 85865604326604459147625 := by
  unfold tailWord_752502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715375169988827872183735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18297335146547497303293173 1715375169988827872183735)
  ·
    refine ⟨2573062754983241808275603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715375169988827872183735 2573062754983241808275603)
    ·
      refine ⟨3859594132474862712413405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573062754983241808275603 3859594132474862712413405)
      ·
        refine ⟨1447347799678073517155027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3859594132474862712413405 1447347799678073517155027)
        ·
          refine ⟨2171021699517110275732541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447347799678073517155027 2171021699517110275732541)
          ·
            refine ⟨814133137318916353399703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171021699517110275732541 814133137318916353399703)
            ·
              refine ⟨1221199705978374530099555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814133137318916353399703 1221199705978374530099555)
              ·
                refine ⟨1831799558967561795149333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221199705978374530099555 1831799558967561795149333)
                ·
                  refine ⟨85865604326604459147625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1831799558967561795149333 85865604326604459147625)
                  ·
                    rfl

theorem cell22_752502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_752502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752502 prefixEnd_752502 := by exact prefixLift 752502
  have htrace : WordTrace (prefixWord ++ tailWord_752502) baseStart_752502 baseEnd_752502 := by
    simpa [prefixWord, tailWord_752502, baseEnd_752502] using wordTrace_append hprefix tailTrace_752502
  have hstable : (prefixWord ++ tailWord_752502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752502).length < 2 ^ (prefixWord ++ tailWord_752502).sum := by decide
  have hdescent : baseEnd_752502 < baseStart_752502 := by decide
  rcases family_descends (prefixWord ++ tailWord_752502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752517 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_752517 : Nat := 118140960795 + 752517 * 2 ^ 59
def prefixEnd_752517 : Nat := 4983230072969 + 3 ^ 40 * 752517 * 2
def baseEnd_752517 : Nat := 257601947786358338317829

theorem tailTrace_752517 : CollatzResearch.WordTrace tailWord_752517 prefixEnd_752517 257601947786358338317829 := by
  unfold tailWord_752517
  simp only [CollatzResearch.WordTrace]
  refine ⟨27446549814766903516735805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18297699876511269011157203 27446549814766903516735805)
  ·
    refine ⟨10292456180537588818775927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27446549814766903516735805 10292456180537588818775927)
    ·
      refine ⟨15438684270806383228163891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10292456180537588818775927 15438684270806383228163891)
      ·
        refine ⟨23158026406209574842245837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438684270806383228163891 23158026406209574842245837)
        ·
          refine ⟨8684259902328590565842189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23158026406209574842245837 8684259902328590565842189)
          ·
            refine ⟨3256597463373221462190821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8684259902328590565842189 3256597463373221462190821)
            ·
              refine ⟨610612024382479024160779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3256597463373221462190821 610612024382479024160779)
              ·
                refine ⟨915918036573718536241169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610612024382479024160779 915918036573718536241169)
                ·
                  refine ⟨686938527430288902180877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915918036573718536241169 686938527430288902180877)
                  ·
                    refine ⟨257601947786358338317829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686938527430288902180877 257601947786358338317829)
                    ·
                      rfl

theorem cell22_752517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_752517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752517 prefixEnd_752517 := by exact prefixLift 752517
  have htrace : WordTrace (prefixWord ++ tailWord_752517) baseStart_752517 baseEnd_752517 := by
    simpa [prefixWord, tailWord_752517, baseEnd_752517] using wordTrace_append hprefix tailTrace_752517
  have hstable : (prefixWord ++ tailWord_752517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752517).length < 2 ^ (prefixWord ++ tailWord_752517).sum := by decide
  have hdescent : baseEnd_752517 < baseStart_752517 := by decide
  rcases family_descends (prefixWord ++ tailWord_752517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752534 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_752534 : Nat := 118140960795 + 752534 * 2 ^ 59
def prefixEnd_752534 : Nat := 4983230072969 + 3 ^ 40 * 752534 * 2
def baseEnd_752534 : Nat := 257607767233775960642777

theorem tailTrace_752534 : CollatzResearch.WordTrace tailWord_752534 prefixEnd_752534 257607767233775960642777 := by
  unfold tailWord_752534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715448115981582213756541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18298113237136876946736437 1715448115981582213756541)
  ·
    refine ⟨643293043493093330158703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1715448115981582213756541 643293043493093330158703)
    ·
      refine ⟨964939565239639995238055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643293043493093330158703 964939565239639995238055)
      ·
        refine ⟨1447409347859459992857083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964939565239639995238055 1447409347859459992857083)
        ·
          refine ⟨2171114021789189989285625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447409347859459992857083 2171114021789189989285625)
          ·
            refine ⟨1628335516341892491964219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171114021789189989285625 1628335516341892491964219)
            ·
              refine ⟨2442503274512838737946329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628335516341892491964219 2442503274512838737946329)
              ·
                refine ⟨1831877455884629053459747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442503274512838737946329 1831877455884629053459747)
                ·
                  refine ⟨2747816183826943580189621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831877455884629053459747 2747816183826943580189621)
                  ·
                    refine ⟨257607767233775960642777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2747816183826943580189621 257607767233775960642777)
                    ·
                      rfl

theorem cell22_752534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_752534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752534 prefixEnd_752534 := by exact prefixLift 752534
  have htrace : WordTrace (prefixWord ++ tailWord_752534) baseStart_752534 baseEnd_752534 := by
    simpa [prefixWord, tailWord_752534, baseEnd_752534] using wordTrace_append hprefix tailTrace_752534
  have hstable : (prefixWord ++ tailWord_752534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752534).length < 2 ^ (prefixWord ++ tailWord_752534).sum := by decide
  have hdescent : baseEnd_752534 < baseStart_752534 := by decide
  rcases family_descends (prefixWord ++ tailWord_752534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752633 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_752633 : Nat := 118140960795 + 752633 * 2 ^ 59
def prefixEnd_752633 : Nat := 4983230072969 + 3 ^ 40 * 752633 * 2
def baseEnd_752633 : Nat := 257641656956972702417473

theorem tailTrace_752633 : CollatzResearch.WordTrace tailWord_752633 prefixEnd_752633 257641656956972702417473 := by
  unfold tailWord_752633
  simp only [CollatzResearch.WordTrace]
  refine ⟨27450780682346655327958553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18300520454897770218639035 27450780682346655327958553)
  ·
    refine ⟨20588085511759991495968915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27450780682346655327958553 20588085511759991495968915)
    ·
      refine ⟨30882128267639987243953373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20588085511759991495968915 30882128267639987243953373)
      ·
        refine ⟨11580798100364995216482515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30882128267639987243953373 11580798100364995216482515)
        ·
          refine ⟨17371197150547492824723773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11580798100364995216482515 17371197150547492824723773)
          ·
            refine ⟨6514198931455309809271415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17371197150547492824723773 6514198931455309809271415)
            ·
              refine ⟨9771298397182964713907123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514198931455309809271415 9771298397182964713907123)
              ·
                refine ⟨14656947595774447070860685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771298397182964713907123 14656947595774447070860685)
                ·
                  refine ⟨5496355348415417651572757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14656947595774447070860685 5496355348415417651572757)
                  ·
                    refine ⟨257641656956972702417473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5496355348415417651572757 257641656956972702417473)
                    ·
                      rfl

theorem cell22_752633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_752633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752633 prefixEnd_752633 := by exact prefixLift 752633
  have htrace : WordTrace (prefixWord ++ tailWord_752633) baseStart_752633 baseEnd_752633 := by
    simpa [prefixWord, tailWord_752633, baseEnd_752633] using wordTrace_append hprefix tailTrace_752633
  have hstable : (prefixWord ++ tailWord_752633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752633).length < 2 ^ (prefixWord ++ tailWord_752633).sum := by decide
  have hdescent : baseEnd_752633 < baseStart_752633 := by decide
  rcases family_descends (prefixWord ++ tailWord_752633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752650 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_752650 : Nat := 118140960795 + 752650 * 2 ^ 59
def prefixEnd_752650 : Nat := 4983230072969 + 3 ^ 40 * 752650 * 2
def baseEnd_752650 : Nat := 257647476404390324742421

theorem tailTrace_752650 : CollatzResearch.WordTrace tailWord_752650 prefixEnd_752650 257647476404390324742421 := by
  unfold tailWord_752650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6862850180821266807831851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18300933815523378154218269 6862850180821266807831851)
  ·
    refine ⟨10294275271231900211747777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6862850180821266807831851 10294275271231900211747777)
    ·
      refine ⟨7720706453423925158810833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10294275271231900211747777 7720706453423925158810833)
      ·
        refine ⟨5790529840067943869108125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7720706453423925158810833 5790529840067943869108125)
        ·
          refine ⟨2171448690025478950915547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5790529840067943869108125 2171448690025478950915547)
          ·
            refine ⟨3257173035038218426373321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171448690025478950915547 3257173035038218426373321)
            ·
              refine ⟨2442879776278663819779991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257173035038218426373321 2442879776278663819779991)
              ·
                refine ⟨3664319664417995729669987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442879776278663819779991 3664319664417995729669987)
                ·
                  refine ⟨5496479496626993594504981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664319664417995729669987 5496479496626993594504981)
                  ·
                    refine ⟨257647476404390324742421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5496479496626993594504981 257647476404390324742421)
                    ·
                      rfl

theorem cell22_752650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_752650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752650 prefixEnd_752650 := by exact prefixLift 752650
  have htrace : WordTrace (prefixWord ++ tailWord_752650) baseStart_752650 baseEnd_752650 := by
    simpa [prefixWord, tailWord_752650, baseEnd_752650] using wordTrace_append hprefix tailTrace_752650
  have hstable : (prefixWord ++ tailWord_752650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752650).length < 2 ^ (prefixWord ++ tailWord_752650).sum := by decide
  have hdescent : baseEnd_752650 < baseStart_752650 := by decide
  rcases family_descends (prefixWord ++ tailWord_752650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752654 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_752654 : Nat := 118140960795 + 752654 * 2 ^ 59
def prefixEnd_752654 : Nat := 4983230072969 + 3 ^ 40 * 752654 * 2
def baseEnd_752654 : Nat := 85882948562045215880803

theorem tailTrace_752654 : CollatzResearch.WordTrace tailWord_752654 prefixEnd_752654 85882948562045215880803 := by
  unfold tailWord_752654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431443326908821989309127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18301031076847050609648677 3431443326908821989309127)
  ·
    refine ⟨5147164990363232983963691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3431443326908821989309127 5147164990363232983963691)
    ·
      refine ⟨7720747485544849475945537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5147164990363232983963691 7720747485544849475945537)
      ·
        refine ⟨5790560614158637106959153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7720747485544849475945537 5790560614158637106959153)
        ·
          refine ⟨4342920460618977830219365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5790560614158637106959153 4342920460618977830219365)
          ·
            refine ⟨814297586366058343166131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4342920460618977830219365 814297586366058343166131)
            ·
              refine ⟨1221446379549087514749197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814297586366058343166131 1221446379549087514749197)
              ·
                refine ⟨458042392330907818030949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221446379549087514749197 458042392330907818030949)
                ·
                  refine ⟨85882948562045215880803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458042392330907818030949 85882948562045215880803)
                  ·
                    rfl

theorem cell22_752654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_752654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752654 prefixEnd_752654 := by exact prefixLift 752654
  have htrace : WordTrace (prefixWord ++ tailWord_752654) baseStart_752654 baseEnd_752654 := by
    simpa [prefixWord, tailWord_752654, baseEnd_752654] using wordTrace_append hprefix tailTrace_752654
  have hstable : (prefixWord ++ tailWord_752654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752654).length < 2 ^ (prefixWord ++ tailWord_752654).sum := by decide
  have hdescent : baseEnd_752654 < baseStart_752654 := by decide
  rcases family_descends (prefixWord ++ tailWord_752654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752682 : List Nat := [3, 1, 4, 1, 3, 1, 2, 7]
def baseStart_752682 : Nat := 118140960795 + 752682 * 2 ^ 59
def prefixEnd_752682 : Nat := 4983230072969 + 3 ^ 40 * 752682 * 2
def baseEnd_752682 : Nat := 28628714517594767549147

theorem tailTrace_752682 : CollatzResearch.WordTrace tailWord_752682 prefixEnd_752682 28628714517594767549147 := by
  unfold tailWord_752682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863141964792284174123075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18301711906112757797661533 6863141964792284174123075)
  ·
    refine ⟨10294712947188426261184613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6863141964792284174123075 10294712947188426261184613)
    ·
      refine ⟨1930258677597829923972115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10294712947188426261184613 1930258677597829923972115)
      ·
        refine ⟨2895388016396744885958173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930258677597829923972115 2895388016396744885958173)
        ·
          refine ⟨1085770506148779332234315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2895388016396744885958173 1085770506148779332234315)
          ·
            refine ⟨1628655759223168998351473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085770506148779332234315 1628655759223168998351473)
            ·
              refine ⟨1221491819417376748763605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628655759223168998351473 1221491819417376748763605)
              ·
                refine ⟨28628714517594767549147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1221491819417376748763605 28628714517594767549147)
                ·
                  rfl

theorem cell22_752682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_752682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752682 prefixEnd_752682 := by exact prefixLift 752682
  have htrace : WordTrace (prefixWord ++ tailWord_752682) baseStart_752682 baseEnd_752682 := by
    simpa [prefixWord, tailWord_752682, baseEnd_752682] using wordTrace_append hprefix tailTrace_752682
  have hstable : (prefixWord ++ tailWord_752682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752682).length < 2 ^ (prefixWord ++ tailWord_752682).sum := by decide
  have hdescent : baseEnd_752682 < baseStart_752682 := by decide
  rcases family_descends (prefixWord ++ tailWord_752682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752725 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_752725 : Nat := 118140960795 + 752725 * 2 ^ 59
def prefixEnd_752725 : Nat := 4983230072969 + 3 ^ 40 * 752725 * 2
def baseEnd_752725 : Nat := 257673150437115129117191

theorem tailTrace_752725 : CollatzResearch.WordTrace tailWord_752725 prefixEnd_752725 257673150437115129117191 := by
  unfold tailWord_752725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27454136198013355040307629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18302757465342236693538419 27454136198013355040307629)
  ·
    refine ⟨10295301074255008140115361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27454136198013355040307629 10295301074255008140115361)
    ·
      refine ⟨7721475805691256105086521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10295301074255008140115361 7721475805691256105086521)
      ·
        refine ⟨5791106854268442078814891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7721475805691256105086521 5791106854268442078814891)
        ·
          refine ⟨8686660281402663118222337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791106854268442078814891 8686660281402663118222337)
          ·
            refine ⟨6514995211051997338666753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686660281402663118222337 6514995211051997338666753)
            ·
              refine ⟨4886246408288998004000065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6514995211051997338666753 4886246408288998004000065)
              ·
                refine ⟨3664684806216748503000049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886246408288998004000065 3664684806216748503000049)
                ·
                  refine ⟨2748513604662561377250037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3664684806216748503000049 2748513604662561377250037)
                  ·
                    refine ⟨257673150437115129117191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2748513604662561377250037 257673150437115129117191)
                    ·
                      rfl

theorem cell22_752725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_752725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752725 prefixEnd_752725 := by exact prefixLift 752725
  have htrace : WordTrace (prefixWord ++ tailWord_752725) baseStart_752725 baseEnd_752725 := by
    simpa [prefixWord, tailWord_752725, baseEnd_752725] using wordTrace_append hprefix tailTrace_752725
  have hstable : (prefixWord ++ tailWord_752725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752725).length < 2 ^ (prefixWord ++ tailWord_752725).sum := by decide
  have hdescent : baseEnd_752725 < baseStart_752725 := by decide
  rcases family_descends (prefixWord ++ tailWord_752725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752800 : List Nat := [2, 1, 1, 4, 2, 1, 2, 9]
def baseStart_752800 : Nat := 118140960795 + 752800 * 2 ^ 59
def prefixEnd_752800 : Nat := 4983230072969 + 3 ^ 40 * 752800 * 2
def baseEnd_752800 : Nat := 28633202718871103721329

theorem tailTrace_752800 : CollatzResearch.WordTrace tailWord_752800 prefixEnd_752800 28633202718871103721329 := by
  unfold tailWord_752800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728435836370821424643927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18304581115161095232858569 13728435836370821424643927)
  ·
    refine ⟨20592653754556232136965891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13728435836370821424643927 20592653754556232136965891)
    ·
      refine ⟨30888980631834348205448837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20592653754556232136965891 30888980631834348205448837)
      ·
        refine ⟨5791683868468940288521657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30888980631834348205448837 5791683868468940288521657)
        ·
          refine ⟨4343762901351705216391243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5791683868468940288521657 4343762901351705216391243)
          ·
            refine ⟨6515644352027557824586865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343762901351705216391243 6515644352027557824586865)
            ·
              refine ⟨4886733264020668368440149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6515644352027557824586865 4886733264020668368440149)
              ·
                refine ⟨28633202718871103721329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4886733264020668368440149 28633202718871103721329)
                ·
                  rfl

theorem cell22_752800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_752800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752800 prefixEnd_752800 := by exact prefixLift 752800
  have htrace : WordTrace (prefixWord ++ tailWord_752800) baseStart_752800 baseEnd_752800 := by
    simpa [prefixWord, tailWord_752800, baseEnd_752800] using wordTrace_append hprefix tailTrace_752800
  have hstable : (prefixWord ++ tailWord_752800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752800).length < 2 ^ (prefixWord ++ tailWord_752800).sum := by decide
  have hdescent : baseEnd_752800 < baseStart_752800 := by decide
  rcases family_descends (prefixWord ++ tailWord_752800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752804 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_752804 : Nat := 118140960795 + 752804 * 2 ^ 59
def prefixEnd_752804 : Nat := 4983230072969 + 3 ^ 40 * 752804 * 2
def baseEnd_752804 : Nat := 257700193751585256391949

theorem tailTrace_752804 : CollatzResearch.WordTrace tailWord_752804 prefixEnd_752804 257700193751585256391949 := by
  unfold tailWord_752804
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728508782363575766216733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18304678376484767688288977 13728508782363575766216733)
  ·
    refine ⟨5148190793386340912331275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13728508782363575766216733 5148190793386340912331275)
    ·
      refine ⟨7722286190079511368496913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148190793386340912331275 7722286190079511368496913)
      ·
        refine ⟨5791714642559633526372685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7722286190079511368496913 5791714642559633526372685)
        ·
          refine ⟨2171892990959862572389757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5791714642559633526372685 2171892990959862572389757)
          ·
            refine ⟨814459871609948464646159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171892990959862572389757 814459871609948464646159)
            ·
              refine ⟨1221689807414922696969239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814459871609948464646159 1221689807414922696969239)
              ·
                refine ⟨1832534711122384045453859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221689807414922696969239 1832534711122384045453859)
                ·
                  refine ⟨2748802066683576068180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832534711122384045453859 2748802066683576068180789)
                  ·
                    refine ⟨257700193751585256391949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2748802066683576068180789 257700193751585256391949)
                    ·
                      rfl

theorem cell22_752804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_752804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752804 prefixEnd_752804 := by exact prefixLift 752804
  have htrace : WordTrace (prefixWord ++ tailWord_752804) baseStart_752804 baseEnd_752804 := by
    simpa [prefixWord, tailWord_752804, baseEnd_752804] using wordTrace_append hprefix tailTrace_752804
  have hstable : (prefixWord ++ tailWord_752804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752804).length < 2 ^ (prefixWord ++ tailWord_752804).sum := by decide
  have hdescent : baseEnd_752804 < baseStart_752804 := by decide
  rcases family_descends (prefixWord ++ tailWord_752804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752817 : List Nat := [1, 2, 2, 5, 1, 2, 1, 8]
def baseStart_752817 : Nat := 118140960795 + 752817 * 2 ^ 59
def prefixEnd_752817 : Nat := 4983230072969 + 3 ^ 40 * 752817 * 2
def baseEnd_752817 : Nat := 28633849324139728424101

theorem tailTrace_752817 : CollatzResearch.WordTrace tailWord_752817 prefixEnd_752817 28633849324139728424101 := by
  unfold tailWord_752817
  simp only [CollatzResearch.WordTrace]
  refine ⟨27457491713680054752656705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18304994475786703168437803 27457491713680054752656705)
  ·
    refine ⟨20593118785260041064492529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27457491713680054752656705 20593118785260041064492529)
    ·
      refine ⟨15444839088945030798369397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20593118785260041064492529 15444839088945030798369397)
      ·
        refine ⟨1447953664588596637347131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15444839088945030798369397 1447953664588596637347131)
        ·
          refine ⟨2171930496882894956020697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447953664588596637347131 2171930496882894956020697)
          ·
            refine ⟨1628947872662171217015523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171930496882894956020697 1628947872662171217015523)
            ·
              refine ⟨2443421808993256825523285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628947872662171217015523 2443421808993256825523285)
              ·
                refine ⟨28633849324139728424101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2443421808993256825523285 28633849324139728424101)
                ·
                  rfl

theorem cell22_752817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 8].length) (baseStart_752817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752817 prefixEnd_752817 := by exact prefixLift 752817
  have htrace : WordTrace (prefixWord ++ tailWord_752817) baseStart_752817 baseEnd_752817 := by
    simpa [prefixWord, tailWord_752817, baseEnd_752817] using wordTrace_append hprefix tailTrace_752817
  have hstable : (prefixWord ++ tailWord_752817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752817).length < 2 ^ (prefixWord ++ tailWord_752817).sum := by decide
  have hdescent : baseEnd_752817 < baseStart_752817 := by decide
  rcases family_descends (prefixWord ++ tailWord_752817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752900 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_752900 : Nat := 118140960795 + 752900 * 2 ^ 59
def prefixEnd_752900 : Nat := 4983230072969 + 3 ^ 40 * 752900 * 2
def baseEnd_752900 : Nat := 257733056513473005991655

theorem tailTrace_752900 : CollatzResearch.WordTrace tailWord_752900 prefixEnd_752900 257733056513473005991655 := by
  unfold tailWord_752900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730259486189679963964077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18307012648252906618618769 13730259486189679963964077)
  ·
    refine ⟨5148847307321129986486529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13730259486189679963964077 5148847307321129986486529)
    ·
      refine ⟨3861635480490847489864897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5148847307321129986486529 3861635480490847489864897)
      ·
        refine ⟨2896226610368135617398673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3861635480490847489864897 2896226610368135617398673)
        ·
          refine ⟨2172169957776101713049005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2896226610368135617398673 2172169957776101713049005)
          ·
            refine ⟨814563734166038142393377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2172169957776101713049005 814563734166038142393377)
            ·
              refine ⟨610922800624528606795033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814563734166038142393377 610922800624528606795033)
              ·
                refine ⟨458192100468396455096275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610922800624528606795033 458192100468396455096275)
                ·
                  refine ⟨687288150702594682644413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458192100468396455096275 687288150702594682644413)
                  ·
                    refine ⟨257733056513473005991655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687288150702594682644413 257733056513473005991655)
                    ·
                      rfl

theorem cell22_752900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_752900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752900 prefixEnd_752900 := by exact prefixLift 752900
  have htrace : WordTrace (prefixWord ++ tailWord_752900) baseStart_752900 baseEnd_752900 := by
    simpa [prefixWord, tailWord_752900, baseEnd_752900] using wordTrace_append hprefix tailTrace_752900
  have hstable : (prefixWord ++ tailWord_752900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752900).length < 2 ^ (prefixWord ++ tailWord_752900).sum := by decide
  have hdescent : baseEnd_752900 < baseStart_752900 := by decide
  rcases family_descends (prefixWord ++ tailWord_752900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752956 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_752956 : Nat := 118140960795 + 752956 * 2 ^ 59
def prefixEnd_752956 : Nat := 4983230072969 + 3 ^ 40 * 752956 * 2
def baseEnd_752956 : Nat := 257752226457907526591483

theorem tailTrace_752956 : CollatzResearch.WordTrace tailWord_752956 prefixEnd_752956 257752226457907526591483 := by
  unfold tailWord_752956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13731280730088240745983361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18308374306784320994644481 13731280730088240745983361)
  ·
    refine ⟨10298460547566180559487521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13731280730088240745983361 10298460547566180559487521)
    ·
      refine ⟨7723845410674635419615641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10298460547566180559487521 7723845410674635419615641)
      ·
        refine ⟨5792884058005976564711731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7723845410674635419615641 5792884058005976564711731)
        ·
          refine ⟨8689326087008964847067597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792884058005976564711731 8689326087008964847067597)
          ·
            refine ⟨3258497282628361817650349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8689326087008964847067597 3258497282628361817650349)
            ·
              refine ⟨1221936480985635681618881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3258497282628361817650349 1221936480985635681618881)
              ·
                refine ⟨916452360739226761214161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221936480985635681618881 916452360739226761214161)
                ·
                  refine ⟨687339270554420070910621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916452360739226761214161 687339270554420070910621)
                  ·
                    refine ⟨257752226457907526591483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687339270554420070910621 257752226457907526591483)
                    ·
                      rfl

theorem cell22_752956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_752956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752956 prefixEnd_752956 := by exact prefixLift 752956
  have htrace : WordTrace (prefixWord ++ tailWord_752956) baseStart_752956 baseEnd_752956 := by
    simpa [prefixWord, tailWord_752956, baseEnd_752956] using wordTrace_append hprefix tailTrace_752956
  have hstable : (prefixWord ++ tailWord_752956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752956).length < 2 ^ (prefixWord ++ tailWord_752956).sum := by decide
  have hdescent : baseEnd_752956 < baseStart_752956 := by decide
  rcases family_descends (prefixWord ++ tailWord_752956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752984 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_752984 : Nat := 118140960795 + 752984 * 2 ^ 59
def prefixEnd_752984 : Nat := 4983230072969 + 3 ^ 40 * 752984 * 2
def baseEnd_752984 : Nat := 257761811430124786891397

theorem tailTrace_752984 : CollatzResearch.WordTrace tailWord_752984 prefixEnd_752984 257761811430124786891397 := by
  unfold tailWord_752984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13731791352037521136993003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18309055136050028182657337 13731791352037521136993003)
  ·
    refine ⟨20597687028056281705489505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13731791352037521136993003 20597687028056281705489505)
    ·
      refine ⟨15448265271042211279117129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20597687028056281705489505 15448265271042211279117129)
      ·
        refine ⟨11586198953281658459337847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15448265271042211279117129 11586198953281658459337847)
        ·
          refine ⟨17379298429922487689006771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11586198953281658459337847 17379298429922487689006771)
          ·
            refine ⟨26068947644883731533510157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17379298429922487689006771 26068947644883731533510157)
            ·
              refine ⟨9775855366831399325066309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26068947644883731533510157 9775855366831399325066309)
              ·
                refine ⟨1832972881280887373449933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9775855366831399325066309 1832972881280887373449933)
                ·
                  refine ⟨687364830480332765043725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1832972881280887373449933 687364830480332765043725)
                  ·
                    refine ⟨257761811430124786891397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687364830480332765043725 257761811430124786891397)
                    ·
                      rfl

theorem cell22_752984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_752984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752984 prefixEnd_752984 := by exact prefixLift 752984
  have htrace : WordTrace (prefixWord ++ tailWord_752984) baseStart_752984 baseEnd_752984 := by
    simpa [prefixWord, tailWord_752984, baseEnd_752984] using wordTrace_append hprefix tailTrace_752984
  have hstable : (prefixWord ++ tailWord_752984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752984).length < 2 ^ (prefixWord ++ tailWord_752984).sum := by decide
  have hdescent : baseEnd_752984 < baseStart_752984 := by decide
  rcases family_descends (prefixWord ++ tailWord_752984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752997 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 9]
def baseStart_752997 : Nat := 118140960795 + 752997 * 2 ^ 59
def prefixEnd_752997 : Nat := 4983230072969 + 3 ^ 40 * 752997 * 2
def baseEnd_752997 : Nat := 85922087198599028772119

theorem tailTrace_752997 : CollatzResearch.WordTrace tailWord_752997 prefixEnd_752997 85922087198599028772119 := by
  unfold tailWord_752997
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464056853027945494209245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18309371235351963662806163 27464056853027945494209245)
  ·
    refine ⟨10299021319885479560328467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27464056853027945494209245 10299021319885479560328467)
    ·
      refine ⟨15448531979828219340492701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299021319885479560328467 15448531979828219340492701)
      ·
        refine ⟨5793199492435582252684763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15448531979828219340492701 5793199492435582252684763)
        ·
          refine ⟨8689799238653373379027145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793199492435582252684763 8689799238653373379027145)
          ·
            refine ⟨6517349428990030034270359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8689799238653373379027145 6517349428990030034270359)
            ·
              refine ⟨9776024143485045051405539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517349428990030034270359 9776024143485045051405539)
              ·
                refine ⟨14664036215227567577108309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776024143485045051405539 14664036215227567577108309)
                ·
                  refine ⟨85922087198599028772119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14664036215227567577108309 85922087198599028772119)
                  ·
                    rfl

theorem cell22_752997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_752997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_752997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_752997 prefixEnd_752997 := by exact prefixLift 752997
  have htrace : WordTrace (prefixWord ++ tailWord_752997) baseStart_752997 baseEnd_752997 := by
    simpa [prefixWord, tailWord_752997, baseEnd_752997] using wordTrace_append hprefix tailTrace_752997
  have hstable : (prefixWord ++ tailWord_752997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752997).length < 2 ^ (prefixWord ++ tailWord_752997).sum := by decide
  have hdescent : baseEnd_752997 < baseStart_752997 := by decide
  rcases family_descends (prefixWord ++ tailWord_752997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753001 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 1, 3]
def baseStart_753001 : Nat := 118140960795 + 753001 * 2 ^ 59
def prefixEnd_753001 : Nat := 4983230072969 + 3 ^ 40 * 753001 * 2
def baseEnd_753001 : Nat := 257767630877542409216345

theorem tailTrace_753001 : CollatzResearch.WordTrace tailWord_753001 prefixEnd_753001 257767630877542409216345 := by
  unfold tailWord_753001
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464202745013454177354857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18309468496675636118236571 27464202745013454177354857)
  ·
    refine ⟨20598152058760090633016143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27464202745013454177354857 20598152058760090633016143)
    ·
      refine ⟨30897228088140135949524215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20598152058760090633016143 30897228088140135949524215)
      ·
        refine ⟨46345842132210203924286323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30897228088140135949524215 46345842132210203924286323)
        ·
          refine ⟨69518763198315305886429485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46345842132210203924286323 69518763198315305886429485)
          ·
            refine ⟨26069536199368239707411057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69518763198315305886429485 26069536199368239707411057)
            ·
              refine ⟨19552152149526179780558293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26069536199368239707411057 19552152149526179780558293)
              ·
                refine ⟨458253566004519838606835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19552152149526179780558293 458253566004519838606835)
                ·
                  refine ⟨687380349006779757910253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458253566004519838606835 687380349006779757910253)
                  ·
                    refine ⟨257767630877542409216345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687380349006779757910253 257767630877542409216345)
                    ·
                      rfl

theorem cell22_753001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_753001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753001 prefixEnd_753001 := by exact prefixLift 753001
  have htrace : WordTrace (prefixWord ++ tailWord_753001) baseStart_753001 baseEnd_753001 := by
    simpa [prefixWord, tailWord_753001, baseEnd_753001] using wordTrace_append hprefix tailTrace_753001
  have hstable : (prefixWord ++ tailWord_753001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753001).length < 2 ^ (prefixWord ++ tailWord_753001).sum := by decide
  have hdescent : baseEnd_753001 < baseStart_753001 := by decide
  rcases family_descends (prefixWord ++ tailWord_753001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753031 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 5]
def baseStart_753031 : Nat := 118140960795 + 753031 * 2 ^ 59
def prefixEnd_753031 : Nat := 4983230072969 + 3 ^ 40 * 753031 * 2
def baseEnd_753031 : Nat := 85925966830210776988751

theorem tailTrace_753031 : CollatzResearch.WordTrace tailWord_753031 prefixEnd_753031 85925966830210776988751 := by
  unfold tailWord_753031
  simp only [CollatzResearch.WordTrace]
  refine ⟨27465296934904769300946947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18310197956603179533964631 27465296934904769300946947)
  ·
    refine ⟨41197945402357153951420421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27465296934904769300946947 41197945402357153951420421)
    ·
      refine ⟨7724614762941966365891329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41197945402357153951420421 7724614762941966365891329)
      ·
        refine ⟨5793461072206474774418497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7724614762941966365891329 5793461072206474774418497)
        ·
          refine ⟨4345095804154856080813873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5793461072206474774418497 4345095804154856080813873)
          ·
            refine ⟨3258821853116142060610405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345095804154856080813873 3258821853116142060610405)
            ·
              refine ⟨611029097459276636364451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3258821853116142060610405 611029097459276636364451)
              ·
                refine ⟨916543646188914954546677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611029097459276636364451 916543646188914954546677)
                ·
                  refine ⟨85925966830210776988751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916543646188914954546677 85925966830210776988751)
                  ·
                    rfl

theorem cell22_753031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 5].length) (baseStart_753031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753031 prefixEnd_753031 := by exact prefixLift 753031
  have htrace : WordTrace (prefixWord ++ tailWord_753031) baseStart_753031 baseEnd_753031 := by
    simpa [prefixWord, tailWord_753031, baseEnd_753031] using wordTrace_append hprefix tailTrace_753031
  have hstable : (prefixWord ++ tailWord_753031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753031).length < 2 ^ (prefixWord ++ tailWord_753031).sum := by decide
  have hdescent : baseEnd_753031 < baseStart_753031 := by decide
  rcases family_descends (prefixWord ++ tailWord_753031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753091 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 2, 3]
def baseStart_753091 : Nat := 118140960795 + 753091 * 2 ^ 59
def prefixEnd_753091 : Nat := 4983230072969 + 3 ^ 40 * 753091 * 2
def baseEnd_753091 : Nat := 257798439716812174466069

theorem tailTrace_753091 : CollatzResearch.WordTrace tailWord_753091 prefixEnd_753091 257798439716812174466069 := by
  unfold tailWord_753091
  simp only [CollatzResearch.WordTrace]
  refine ⟨27467485314687399548131127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18311656876458266365420751 27467485314687399548131127)
  ·
    refine ⟨41201227972031099322196691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27467485314687399548131127 41201227972031099322196691)
    ·
      refine ⟨61801841958046648983295037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41201227972031099322196691 61801841958046648983295037)
      ·
        refine ⟨23175690734267493368735639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61801841958046648983295037 23175690734267493368735639)
        ·
          refine ⟨34763536101401240053103459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23175690734267493368735639 34763536101401240053103459)
          ·
            refine ⟨52145304152101860079655189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34763536101401240053103459 52145304152101860079655189)
            ·
              refine ⟨2444311132129774691233837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52145304152101860079655189 2444311132129774691233837)
              ·
                refine ⟨916616674548665509212689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2444311132129774691233837 916616674548665509212689)
                ·
                  refine ⟨687462505911499131909517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916616674548665509212689 687462505911499131909517)
                  ·
                    refine ⟨257798439716812174466069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687462505911499131909517 257798439716812174466069)
                    ·
                      rfl

theorem cell22_753091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3].length) (baseStart_753091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753091 prefixEnd_753091 := by exact prefixLift 753091
  have htrace : WordTrace (prefixWord ++ tailWord_753091) baseStart_753091 baseEnd_753091 := by
    simpa [prefixWord, tailWord_753091, baseEnd_753091] using wordTrace_append hprefix tailTrace_753091
  have hstable : (prefixWord ++ tailWord_753091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753091).length < 2 ^ (prefixWord ++ tailWord_753091).sum := by decide
  have hdescent : baseEnd_753091 < baseStart_753091 := by decide
  rcases family_descends (prefixWord ++ tailWord_753091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753110 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_753110 : Nat := 118140960795 + 753110 * 2 ^ 59
def prefixEnd_753110 : Nat := 4983230072969 + 3 ^ 40 * 753110 * 2
def baseEnd_753110 : Nat := 85934981268367486080337

theorem tailTrace_753110 : CollatzResearch.WordTrace tailWord_753110 prefixEnd_753110 85934981268367486080337 := by
  unfold tailWord_753110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716761143851160362067049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18312118867745710528715189 1716761143851160362067049)
  ·
    refine ⟨1287570857888370271550287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1716761143851160362067049 1287570857888370271550287)
    ·
      refine ⟨1931356286832555407325431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287570857888370271550287 1931356286832555407325431)
      ·
        refine ⟨2897034430248833110988147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931356286832555407325431 2897034430248833110988147)
        ·
          refine ⟨4345551645373249666482221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897034430248833110988147 4345551645373249666482221)
          ·
            refine ⟨1629581867014968624930833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4345551645373249666482221 1629581867014968624930833)
            ·
              refine ⟨1222186400261226468698125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1629581867014968624930833 1222186400261226468698125)
              ·
                refine ⟨458319900097959925761797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1222186400261226468698125 458319900097959925761797)
                ·
                  refine ⟨85934981268367486080337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458319900097959925761797 85934981268367486080337)
                  ·
                    rfl

theorem cell22_753110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_753110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753110 prefixEnd_753110 := by exact prefixLift 753110
  have htrace : WordTrace (prefixWord ++ tailWord_753110) baseStart_753110 baseEnd_753110 := by
    simpa [prefixWord, tailWord_753110, baseEnd_753110] using wordTrace_append hprefix tailTrace_753110
  have hstable : (prefixWord ++ tailWord_753110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753110).length < 2 ^ (prefixWord ++ tailWord_753110).sum := by decide
  have hdescent : baseEnd_753110 < baseStart_753110 := by decide
  rcases family_descends (prefixWord ++ tailWord_753110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753125 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_753125 : Nat := 118140960795 + 753125 * 2 ^ 59
def prefixEnd_753125 : Nat := 4983230072969 + 3 ^ 40 * 753125 * 2
def baseEnd_753125 : Nat := 257810078611647419115965

theorem tailTrace_753125 : CollatzResearch.WordTrace tailWord_753125 prefixEnd_753125 257810078611647419115965 := by
  unfold tailWord_753125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27468725396564223354868829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18312483597709482236579219 27468725396564223354868829)
  ·
    refine ⟨10300772023711583758075811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27468725396564223354868829 10300772023711583758075811)
    ·
      refine ⟨15451158035567375637113717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10300772023711583758075811 15451158035567375637113717)
      ·
        refine ⟨1448546065834441465979411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15451158035567375637113717 1448546065834441465979411)
        ·
          refine ⟨2172819098751662198969117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448546065834441465979411 2172819098751662198969117)
          ·
            refine ⟨814807162031873324613419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2172819098751662198969117 814807162031873324613419)
            ·
              refine ⟨1222210743047809986920129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814807162031873324613419 1222210743047809986920129)
              ·
                refine ⟨916658057285857490190097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222210743047809986920129 916658057285857490190097)
                ·
                  refine ⟨687493542964393117642573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916658057285857490190097 687493542964393117642573)
                  ·
                    refine ⟨257810078611647419115965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687493542964393117642573 257810078611647419115965)
                    ·
                      rfl

theorem cell22_753125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_753125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753125 prefixEnd_753125 := by exact prefixLift 753125
  have htrace : WordTrace (prefixWord ++ tailWord_753125) baseStart_753125 baseEnd_753125 := by
    simpa [prefixWord, tailWord_753125, baseEnd_753125] using wordTrace_append hprefix tailTrace_753125
  have hstable : (prefixWord ++ tailWord_753125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753125).length < 2 ^ (prefixWord ++ tailWord_753125).sum := by decide
  have hdescent : baseEnd_753125 < baseStart_753125 := by decide
  rcases family_descends (prefixWord ++ tailWord_753125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753136 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_753136 : Nat := 118140960795 + 753136 * 2 ^ 59
def prefixEnd_753136 : Nat := 4983230072969 + 3 ^ 40 * 753136 * 2
def baseEnd_753136 : Nat := 257813844136447057090931

theorem tailTrace_753136 : CollatzResearch.WordTrace tailWord_753136 prefixEnd_753136 257813844136447057090931 := by
  unfold tailWord_753136
  simp only [CollatzResearch.WordTrace]
  refine ⟨13734563299762186116759631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18312751066349581489012841 13734563299762186116759631)
  ·
    refine ⟨20601844949643279175139447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13734563299762186116759631 20601844949643279175139447)
    ·
      refine ⟨30902767424464918762709171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20601844949643279175139447 30902767424464918762709171)
      ·
        refine ⟨46354151136697378144063757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30902767424464918762709171 46354151136697378144063757)
        ·
          refine ⟨17382806676261516804023909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46354151136697378144063757 17382806676261516804023909)
          ·
            refine ⟨3259276251799034400754483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17382806676261516804023909 3259276251799034400754483)
            ·
              refine ⟨4888914377698551601131725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259276251799034400754483 4888914377698551601131725)
              ·
                refine ⟨1833342891636956850424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4888914377698551601131725 1833342891636956850424397)
                ·
                  refine ⟨687503584363858818909149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1833342891636956850424397 687503584363858818909149)
                  ·
                    refine ⟨257813844136447057090931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687503584363858818909149 257813844136447057090931)
                    ·
                      rfl

theorem cell22_753136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_753136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753136 prefixEnd_753136 := by exact prefixLift 753136
  have htrace : WordTrace (prefixWord ++ tailWord_753136) baseStart_753136 baseEnd_753136 := by
    simpa [prefixWord, tailWord_753136, baseEnd_753136] using wordTrace_append hprefix tailTrace_753136
  have hstable : (prefixWord ++ tailWord_753136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753136).length < 2 ^ (prefixWord ++ tailWord_753136).sum := by decide
  have hdescent : baseEnd_753136 < baseStart_753136 := by decide
  rcases family_descends (prefixWord ++ tailWord_753136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753187 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 1, 3]
def baseStart_753187 : Nat := 118140960795 + 753187 * 2 ^ 59
def prefixEnd_753187 : Nat := 4983230072969 + 3 ^ 40 * 753187 * 2
def baseEnd_753187 : Nat := 257831302478699924065775

theorem tailTrace_753187 : CollatzResearch.WordTrace tailWord_753187 prefixEnd_753187 257831302478699924065775 := by
  unfold tailWord_753187
  simp only [CollatzResearch.WordTrace]
  refine ⟨27470986722339607943625815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18313991148226405295750543 27470986722339607943625815)
  ·
    refine ⟨41206480083509411915438723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27470986722339607943625815 41206480083509411915438723)
    ·
      refine ⟨61809720125264117873158085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41206480083509411915438723 61809720125264117873158085)
      ·
        refine ⟨11589322523487022101217141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61809720125264117873158085 11589322523487022101217141)
        ·
          refine ⟨1086498986576908321989107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11589322523487022101217141 1086498986576908321989107)
          ·
            refine ⟨1629748479865362482983661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086498986576908321989107 1629748479865362482983661)
            ·
              refine ⟨611155679949510931118873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1629748479865362482983661 611155679949510931118873)
              ·
                refine ⟨458366759962133198339155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611155679949510931118873 458366759962133198339155)
                ·
                  refine ⟨687550139943199797508733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458366759962133198339155 687550139943199797508733)
                  ·
                    refine ⟨257831302478699924065775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687550139943199797508733 257831302478699924065775)
                    ·
                      rfl

theorem cell22_753187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 3].length) (baseStart_753187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753187 prefixEnd_753187 := by exact prefixLift 753187
  have htrace : WordTrace (prefixWord ++ tailWord_753187) baseStart_753187 baseEnd_753187 := by
    simpa [prefixWord, tailWord_753187, baseEnd_753187] using wordTrace_append hprefix tailTrace_753187
  have hstable : (prefixWord ++ tailWord_753187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753187).length < 2 ^ (prefixWord ++ tailWord_753187).sum := by decide
  have hdescent : baseEnd_753187 < baseStart_753187 := by decide
  rcases family_descends (prefixWord ++ tailWord_753187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753213 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_753213 : Nat := 118140960795 + 753213 * 2 ^ 59
def prefixEnd_753213 : Nat := 4983230072969 + 3 ^ 40 * 753213 * 2
def baseEnd_753213 : Nat := 257840202810044522915695

theorem tailTrace_753213 : CollatzResearch.WordTrace tailWord_753213 prefixEnd_753213 257840202810044522915695 := by
  unfold tailWord_753213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471935020245414384072293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18314623346830276256048195 27471935020245414384072293)
  ·
    refine ⟨5150987816296015197013555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27471935020245414384072293 5150987816296015197013555)
    ·
      refine ⟨7726481724444022795520333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150987816296015197013555 7726481724444022795520333)
      ·
        refine ⟨2897430646666508548320125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7726481724444022795520333 2897430646666508548320125)
        ·
          refine ⟨1086536492499940705620047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2897430646666508548320125 1086536492499940705620047)
          ·
            refine ⟨1629804738749911058430071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086536492499940705620047 1629804738749911058430071)
            ·
              refine ⟨2444707108124866587645107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629804738749911058430071 2444707108124866587645107)
              ·
                refine ⟨3667060662187299881467661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444707108124866587645107 3667060662187299881467661)
                ·
                  refine ⟨1375147748320237455550373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3667060662187299881467661 1375147748320237455550373)
                  ·
                    refine ⟨257840202810044522915695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375147748320237455550373 257840202810044522915695)
                    ·
                      rfl

theorem cell22_753213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_753213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753213 prefixEnd_753213 := by exact prefixLift 753213
  have htrace : WordTrace (prefixWord ++ tailWord_753213) baseStart_753213 baseEnd_753213 := by
    simpa [prefixWord, tailWord_753213, baseEnd_753213] using wordTrace_append hprefix tailTrace_753213
  have hstable : (prefixWord ++ tailWord_753213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753213).length < 2 ^ (prefixWord ++ tailWord_753213).sum := by decide
  have hdescent : baseEnd_753213 < baseStart_753213 := by decide
  rcases family_descends (prefixWord ++ tailWord_753213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753226 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_753226 : Nat := 118140960795 + 753226 * 2 ^ 59
def prefixEnd_753226 : Nat := 4983230072969 + 3 ^ 40 * 753226 * 2
def baseEnd_753226 : Nat := 257844652975716822340655

theorem tailTrace_753226 : CollatzResearch.WordTrace tailWord_753226 prefixEnd_753226 257844652975716822340655 := by
  unfold tailWord_753226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868102292299579401073883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18314939446132211736197021 6868102292299579401073883)
  ·
    refine ⟨10302153438449369101610825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6868102292299579401073883 10302153438449369101610825)
    ·
      refine ⟨7726615078837026826208119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10302153438449369101610825 7726615078837026826208119)
      ·
        refine ⟨11589922618255540239312179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7726615078837026826208119 11589922618255540239312179)
        ·
          refine ⟨17384883927383310358968269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11589922618255540239312179 17384883927383310358968269)
          ·
            refine ⟨6519331472768741384613101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17384883927383310358968269 6519331472768741384613101)
            ·
              refine ⟨2444749302288278019229913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6519331472768741384613101 2444749302288278019229913)
              ·
                refine ⟨1833561976716208514422435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444749302288278019229913 1833561976716208514422435)
                ·
                  refine ⟨2750342965074312771633653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833561976716208514422435 2750342965074312771633653)
                  ·
                    refine ⟨257844652975716822340655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2750342965074312771633653 257844652975716822340655)
                    ·
                      rfl

theorem cell22_753226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_753226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753226 prefixEnd_753226 := by exact prefixLift 753226
  have htrace : WordTrace (prefixWord ++ tailWord_753226) baseStart_753226 baseEnd_753226 := by
    simpa [prefixWord, tailWord_753226, baseEnd_753226] using wordTrace_append hprefix tailTrace_753226
  have hstable : (prefixWord ++ tailWord_753226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753226).length < 2 ^ (prefixWord ++ tailWord_753226).sum := by decide
  have hdescent : baseEnd_753226 < baseStart_753226 := by decide
  rcases family_descends (prefixWord ++ tailWord_753226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753238 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_753238 : Nat := 118140960795 + 753238 * 2 ^ 59
def prefixEnd_753238 : Nat := 4983230072969 + 3 ^ 40 * 753238 * 2
def baseEnd_753238 : Nat := 257848760820952791040619

theorem tailTrace_753238 : CollatzResearch.WordTrace tailWord_753238 prefixEnd_753238 257848760820952791040619 := by
  unfold tailWord_753238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717052927822177728358273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18315231230103229102488245 1717052927822177728358273)
  ·
    refine ⟨1287789695866633296268705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1717052927822177728358273 1287789695866633296268705)
    ·
      refine ⟨965842271899974972201529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1287789695866633296268705 965842271899974972201529)
      ·
        refine ⟨724381703924981229151147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965842271899974972201529 724381703924981229151147)
        ·
          refine ⟨1086572555887471843726721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724381703924981229151147 1086572555887471843726721)
          ·
            refine ⟨814929416915603882795041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086572555887471843726721 814929416915603882795041)
            ·
              refine ⟨611197062686702912096281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814929416915603882795041 611197062686702912096281)
              ·
                refine ⟨458397797015027184072211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611197062686702912096281 458397797015027184072211)
                ·
                  refine ⟨687596695522540776108317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458397797015027184072211 687596695522540776108317)
                  ·
                    refine ⟨257848760820952791040619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687596695522540776108317 257848760820952791040619)
                    ·
                      rfl

theorem cell22_753238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_753238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753238 prefixEnd_753238 := by exact prefixLift 753238
  have htrace : WordTrace (prefixWord ++ tailWord_753238) baseStart_753238 baseEnd_753238 := by
    simpa [prefixWord, tailWord_753238, baseEnd_753238] using wordTrace_append hprefix tailTrace_753238
  have hstable : (prefixWord ++ tailWord_753238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753238).length < 2 ^ (prefixWord ++ tailWord_753238).sum := by decide
  have hdescent : baseEnd_753238 < baseStart_753238 := by decide
  rcases family_descends (prefixWord ++ tailWord_753238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753239 : List Nat := [1, 1, 3, 2, 2, 13]
def baseStart_753239 : Nat := 118140960795 + 753239 * 2 ^ 59
def prefixEnd_753239 : Nat := 4983230072969 + 3 ^ 40 * 753239 * 2
def baseEnd_753239 : Nat := 3183322261004803972415

theorem tailTrace_753239 : CollatzResearch.WordTrace tailWord_753239 prefixEnd_753239 3183322261004803972415 := by
  unfold tailWord_753239
  simp only [CollatzResearch.WordTrace]
  refine ⟨27472883318151220824518771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18315255545434147216345847 27472883318151220824518771)
  ·
    refine ⟨41209324977226831236778157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27472883318151220824518771 41209324977226831236778157)
    ·
      refine ⟨15453496866460061713791809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41209324977226831236778157 15453496866460061713791809)
      ·
        refine ⟨11590122649845046285343857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15453496866460061713791809 11590122649845046285343857)
        ·
          refine ⟨8692591987383784714007893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11590122649845046285343857 8692591987383784714007893)
          ·
            refine ⟨3183322261004803972415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 8692591987383784714007893 3183322261004803972415)
            ·
              rfl

theorem cell22_753239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 13].length) (baseStart_753239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753239 prefixEnd_753239 := by exact prefixLift 753239
  have htrace : WordTrace (prefixWord ++ tailWord_753239) baseStart_753239 baseEnd_753239 := by
    simpa [prefixWord, tailWord_753239, baseEnd_753239] using wordTrace_append hprefix tailTrace_753239
  have hstable : (prefixWord ++ tailWord_753239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753239).length < 2 ^ (prefixWord ++ tailWord_753239).sum := by decide
  have hdescent : baseEnd_753239 < baseStart_753239 := by decide
  rcases family_descends (prefixWord ++ tailWord_753239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753376 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_753376 : Nat := 118140960795 + 753376 * 2 ^ 59
def prefixEnd_753376 : Nat := 4983230072969 + 3 ^ 40 * 753376 * 2
def baseEnd_753376 : Nat := 257896001041166431090195

theorem tailTrace_753376 : CollatzResearch.WordTrace tailWord_753376 prefixEnd_753376 257896001041166431090195 := by
  unfold tailWord_753376
  simp only [CollatzResearch.WordTrace]
  refine ⟨13738940059327446611127991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18318586745769928814837321 13738940059327446611127991)
  ·
    refine ⟨20608410088991169916691987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13738940059327446611127991 20608410088991169916691987)
    ·
      refine ⟨30912615133486754875037981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20608410088991169916691987 30912615133486754875037981)
      ·
        refine ⟨11592230675057533078139243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30912615133486754875037981 11592230675057533078139243)
        ·
          refine ⟨17388346012586299617208865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11592230675057533078139243 17388346012586299617208865)
          ·
            refine ⟨13041259509439724712906649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17388346012586299617208865 13041259509439724712906649)
            ·
              refine ⟨9780944632079793534679987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13041259509439724712906649 9780944632079793534679987)
              ·
                refine ⟨14671416948119690302019981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9780944632079793534679987 14671416948119690302019981)
                ·
                  refine ⟨5501781355544883863257493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14671416948119690302019981 5501781355544883863257493)
                  ·
                    refine ⟨257896001041166431090195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5501781355544883863257493 257896001041166431090195)
                    ·
                      rfl

theorem cell22_753376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_753376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753376 prefixEnd_753376 := by exact prefixLift 753376
  have htrace : WordTrace (prefixWord ++ tailWord_753376) baseStart_753376 baseEnd_753376 := by
    simpa [prefixWord, tailWord_753376, baseEnd_753376] using wordTrace_append hprefix tailTrace_753376
  have hstable : (prefixWord ++ tailWord_753376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753376).length < 2 ^ (prefixWord ++ tailWord_753376).sum := by decide
  have hdescent : baseEnd_753376 < baseStart_753376 := by decide
  rcases family_descends (prefixWord ++ tailWord_753376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753391 : List Nat := [1, 1, 2, 1, 5, 1, 1, 10]
def baseStart_753391 : Nat := 118140960795 + 753391 * 2 ^ 59
def prefixEnd_753391 : Nat := 4983230072969 + 3 ^ 40 * 753391 * 2
def baseEnd_753391 : Nat := 28655681760856821329461

theorem tailTrace_753391 : CollatzResearch.WordTrace tailWord_753391 prefixEnd_753391 28655681760856821329461 := by
  unfold tailWord_753391
  simp only [CollatzResearch.WordTrace]
  refine ⟨27478427213600550784052027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18318951475733700522701351 27478427213600550784052027)
  ·
    refine ⟨41217640820400826176078041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27478427213600550784052027 41217640820400826176078041)
    ·
      refine ⟨30913230615300619632058531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41217640820400826176078041 30913230615300619632058531)
      ·
        refine ⟨46369845922950929448087797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30913230615300619632058531 46369845922950929448087797)
        ·
          refine ⟨4347173055276649635758231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46369845922950929448087797 4347173055276649635758231)
          ·
            refine ⟨6520759582914974453637347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347173055276649635758231 6520759582914974453637347)
            ·
              refine ⟨9781139374372461680456021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520759582914974453637347 9781139374372461680456021)
              ·
                refine ⟨28655681760856821329461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9781139374372461680456021 28655681760856821329461)
                ·
                  rfl

theorem cell22_753391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 10].length) (baseStart_753391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753391 prefixEnd_753391 := by exact prefixLift 753391
  have htrace : WordTrace (prefixWord ++ tailWord_753391) baseStart_753391 baseEnd_753391 := by
    simpa [prefixWord, tailWord_753391, baseEnd_753391] using wordTrace_append hprefix tailTrace_753391
  have hstable : (prefixWord ++ tailWord_753391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753391).length < 2 ^ (prefixWord ++ tailWord_753391).sum := by decide
  have hdescent : baseEnd_753391 < baseStart_753391 := by decide
  rcases family_descends (prefixWord ++ tailWord_753391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753393 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_753393 : Nat := 118140960795 + 753393 * 2 ^ 59
def prefixEnd_753393 : Nat := 4983230072969 + 3 ^ 40 * 753393 * 2
def baseEnd_753393 : Nat := 257901820488584053415143

theorem tailTrace_753393 : CollatzResearch.WordTrace tailWord_753393 prefixEnd_753393 257901820488584053415143 := by
  unfold tailWord_753393
  simp only [CollatzResearch.WordTrace]
  refine ⟨27478500159593305125624833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18319000106395536750416555 27478500159593305125624833)
  ·
    refine ⟨20608875119694978844218625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27478500159593305125624833 20608875119694978844218625)
    ·
      refine ⟨15456656339771234133163969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20608875119694978844218625 15456656339771234133163969)
      ·
        refine ⟨11592492254828425599872977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15456656339771234133163969 11592492254828425599872977)
        ·
          refine ⟨8694369191121319199904733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11592492254828425599872977 8694369191121319199904733)
          ·
            refine ⟨3260388446670494699964275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8694369191121319199904733 3260388446670494699964275)
            ·
              refine ⟨4890582670005742049946413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260388446670494699964275 4890582670005742049946413)
              ·
                refine ⟨1833968501252153268729905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4890582670005742049946413 1833968501252153268729905)
                ·
                  refine ⟨1375476375939114951547429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833968501252153268729905 1375476375939114951547429)
                  ·
                    refine ⟨257901820488584053415143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375476375939114951547429 257901820488584053415143)
                    ·
                      rfl

theorem cell22_753393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_753393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753393 prefixEnd_753393 := by exact prefixLift 753393
  have htrace : WordTrace (prefixWord ++ tailWord_753393) baseStart_753393 baseEnd_753393 := by
    simpa [prefixWord, tailWord_753393, baseEnd_753393] using wordTrace_append hprefix tailTrace_753393
  have hstable : (prefixWord ++ tailWord_753393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753393).length < 2 ^ (prefixWord ++ tailWord_753393).sum := by decide
  have hdescent : baseEnd_753393 < baseStart_753393 := by decide
  rcases family_descends (prefixWord ++ tailWord_753393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753410 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_753410 : Nat := 118140960795 + 753410 * 2 ^ 59
def prefixEnd_753410 : Nat := 4983230072969 + 3 ^ 40 * 753410 * 2
def baseEnd_753410 : Nat := 257907639936001675740091

theorem tailTrace_753410 : CollatzResearch.WordTrace tailWord_753410 prefixEnd_753410 257907639936001675740091 := by
  unfold tailWord_753410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869780050132929257248421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18319413467021144685995789 6869780050132929257248421)
  ·
    refine ⟨1288083759399924235734079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6869780050132929257248421 1288083759399924235734079)
    ·
      refine ⟨1932125639099886353601119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288083759399924235734079 1932125639099886353601119)
      ·
        refine ⟨2898188458649829530401679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932125639099886353601119 2898188458649829530401679)
        ·
          refine ⟨4347282687974744295602519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898188458649829530401679 4347282687974744295602519)
          ·
            refine ⟨6520924031962116443403779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347282687974744295602519 6520924031962116443403779)
            ·
              refine ⟨9781386047943174665105669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520924031962116443403779 9781386047943174665105669)
              ·
                refine ⟨1834009883989345249707313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9781386047943174665105669 1834009883989345249707313)
                ·
                  refine ⟨1375507412992008937280485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834009883989345249707313 1375507412992008937280485)
                  ·
                    refine ⟨257907639936001675740091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375507412992008937280485 257907639936001675740091)
                    ·
                      rfl

theorem cell22_753410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_753410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753410 prefixEnd_753410 := by exact prefixLift 753410
  have htrace : WordTrace (prefixWord ++ tailWord_753410) baseStart_753410 baseEnd_753410 := by
    simpa [prefixWord, tailWord_753410, baseEnd_753410] using wordTrace_append hprefix tailTrace_753410
  have hstable : (prefixWord ++ tailWord_753410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753410).length < 2 ^ (prefixWord ++ tailWord_753410).sum := by decide
  have hdescent : baseEnd_753410 < baseStart_753410 := by decide
  rcases family_descends (prefixWord ++ tailWord_753410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753412 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_753412 : Nat := 118140960795 + 753412 * 2 ^ 59
def prefixEnd_753412 : Nat := 4983230072969 + 3 ^ 40 * 753412 * 2
def baseEnd_753412 : Nat := 257908324576874337190085

theorem tailTrace_753412 : CollatzResearch.WordTrace tailWord_753412 prefixEnd_753412 257908324576874337190085 := by
  unfold tailWord_753412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13739596573262235685283245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18319462097682980913710993 13739596573262235685283245)
  ·
    refine ⟨5152348714973338381981217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13739596573262235685283245 5152348714973338381981217)
    ·
      refine ⟨3864261536230003786485913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5152348714973338381981217 3864261536230003786485913)
      ·
        refine ⟨2898196152172502839864435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864261536230003786485913 2898196152172502839864435)
        ·
          refine ⟨4347294228258754259796653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898196152172502839864435 4347294228258754259796653)
          ·
            refine ⟨1630235335597032847423745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4347294228258754259796653 1630235335597032847423745)
            ·
              refine ⟨1222676501697774635567809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630235335597032847423745 1222676501697774635567809)
              ·
                refine ⟨917007376273330976675857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222676501697774635567809 917007376273330976675857)
                ·
                  refine ⟨687755532204998232506893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 917007376273330976675857 687755532204998232506893)
                  ·
                    refine ⟨257908324576874337190085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687755532204998232506893 257908324576874337190085)
                    ·
                      rfl

theorem cell22_753412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_753412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753412 prefixEnd_753412 := by exact prefixLift 753412
  have htrace : WordTrace (prefixWord ++ tailWord_753412) baseStart_753412 baseEnd_753412 := by
    simpa [prefixWord, tailWord_753412, baseEnd_753412] using wordTrace_append hprefix tailTrace_753412
  have hstable : (prefixWord ++ tailWord_753412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753412).length < 2 ^ (prefixWord ++ tailWord_753412).sum := by decide
  have hdescent : baseEnd_753412 < baseStart_753412 := by decide
  rcases family_descends (prefixWord ++ tailWord_753412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753440 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_753440 : Nat := 118140960795 + 753440 * 2 ^ 59
def prefixEnd_753440 : Nat := 4983230072969 + 3 ^ 40 * 753440 * 2
def baseEnd_753440 : Nat := 257917909549091597489999

theorem tailTrace_753440 : CollatzResearch.WordTrace tailWord_753440 prefixEnd_753440 257917909549091597489999 := by
  unfold tailWord_753440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740107195211516076292887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18320142926948688101723849 13740107195211516076292887)
  ·
    refine ⟨20610160792817274114439331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13740107195211516076292887 20610160792817274114439331)
    ·
      refine ⟨30915241189225911171658997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610160792817274114439331 30915241189225911171658997)
      ·
        refine ⟨2898303861489929172343031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30915241189225911171658997 2898303861489929172343031)
        ·
          refine ⟨4347455792234893758514547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898303861489929172343031 4347455792234893758514547)
          ·
            refine ⟨6521183688352340637771821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347455792234893758514547 6521183688352340637771821)
            ·
              refine ⟨2445443883132127739164433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6521183688352340637771821 2445443883132127739164433)
              ·
                refine ⟨1834082912349095804373325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445443883132127739164433 1834082912349095804373325)
                ·
                  refine ⟨687781092130910926639997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1834082912349095804373325 687781092130910926639997)
                  ·
                    refine ⟨257917909549091597489999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687781092130910926639997 257917909549091597489999)
                    ·
                      rfl

theorem cell22_753440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_753440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753440 prefixEnd_753440 := by exact prefixLift 753440
  have htrace : WordTrace (prefixWord ++ tailWord_753440) baseStart_753440 baseEnd_753440 := by
    simpa [prefixWord, tailWord_753440, baseEnd_753440] using wordTrace_append hprefix tailTrace_753440
  have hstable : (prefixWord ++ tailWord_753440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753440).length < 2 ^ (prefixWord ++ tailWord_753440).sum := by decide
  have hdescent : baseEnd_753440 < baseStart_753440 := by decide
  rcases family_descends (prefixWord ++ tailWord_753440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753457 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 1, 3]
def baseStart_753457 : Nat := 118140960795 + 753457 * 2 ^ 59
def prefixEnd_753457 : Nat := 4983230072969 + 3 ^ 40 * 753457 * 2
def baseEnd_753457 : Nat := 257923728996509219814947

theorem tailTrace_753457 : CollatzResearch.WordTrace tailWord_753457 prefixEnd_753457 257923728996509219814947 := by
  unfold tailWord_753457
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480834431361444055954625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18320556287574296037303083 27480834431361444055954625)
  ·
    refine ⟨20610625823521083041965969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27480834431361444055954625 20610625823521083041965969)
    ·
      refine ⟨15457969367640812281474477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20610625823521083041965969 15457969367640812281474477)
      ·
        refine ⟨5796738512865304605552929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15457969367640812281474477 5796738512865304605552929)
        ·
          refine ⟨4347553884648978454164697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5796738512865304605552929 4347553884648978454164697)
          ·
            refine ⟨3260665413486733840623523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4347553884648978454164697 3260665413486733840623523)
            ·
              refine ⟨4890998120230100760935285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260665413486733840623523 4890998120230100760935285)
              ·
                refine ⟨458531073771571946337683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4890998120230100760935285 458531073771571946337683)
                ·
                  refine ⟨687796610657357919506525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458531073771571946337683 687796610657357919506525)
                  ·
                    refine ⟨257923728996509219814947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687796610657357919506525 257923728996509219814947)
                    ·
                      rfl

theorem cell22_753457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_753457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753457 prefixEnd_753457 := by exact prefixLift 753457
  have htrace : WordTrace (prefixWord ++ tailWord_753457) baseStart_753457 baseEnd_753457 := by
    simpa [prefixWord, tailWord_753457, baseEnd_753457] using wordTrace_append hprefix tailTrace_753457
  have hstable : (prefixWord ++ tailWord_753457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753457).length < 2 ^ (prefixWord ++ tailWord_753457).sum := by decide
  have hdescent : baseEnd_753457 < baseStart_753457 := by decide
  rcases family_descends (prefixWord ++ tailWord_753457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753468 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_753468 : Nat := 118140960795 + 753468 * 2 ^ 59
def prefixEnd_753468 : Nat := 4983230072969 + 3 ^ 40 * 753468 * 2
def baseEnd_753468 : Nat := 257927494521308857789913

theorem tailTrace_753468 : CollatzResearch.WordTrace tailWord_753468 prefixEnd_753468 257927494521308857789913 := by
  unfold tailWord_753468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740617817160796467302529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18320823756214395289736705 13740617817160796467302529)
  ·
    refine ⟨10305463362870597350476897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13740617817160796467302529 10305463362870597350476897)
    ·
      refine ⟨7729097522152948012857673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10305463362870597350476897 7729097522152948012857673)
      ·
        refine ⟨5796823141614711009643255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7729097522152948012857673 5796823141614711009643255)
        ·
          refine ⟨8695234712422066514464883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796823141614711009643255 8695234712422066514464883)
          ·
            refine ⟨13042852068633099771697325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695234712422066514464883 13042852068633099771697325)
            ·
              refine ⟨4891069525737412414386497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13042852068633099771697325 4891069525737412414386497)
              ·
                refine ⟨3668302144303059310789873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891069525737412414386497 3668302144303059310789873)
                ·
                  refine ⟨2751226608227294483092405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668302144303059310789873 2751226608227294483092405)
                  ·
                    refine ⟨257927494521308857789913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2751226608227294483092405 257927494521308857789913)
                    ·
                      rfl

theorem cell22_753468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_753468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753468 prefixEnd_753468 := by exact prefixLift 753468
  have htrace : WordTrace (prefixWord ++ tailWord_753468) baseStart_753468 baseEnd_753468 := by
    simpa [prefixWord, tailWord_753468, baseEnd_753468] using wordTrace_append hprefix tailTrace_753468
  have hstable : (prefixWord ++ tailWord_753468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753468).length < 2 ^ (prefixWord ++ tailWord_753468).sum := by decide
  have hdescent : baseEnd_753468 < baseStart_753468 := by decide
  rcases family_descends (prefixWord ++ tailWord_753468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753470 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_753470 : Nat := 118140960795 + 753470 * 2 ^ 59
def prefixEnd_753470 : Nat := 4983230072969 + 3 ^ 40 * 753470 * 2
def baseEnd_753470 : Nat := 85976059720727173079969

theorem tailTrace_753470 : CollatzResearch.WordTrace tailWord_753470 prefixEnd_753470 85976059720727173079969 := by
  unfold tailWord_753470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435163572539293409522233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18320872386876231517451909 3435163572539293409522233)
  ·
    refine ⟨2576372679404470057141675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3435163572539293409522233 2576372679404470057141675)
    ·
      refine ⟨3864559019106705085712513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576372679404470057141675 3864559019106705085712513)
      ·
        refine ⟨2898419264330028814284385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864559019106705085712513 2898419264330028814284385)
        ·
          refine ⟨2173814448247521610713289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898419264330028814284385 2173814448247521610713289)
          ·
            refine ⟨1630360836185641208034967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173814448247521610713289 1630360836185641208034967)
            ·
              refine ⟨2445541254278461812052451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630360836185641208034967 2445541254278461812052451)
              ·
                refine ⟨3668311881417692718078677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445541254278461812052451 3668311881417692718078677)
                ·
                  refine ⟨85976059720727173079969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3668311881417692718078677 85976059720727173079969)
                  ·
                    rfl

theorem cell22_753470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_753470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753470 prefixEnd_753470 := by exact prefixLift 753470
  have htrace : WordTrace (prefixWord ++ tailWord_753470) baseStart_753470 baseEnd_753470 := by
    simpa [prefixWord, tailWord_753470, baseEnd_753470] using wordTrace_append hprefix tailTrace_753470
  have hstable : (prefixWord ++ tailWord_753470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753470).length < 2 ^ (prefixWord ++ tailWord_753470).sum := by decide
  have hdescent : baseEnd_753470 < baseStart_753470 := by decide
  rcases family_descends (prefixWord ++ tailWord_753470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
