import V185TrunkScan23Chunk0317

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1880225 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1880225 : Nat := 118140960795 + 1880225 * 2 ^ 59
def prefixEnd_1880225 : Nat := 4983230072969 + 3 ^ 40 * 1880225 * 2
def baseEnd_1880225 : Nat := 965459163600011344740509

theorem tailTrace_1880225 : CollatzResearch.WordTrace tailWord_1880225 prefixEnd_1880225 965459163600011344740509 := by
  unfold tailWord_1880225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68577439613273416709690129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45718293075515611139793419 68577439613273416709690129)
  ·
    refine ⟨51433079709955062532267597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68577439613273416709690129 51433079709955062532267597)
    ·
      refine ⟨19287404891233148449600349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51433079709955062532267597 19287404891233148449600349)
      ·
        refine ⟨7232776834212430668600131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19287404891233148449600349 7232776834212430668600131)
        ·
          refine ⟨10849165251318646002900197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232776834212430668600131 10849165251318646002900197)
          ·
            refine ⟨2034218484622246125543787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10849165251318646002900197 2034218484622246125543787)
            ·
              refine ⟨3051327726933369188315681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034218484622246125543787 3051327726933369188315681)
              ·
                refine ⟨2288495795200026891236761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051327726933369188315681 2288495795200026891236761)
                ·
                  refine ⟨1716371846400020168427571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288495795200026891236761 1716371846400020168427571)
                  ·
                    refine ⟨2574557769600030252641357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1716371846400020168427571 2574557769600030252641357)
                    ·
                      refine ⟨965459163600011344740509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2574557769600030252641357 965459163600011344740509)
                      ·
                        rfl

theorem cell23_1880225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1880225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880225 prefixEnd_1880225 := by exact prefixLift 1880225
  have htrace : WordTrace (prefixWord ++ tailWord_1880225) baseStart_1880225 baseEnd_1880225 := by
    simpa [prefixWord, tailWord_1880225, baseEnd_1880225] using wordTrace_append hprefix tailTrace_1880225
  have hstable : (prefixWord ++ tailWord_1880225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880225).length < 2 ^ (prefixWord ++ tailWord_1880225).sum := by decide
  have hdescent : baseEnd_1880225 < baseStart_1880225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880268 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1880268 : Nat := 118140960795 + 1880268 * 2 ^ 59
def prefixEnd_1880268 : Nat := 4983230072969 + 3 ^ 40 * 1880268 * 2
def baseEnd_1880268 : Nat := 965481243268154676502811

theorem tailTrace_1880268 : CollatzResearch.WordTrace tailWord_1880268 prefixEnd_1880268 965481243268154676502811 := by
  unfold tailWord_1880268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34289503976058817526752729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45719338634745090035670305 34289503976058817526752729)
  ·
    refine ⟨25717127982044113145064547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34289503976058817526752729 25717127982044113145064547)
    ·
      refine ⟨38575691973066169717596821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25717127982044113145064547 38575691973066169717596821)
      ·
        refine ⟨1808235561237476705512351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38575691973066169717596821 1808235561237476705512351)
        ·
          refine ⟨2712353341856215058268527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808235561237476705512351 2712353341856215058268527)
          ·
            refine ⟨4068530012784322587402791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712353341856215058268527 4068530012784322587402791)
            ·
              refine ⟨6102795019176483881104187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068530012784322587402791 6102795019176483881104187)
              ·
                refine ⟨9154192528764725821656281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102795019176483881104187 9154192528764725821656281)
                ·
                  refine ⟨6865644396573544366242211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154192528764725821656281 6865644396573544366242211)
                  ·
                    refine ⟨10298466594860316549363317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6865644396573544366242211 10298466594860316549363317)
                    ·
                      refine ⟨965481243268154676502811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10298466594860316549363317 965481243268154676502811)
                      ·
                        rfl

theorem cell23_1880268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1880268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880268 prefixEnd_1880268 := by exact prefixLift 1880268
  have htrace : WordTrace (prefixWord ++ tailWord_1880268) baseStart_1880268 baseEnd_1880268 := by
    simpa [prefixWord, tailWord_1880268, baseEnd_1880268] using wordTrace_append hprefix tailTrace_1880268
  have hstable : (prefixWord ++ tailWord_1880268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880268).length < 2 ^ (prefixWord ++ tailWord_1880268).sum := by decide
  have hdescent : baseEnd_1880268 < baseStart_1880268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880288 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 5]
def baseStart_1880288 : Nat := 118140960795 + 1880288 * 2 ^ 59
def prefixEnd_1880288 : Nat := 4983230072969 + 3 ^ 40 * 1880288 * 2
def baseEnd_1880288 : Nat := 107276834764582733139191

theorem tailTrace_1880288 : CollatzResearch.WordTrace tailWord_1880288 prefixEnd_1880288 107276834764582733139191 := by
  unfold tailWord_1880288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34289868706022589234616759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45719824941363452312822345 34289868706022589234616759)
  ·
    refine ⟨51434803059033883851925139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34289868706022589234616759 51434803059033883851925139)
    ·
      refine ⟨77152204588550825777887709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51434803059033883851925139 77152204588550825777887709)
      ·
        refine ⟨28932076720706559666707891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77152204588550825777887709 28932076720706559666707891)
        ·
          refine ⟨43398115081059839500061837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28932076720706559666707891 43398115081059839500061837)
          ·
            refine ⟨16274293155397439812523189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43398115081059839500061837 16274293155397439812523189)
            ·
              refine ⟨1525714983318509982424049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16274293155397439812523189 1525714983318509982424049)
              ·
                refine ⟨1144286237488882486818037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525714983318509982424049 1144286237488882486818037)
                ·
                  refine ⟨107276834764582733139191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1144286237488882486818037 107276834764582733139191)
                  ·
                    rfl

theorem cell23_1880288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 5].length) (baseStart_1880288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880288 prefixEnd_1880288 := by exact prefixLift 1880288
  have htrace : WordTrace (prefixWord ++ tailWord_1880288) baseStart_1880288 baseEnd_1880288 := by
    simpa [prefixWord, tailWord_1880288, baseEnd_1880288] using wordTrace_append hprefix tailTrace_1880288
  have hstable : (prefixWord ++ tailWord_1880288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880288).length < 2 ^ (prefixWord ++ tailWord_1880288).sum := by decide
  have hdescent : baseEnd_1880288 < baseStart_1880288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880304 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1880304 : Nat := 118140960795 + 1880304 * 2 ^ 59
def prefixEnd_1880304 : Nat := 4983230072969 + 3 ^ 40 * 1880304 * 2
def baseEnd_1880304 : Nat := 965499728571716535652645

theorem tailTrace_1880304 : CollatzResearch.WordTrace tailWord_1880304 prefixEnd_1880304 965499728571716535652645 := by
  unfold tailWord_1880304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34290160489993606600907983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45720213986658142134543977 34290160489993606600907983)
  ·
    refine ⟨51435240734990409901361975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34290160489993606600907983 51435240734990409901361975)
    ·
      refine ⟨77152861102485614852042963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51435240734990409901361975 77152861102485614852042963)
      ·
        refine ⟨115729291653728422278064445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77152861102485614852042963 115729291653728422278064445)
        ·
          refine ⟨43398484370148158354274167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115729291653728422278064445 43398484370148158354274167)
          ·
            refine ⟨65097726555222237531411251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43398484370148158354274167 65097726555222237531411251)
            ·
              refine ⟨97646589832833356297116877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65097726555222237531411251 97646589832833356297116877)
              ·
                refine ⟨36617471187312508611418829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97646589832833356297116877 36617471187312508611418829)
                ·
                  refine ⟨13731551695242190729282061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36617471187312508611418829 13731551695242190729282061)
                  ·
                    refine ⟨5149331885715821523480773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13731551695242190729282061 5149331885715821523480773)
                    ·
                      refine ⟨965499728571716535652645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5149331885715821523480773 965499728571716535652645)
                      ·
                        rfl

theorem cell23_1880304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1880304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880304 prefixEnd_1880304 := by exact prefixLift 1880304
  have htrace : WordTrace (prefixWord ++ tailWord_1880304) baseStart_1880304 baseEnd_1880304 := by
    simpa [prefixWord, tailWord_1880304, baseEnd_1880304] using wordTrace_append hprefix tailTrace_1880304
  have hstable : (prefixWord ++ tailWord_1880304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880304).length < 2 ^ (prefixWord ++ tailWord_1880304).sum := by decide
  have hdescent : baseEnd_1880304 < baseStart_1880304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880318 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1880318 : Nat := 118140960795 + 1880318 * 2 ^ 59
def prefixEnd_1880318 : Nat := 4983230072969 + 3 ^ 40 * 1880318 * 2
def baseEnd_1880318 : Nat := 321835639100293160292527

theorem tailTrace_1880318 : CollatzResearch.WordTrace tailWord_1880318 prefixEnd_1880318 321835639100293160292527 := by
  unfold tailWord_1880318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572603950242061699103201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45720554401290995728550405 8572603950242061699103201)
  ·
    refine ⟨6429452962681546274327401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8572603950242061699103201 6429452962681546274327401)
    ·
      refine ⟨4822089722011159705745551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6429452962681546274327401 4822089722011159705745551)
      ·
        refine ⟨7233134583016739558618327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822089722011159705745551 7233134583016739558618327)
        ·
          refine ⟨10849701874525109337927491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233134583016739558618327 10849701874525109337927491)
          ·
            refine ⟨16274552811787664006891237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849701874525109337927491 16274552811787664006891237)
            ·
              refine ⟨3051478652210187001292107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16274552811787664006891237 3051478652210187001292107)
              ·
                refine ⟨4577217978315280501938161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051478652210187001292107 4577217978315280501938161)
                ·
                  refine ⟨3432913483736460376453621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4577217978315280501938161 3432913483736460376453621)
                  ·
                    refine ⟨321835639100293160292527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3432913483736460376453621 321835639100293160292527)
                    ·
                      rfl

theorem cell23_1880318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1880318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880318 prefixEnd_1880318 := by exact prefixLift 1880318
  have htrace : WordTrace (prefixWord ++ tailWord_1880318) baseStart_1880318 baseEnd_1880318 := by
    simpa [prefixWord, tailWord_1880318, baseEnd_1880318] using wordTrace_append hprefix tailTrace_1880318
  have hstable : (prefixWord ++ tailWord_1880318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880318).length < 2 ^ (prefixWord ++ tailWord_1880318).sum := by decide
  have hdescent : baseEnd_1880318 < baseStart_1880318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880382 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1880382 : Nat := 118140960795 + 1880382 * 2 ^ 59
def prefixEnd_1880382 : Nat := 4983230072969 + 3 ^ 40 * 1880382 * 2
def baseEnd_1880382 : Nat := 321846593354255743492429

theorem tailTrace_1880382 : CollatzResearch.WordTrace tailWord_1880382 prefixEnd_1880382 321846593354255743492429 := by
  unfold tailWord_1880382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572895734213079065394425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45722110582469755015436933 8572895734213079065394425)
  ·
    refine ⟨6429671800659809299045819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8572895734213079065394425 6429671800659809299045819)
    ·
      refine ⟨9644507700989713948568729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429671800659809299045819 9644507700989713948568729)
      ·
        refine ⟨7233380775742285461426547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9644507700989713948568729 7233380775742285461426547)
        ·
          refine ⟨10850071163613428192139821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233380775742285461426547 10850071163613428192139821)
          ·
            refine ⟨4068776686355035572052433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10850071163613428192139821 4068776686355035572052433)
            ·
              refine ⟨3051582514766276679039325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068776686355035572052433 3051582514766276679039325)
              ·
                refine ⟨1144343443037353754639747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051582514766276679039325 1144343443037353754639747)
                ·
                  refine ⟨1716515164556030631959621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144343443037353754639747 1716515164556030631959621)
                  ·
                    refine ⟨321846593354255743492429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716515164556030631959621 321846593354255743492429)
                    ·
                      rfl

theorem cell23_1880382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1880382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880382 prefixEnd_1880382 := by exact prefixLift 1880382
  have htrace : WordTrace (prefixWord ++ tailWord_1880382) baseStart_1880382 baseEnd_1880382 := by
    simpa [prefixWord, tailWord_1880382, baseEnd_1880382] using wordTrace_append hprefix tailTrace_1880382
  have hstable : (prefixWord ++ tailWord_1880382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880382).length < 2 ^ (prefixWord ++ tailWord_1880382).sum := by decide
  have hdescent : baseEnd_1880382 < baseStart_1880382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880412 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 6]
def baseStart_1880412 : Nat := 118140960795 + 1880412 * 2 ^ 59
def prefixEnd_1880412 : Nat := 4983230072969 + 3 ^ 40 * 1880412 * 2
def baseEnd_1880412 : Nat := 107283909386933568122461

theorem tailTrace_1880412 : CollatzResearch.WordTrace tailWord_1880412 prefixEnd_1880412 107283909386933568122461 := by
  unfold tailWord_1880412
  simp only [CollatzResearch.WordTrace]
  refine ⟨34292130031797973823373745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45722840042397298431164993 34292130031797973823373745)
  ·
    refine ⟨25719097523848480367530309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34292130031797973823373745 25719097523848480367530309)
    ·
      refine ⟨4822330785721590068911933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25719097523848480367530309 4822330785721590068911933)
      ·
        refine ⟨1808374044645596275841975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4822330785721590068911933 1808374044645596275841975)
        ·
          refine ⟨2712561066968394413762963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808374044645596275841975 2712561066968394413762963)
          ·
            refine ⟨4068841600452591620644445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712561066968394413762963 4068841600452591620644445)
            ·
              refine ⟨1525815600169721857741667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4068841600452591620644445 1525815600169721857741667)
              ·
                refine ⟨2288723400254582786612501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525815600169721857741667 2288723400254582786612501)
                ·
                  refine ⟨107283909386933568122461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2288723400254582786612501 107283909386933568122461)
                  ·
                    rfl

theorem cell23_1880412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_1880412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880412 prefixEnd_1880412 := by exact prefixLift 1880412
  have htrace : WordTrace (prefixWord ++ tailWord_1880412) baseStart_1880412 baseEnd_1880412 := by
    simpa [prefixWord, tailWord_1880412, baseEnd_1880412] using wordTrace_append hprefix tailTrace_1880412
  have hstable : (prefixWord ++ tailWord_1880412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880412).length < 2 ^ (prefixWord ++ tailWord_1880412).sum := by decide
  have hdescent : baseEnd_1880412 < baseStart_1880412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880441 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1880441 : Nat := 118140960795 + 1880441 * 2 ^ 59
def prefixEnd_1880441 : Nat := 4983230072969 + 3 ^ 40 * 1880441 * 2
def baseEnd_1880441 : Nat := 965570075421382499639515

theorem tailTrace_1880441 : CollatzResearch.WordTrace tailWord_1880441 prefixEnd_1880441 965570075421382499639515 := by
  unfold tailWord_1880441
  simp only [CollatzResearch.WordTrace]
  refine ⟨68585317780490885599553177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45723545186993923733035451 68585317780490885599553177)
  ·
    refine ⟨51438988335368164199664883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68585317780490885599553177 51438988335368164199664883)
    ·
      refine ⟨77158482503052246299497325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51438988335368164199664883 77158482503052246299497325)
      ·
        refine ⟨28934430938644592362311497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77158482503052246299497325 28934430938644592362311497)
        ·
          refine ⟨21700823203983444271733623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28934430938644592362311497 21700823203983444271733623)
          ·
            refine ⟨32551234805975166407600435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21700823203983444271733623 32551234805975166407600435)
            ·
              refine ⟨48826852208962749611400653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32551234805975166407600435 48826852208962749611400653)
              ·
                refine ⟨18310069578361031104275245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48826852208962749611400653 18310069578361031104275245)
                ·
                  refine ⟨6866276091885386664103217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18310069578361031104275245 6866276091885386664103217)
                  ·
                    refine ⟨5149707068914039998077413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866276091885386664103217 5149707068914039998077413)
                    ·
                      refine ⟨965570075421382499639515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5149707068914039998077413 965570075421382499639515)
                      ·
                        rfl

theorem cell23_1880441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1880441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880441 prefixEnd_1880441 := by exact prefixLift 1880441
  have htrace : WordTrace (prefixWord ++ tailWord_1880441) baseStart_1880441 baseEnd_1880441 := by
    simpa [prefixWord, tailWord_1880441, baseEnd_1880441] using wordTrace_append hprefix tailTrace_1880441
  have hstable : (prefixWord ++ tailWord_1880441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880441).length < 2 ^ (prefixWord ++ tailWord_1880441).sum := by decide
  have hdescent : baseEnd_1880441 < baseStart_1880441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880472 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 2, 4]
def baseStart_1880472 : Nat := 118140960795 + 1880472 * 2 ^ 59
def prefixEnd_1880472 : Nat := 4983230072969 + 3 ^ 40 * 1880472 * 2
def baseEnd_1880472 : Nat := 321861997773890626117291

theorem tailTrace_1880472 : CollatzResearch.WordTrace tailWord_1880472 prefixEnd_1880472 321861997773890626117291 := by
  unfold tailWord_1880472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293224221689288946965835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45724298962252385262621113 34293224221689288946965835)
  ·
    refine ⟨51439836332533933420448753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34293224221689288946965835 51439836332533933420448753)
    ·
      refine ⟨38579877249400450065336565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51439836332533933420448753 38579877249400450065336565)
      ·
        refine ⟨3616863492131292193625303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38579877249400450065336565 3616863492131292193625303)
        ·
          refine ⟨5425295238196938290437955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616863492131292193625303 5425295238196938290437955)
          ·
            refine ⟨8137942857295407435656933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425295238196938290437955 8137942857295407435656933)
            ·
              refine ⟨1525864285742888894185675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8137942857295407435656933 1525864285742888894185675)
              ·
                refine ⟨2288796428614333341278513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525864285742888894185675 2288796428614333341278513)
                ·
                  refine ⟨1716597321460750005958885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288796428614333341278513 1716597321460750005958885)
                  ·
                    refine ⟨321861997773890626117291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716597321460750005958885 321861997773890626117291)
                    ·
                      rfl

theorem cell23_1880472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_1880472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880472 prefixEnd_1880472 := by exact prefixLift 1880472
  have htrace : WordTrace (prefixWord ++ tailWord_1880472) baseStart_1880472 baseEnd_1880472 := by
    simpa [prefixWord, tailWord_1880472, baseEnd_1880472] using wordTrace_append hprefix tailTrace_1880472
  have hstable : (prefixWord ++ tailWord_1880472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880472).length < 2 ^ (prefixWord ++ tailWord_1880472).sum := by decide
  have hdescent : baseEnd_1880472 < baseStart_1880472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880521 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1880521 : Nat := 118140960795 + 1880521 * 2 ^ 59
def prefixEnd_1880521 : Nat := 4983230072969 + 3 ^ 40 * 1880521 * 2
def baseEnd_1880521 : Nat := 965611153873742186639147

theorem tailTrace_1880521 : CollatzResearch.WordTrace tailWord_1880521 prefixEnd_1880521 965611153873742186639147 := by
  unfold tailWord_1880521
  simp only [CollatzResearch.WordTrace]
  refine ⟨68588235620201059262465417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45725490413467372841643611 68588235620201059262465417)
  ·
    refine ⟨51441176715150794446849063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68588235620201059262465417 51441176715150794446849063)
    ·
      refine ⟨77161765072726191670273595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51441176715150794446849063 77161765072726191670273595)
      ·
        refine ⟨115742647609089287505410393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77161765072726191670273595 115742647609089287505410393)
        ·
          refine ⟨86806985706816965629057795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115742647609089287505410393 86806985706816965629057795)
          ·
            refine ⟨130210478560225448443586693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86806985706816965629057795 130210478560225448443586693)
            ·
              refine ⟨24414464730042271583172505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130210478560225448443586693 24414464730042271583172505)
              ·
                refine ⟨18310848547531703687379379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24414464730042271583172505 18310848547531703687379379)
                ·
                  refine ⟨27466272821297555531069069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310848547531703687379379 27466272821297555531069069)
                  ·
                    refine ⟨10299852307986583324150901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27466272821297555531069069 10299852307986583324150901)
                    ·
                      refine ⟨965611153873742186639147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10299852307986583324150901 965611153873742186639147)
                      ·
                        rfl

theorem cell23_1880521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1880521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880521 prefixEnd_1880521 := by exact prefixLift 1880521
  have htrace : WordTrace (prefixWord ++ tailWord_1880521) baseStart_1880521 baseEnd_1880521 := by
    simpa [prefixWord, tailWord_1880521, baseEnd_1880521] using wordTrace_append hprefix tailTrace_1880521
  have hstable : (prefixWord ++ tailWord_1880521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880521).length < 2 ^ (prefixWord ++ tailWord_1880521).sum := by decide
  have hdescent : baseEnd_1880521 < baseStart_1880521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880535 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_1880535 : Nat := 118140960795 + 1880535 * 2 ^ 59
def prefixEnd_1880535 : Nat := 4983230072969 + 3 ^ 40 * 1880535 * 2
def baseEnd_1880535 : Nat := 965618342602905131864083

theorem tailTrace_1880535 : CollatzResearch.WordTrace tailWord_1880535 prefixEnd_1880535 965618342602905131864083 := by
  unfold tailWord_1880535
  simp only [CollatzResearch.WordTrace]
  refine ⟨68588746242150339653475059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45725830828100226435650039 68588746242150339653475059)
  ·
    refine ⟨102883119363225509480212589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68588746242150339653475059 102883119363225509480212589)
    ·
      refine ⟨38581169761209566055079721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102883119363225509480212589 38581169761209566055079721)
      ·
        refine ⟨28935877320907174541309791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38581169761209566055079721 28935877320907174541309791)
        ·
          refine ⟨43403815981360761811964687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28935877320907174541309791 43403815981360761811964687)
          ·
            refine ⟨65105723972041142717947031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43403815981360761811964687 65105723972041142717947031)
            ·
              refine ⟨97658585958061714076920547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65105723972041142717947031 97658585958061714076920547)
              ·
                refine ⟨146487878937092571115380821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97658585958061714076920547 146487878937092571115380821)
                ·
                  refine ⟨1716654831294053567758369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 146487878937092571115380821 1716654831294053567758369)
                  ·
                    refine ⟨1287491123470540175818777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1716654831294053567758369 1287491123470540175818777)
                    ·
                      refine ⟨965618342602905131864083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287491123470540175818777 965618342602905131864083)
                      ·
                        rfl

theorem cell23_1880535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_1880535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880535 prefixEnd_1880535 := by exact prefixLift 1880535
  have htrace : WordTrace (prefixWord ++ tailWord_1880535) baseStart_1880535 baseEnd_1880535 := by
    simpa [prefixWord, tailWord_1880535, baseEnd_1880535] using wordTrace_append hprefix tailTrace_1880535
  have hstable : (prefixWord ++ tailWord_1880535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880535).length < 2 ^ (prefixWord ++ tailWord_1880535).sum := by decide
  have hdescent : baseEnd_1880535 < baseStart_1880535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880538 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1880538 : Nat := 118140960795 + 1880538 * 2 ^ 59
def prefixEnd_1880538 : Nat := 4983230072969 + 3 ^ 40 * 1880538 * 2
def baseEnd_1880538 : Nat := 965619883044868620126569

theorem tailTrace_1880538 : CollatzResearch.WordTrace tailWord_1880538 prefixEnd_1880538 965619883044868620126569 := by
  unfold tailWord_1880538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147213915284867791458567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45725903774092980777222845 17147213915284867791458567)
  ·
    refine ⟨25720820872927301687187851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17147213915284867791458567 25720820872927301687187851)
    ·
      refine ⟨38581231309390952530781777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25720820872927301687187851 38581231309390952530781777)
      ·
        refine ⟨28935923482043214398086333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38581231309390952530781777 28935923482043214398086333)
        ·
          refine ⟨10850971305766205399282375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28935923482043214398086333 10850971305766205399282375)
          ·
            refine ⟨16276456958649308098923563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850971305766205399282375 16276456958649308098923563)
            ·
              refine ⟨24414685437973962148385345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276456958649308098923563 24414685437973962148385345)
              ·
                refine ⟨18311014078480471611289009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24414685437973962148385345 18311014078480471611289009)
                ·
                  refine ⟨13733260558860353708466757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18311014078480471611289009 13733260558860353708466757)
                  ·
                    refine ⟨2574986354786316320337517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13733260558860353708466757 2574986354786316320337517)
                    ·
                      refine ⟨965619883044868620126569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2574986354786316320337517 965619883044868620126569)
                      ·
                        rfl

theorem cell23_1880538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1880538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880538 prefixEnd_1880538 := by exact prefixLift 1880538
  have htrace : WordTrace (prefixWord ++ tailWord_1880538) baseStart_1880538 baseEnd_1880538 := by
    simpa [prefixWord, tailWord_1880538, baseEnd_1880538] using wordTrace_append hprefix tailTrace_1880538
  have hstable : (prefixWord ++ tailWord_1880538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880538).length < 2 ^ (prefixWord ++ tailWord_1880538).sum := by decide
  have hdescent : baseEnd_1880538 < baseStart_1880538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880568 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_1880568 : Nat := 118140960795 + 1880568 * 2 ^ 59
def prefixEnd_1880568 : Nat := 4983230072969 + 3 ^ 40 * 1880568 * 2
def baseEnd_1880568 : Nat := 965635287464503502751431

theorem tailTrace_1880568 : CollatzResearch.WordTrace tailWord_1880568 prefixEnd_1880568 965635287464503502751431 := by
  unfold tailWord_1880568
  simp only [CollatzResearch.WordTrace]
  refine ⟨34294974925515393144713179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45726633234020524192950905 34294974925515393144713179)
  ·
    refine ⟨51442462388273089717069769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34294974925515393144713179 51442462388273089717069769)
    ·
      refine ⟨38581846791204817287802327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51442462388273089717069769 38581846791204817287802327)
      ·
        refine ⟨57872770186807225931703491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38581846791204817287802327 57872770186807225931703491)
        ·
          refine ⟨86809155280210838897555237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57872770186807225931703491 86809155280210838897555237)
          ·
            refine ⟨16276716615039532293291607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86809155280210838897555237 16276716615039532293291607)
            ·
              refine ⟨24415074922559298439937411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276716615039532293291607 24415074922559298439937411)
              ·
                refine ⟨36622612383838947659906117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24415074922559298439937411 36622612383838947659906117)
                ·
                  refine ⟨6866739821969802686232397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36622612383838947659906117 6866739821969802686232397)
                  ·
                    refine ⟨2575027433238676007337149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6866739821969802686232397 2575027433238676007337149)
                    ·
                      refine ⟨965635287464503502751431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575027433238676007337149 965635287464503502751431)
                      ·
                        rfl

theorem cell23_1880568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_1880568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880568 prefixEnd_1880568 := by exact prefixLift 1880568
  have htrace : WordTrace (prefixWord ++ tailWord_1880568) baseStart_1880568 baseEnd_1880568 := by
    simpa [prefixWord, tailWord_1880568, baseEnd_1880568] using wordTrace_append hprefix tailTrace_1880568
  have hstable : (prefixWord ++ tailWord_1880568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880568).length < 2 ^ (prefixWord ++ tailWord_1880568).sum := by decide
  have hdescent : baseEnd_1880568 < baseStart_1880568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880571 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 7]
def baseStart_1880571 : Nat := 118140960795 + 1880571 * 2 ^ 59
def prefixEnd_1880571 : Nat := 4983230072969 + 3 ^ 40 * 1880571 * 2
def baseEnd_1880571 : Nat := 321878942635488997004639

theorem tailTrace_1880571 : CollatzResearch.WordTrace tailWord_1880571 prefixEnd_1880571 321878942635488997004639 := by
  unfold tailWord_1880571
  simp only [CollatzResearch.WordTrace]
  refine ⟨68590059270019917801785567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45726706180013278534523711 68590059270019917801785567)
  ·
    refine ⟨102885088905029876702678351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68590059270019917801785567 102885088905029876702678351)
    ·
      refine ⟨154327633357544815054017527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102885088905029876702678351 154327633357544815054017527)
      ·
        refine ⟨231491450036317222581026291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154327633357544815054017527 231491450036317222581026291)
        ·
          refine ⟨347237175054475833871539437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231491450036317222581026291 347237175054475833871539437)
          ·
            refine ⟨130213940645428437701827289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347237175054475833871539437 130213940645428437701827289)
            ·
              refine ⟨97660455484071328276370467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130213940645428437701827289 97660455484071328276370467)
              ·
                refine ⟨146490683226106992414555701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97660455484071328276370467 146490683226106992414555701)
                ·
                  refine ⟨13733501552447530538864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146490683226106992414555701 13733501552447530538864597)
                  ·
                    refine ⟨321878942635488997004639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13733501552447530538864597 321878942635488997004639)
                    ·
                      rfl

theorem cell23_1880571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_1880571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880571 prefixEnd_1880571 := by exact prefixLift 1880571
  have htrace : WordTrace (prefixWord ++ tailWord_1880571) baseStart_1880571 baseEnd_1880571 := by
    simpa [prefixWord, tailWord_1880571, baseEnd_1880571] using wordTrace_append hprefix tailTrace_1880571
  have hstable : (prefixWord ++ tailWord_1880571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880571).length < 2 ^ (prefixWord ++ tailWord_1880571).sum := by decide
  have hdescent : baseEnd_1880571 < baseStart_1880571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880588 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1880588 : Nat := 118140960795 + 1880588 * 2 ^ 59
def prefixEnd_1880588 : Nat := 4983230072969 + 3 ^ 40 * 1880588 * 2
def baseEnd_1880588 : Nat := 321881852359197808167113

theorem tailTrace_1880588 : CollatzResearch.WordTrace tailWord_1880588 prefixEnd_1880588 321881852359197808167113 := by
  unfold tailWord_1880588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295339655479164852577209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45727119540638886470102945 34295339655479164852577209)
  ·
    refine ⟨25721504741609373639432907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34295339655479164852577209 25721504741609373639432907)
    ·
      refine ⟨38582257112414060459149361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25721504741609373639432907 38582257112414060459149361)
      ·
        refine ⟨28936692834310545344362021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38582257112414060459149361 28936692834310545344362021)
        ·
          refine ⟨5425629906433227252067879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28936692834310545344362021 5425629906433227252067879)
          ·
            refine ⟨8138444859649840878101819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425629906433227252067879 8138444859649840878101819)
            ·
              refine ⟨12207667289474761317152729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138444859649840878101819 12207667289474761317152729)
              ·
                refine ⟨9155750467106070987864547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12207667289474761317152729 9155750467106070987864547)
                ·
                  refine ⟨13733625700659106481796821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9155750467106070987864547 13733625700659106481796821)
                  ·
                    refine ⟨321881852359197808167113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13733625700659106481796821 321881852359197808167113)
                    ·
                      rfl

theorem cell23_1880588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1880588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880588 prefixEnd_1880588 := by exact prefixLift 1880588
  have htrace : WordTrace (prefixWord ++ tailWord_1880588) baseStart_1880588 baseEnd_1880588 := by
    simpa [prefixWord, tailWord_1880588, baseEnd_1880588] using wordTrace_append hprefix tailTrace_1880588
  have hstable : (prefixWord ++ tailWord_1880588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880588).length < 2 ^ (prefixWord ++ tailWord_1880588).sum := by decide
  have hdescent : baseEnd_1880588 < baseStart_1880588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880622 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1880622 : Nat := 118140960795 + 1880622 * 2 ^ 59
def prefixEnd_1880622 : Nat := 4983230072969 + 3 ^ 40 * 1880622 * 2
def baseEnd_1880622 : Nat := 321887671806615430492061

theorem tailTrace_1880622 : CollatzResearch.WordTrace tailWord_1880622 prefixEnd_1880622 321887671806615430492061 := by
  unfold tailWord_1880622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573989924104394188986515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45727946261890102341261413 8573989924104394188986515)
  ·
    refine ⟨12860984886156591283479773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8573989924104394188986515 12860984886156591283479773)
    ·
      refine ⟨4822869332308721731304915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12860984886156591283479773 4822869332308721731304915)
      ·
        refine ⟨7234303998463082596957373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822869332308721731304915 7234303998463082596957373)
        ·
          refine ⟨2712863999423655973859015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234303998463082596957373 2712863999423655973859015)
          ·
            refine ⟨4069295999135483960788523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712863999423655973859015 4069295999135483960788523)
            ·
              refine ⟨6103943998703225941182785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069295999135483960788523 6103943998703225941182785)
              ·
                refine ⟨4577957999027419455887089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103943998703225941182785 4577957999027419455887089)
                ·
                  refine ⟨3433468499270564591915317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4577957999027419455887089 3433468499270564591915317)
                  ·
                    refine ⟨321887671806615430492061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3433468499270564591915317 321887671806615430492061)
                    ·
                      rfl

theorem cell23_1880622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1880622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880622 prefixEnd_1880622 := by exact prefixLift 1880622
  have htrace : WordTrace (prefixWord ++ tailWord_1880622) baseStart_1880622 baseEnd_1880622 := by
    simpa [prefixWord, tailWord_1880622, baseEnd_1880622] using wordTrace_append hprefix tailTrace_1880622
  have hstable : (prefixWord ++ tailWord_1880622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880622).length < 2 ^ (prefixWord ++ tailWord_1880622).sum := by decide
  have hdescent : baseEnd_1880622 < baseStart_1880622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880625 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_1880625 : Nat := 118140960795 + 1880625 * 2 ^ 59
def prefixEnd_1880625 : Nat := 4983230072969 + 3 ^ 40 * 1880625 * 2
def baseEnd_1880625 : Nat := 965664555861809779738669

theorem tailTrace_1880625 : CollatzResearch.WordTrace tailWord_1880625 prefixEnd_1880625 965664555861809779738669 := by
  unfold tailWord_1880625
  simp only [CollatzResearch.WordTrace]
  refine ⟨68592028811824285024251329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45728019207882856682834219 68592028811824285024251329)
  ·
    refine ⟨51444021608868213768188497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68592028811824285024251329 51444021608868213768188497)
    ·
      refine ⟨38583016206651160326141373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51444021608868213768188497 38583016206651160326141373)
      ·
        refine ⟨14468631077494185122303015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38583016206651160326141373 14468631077494185122303015)
        ·
          refine ⟨21702946616241277683454523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14468631077494185122303015 21702946616241277683454523)
          ·
            refine ⟨32554419924361916525181785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21702946616241277683454523 32554419924361916525181785)
            ·
              refine ⟨24415814943271437393886339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32554419924361916525181785 24415814943271437393886339)
              ·
                refine ⟨36623722414907156090829509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24415814943271437393886339 36623722414907156090829509)
                ·
                  refine ⟨6866947952795091767030533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36623722414907156090829509 6866947952795091767030533)
                  ·
                    refine ⟨1287552741149079706318225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866947952795091767030533 1287552741149079706318225)
                    ·
                      refine ⟨965664555861809779738669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287552741149079706318225 965664555861809779738669)
                      ·
                        rfl

theorem cell23_1880625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_1880625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880625 prefixEnd_1880625 := by exact prefixLift 1880625
  have htrace : WordTrace (prefixWord ++ tailWord_1880625) baseStart_1880625 baseEnd_1880625 := by
    simpa [prefixWord, tailWord_1880625, baseEnd_1880625] using wordTrace_append hprefix tailTrace_1880625
  have hstable : (prefixWord ++ tailWord_1880625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880625).length < 2 ^ (prefixWord ++ tailWord_1880625).sum := by decide
  have hdescent : baseEnd_1880625 < baseStart_1880625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880686 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1880686 : Nat := 118140960795 + 1880686 * 2 ^ 59
def prefixEnd_1880686 : Nat := 4983230072969 + 3 ^ 40 * 1880686 * 2
def baseEnd_1880686 : Nat := 321898626060578013691963

theorem tailTrace_1880686 : CollatzResearch.WordTrace tailWord_1880686 prefixEnd_1880686 321898626060578013691963 := by
  unfold tailWord_1880686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574281708075411555277739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45729502443068861628147941 8574281708075411555277739)
  ·
    refine ⟨12861422562113117332916609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8574281708075411555277739 12861422562113117332916609)
    ·
      refine ⟨9646066921584837999687457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12861422562113117332916609 9646066921584837999687457)
      ·
        refine ⟨7234550191188628499765593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9646066921584837999687457 7234550191188628499765593)
        ·
          refine ⟨5425912643391471374824195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7234550191188628499765593 5425912643391471374824195)
          ·
            refine ⟨8138868965087207062236293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425912643391471374824195 8138868965087207062236293)
            ·
              refine ⟨1526037930953851324169305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8138868965087207062236293 1526037930953851324169305)
              ·
                refine ⟨1144528448215388493126979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526037930953851324169305 1144528448215388493126979)
                ·
                  refine ⟨1716792672323082739690469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144528448215388493126979 1716792672323082739690469)
                  ·
                    refine ⟨321898626060578013691963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716792672323082739690469 321898626060578013691963)
                    ·
                      rfl

theorem cell23_1880686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1880686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880686 prefixEnd_1880686 := by exact prefixLift 1880686
  have htrace : WordTrace (prefixWord ++ tailWord_1880686) baseStart_1880686 baseEnd_1880686 := by
    simpa [prefixWord, tailWord_1880686, baseEnd_1880686] using wordTrace_append hprefix tailTrace_1880686
  have hstable : (prefixWord ++ tailWord_1880686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880686).length < 2 ^ (prefixWord ++ tailWord_1880686).sum := by decide
  have hdescent : baseEnd_1880686 < baseStart_1880686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880715 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 8, 2]
def baseStart_1880715 : Nat := 118140960795 + 1880715 * 2 ^ 59
def prefixEnd_1880715 : Nat := 4983230072969 + 3 ^ 40 * 1880715 * 2
def baseEnd_1880715 : Nat := 965710769120714427613255

theorem tailTrace_1880715 : CollatzResearch.WordTrace tailWord_1880715 prefixEnd_1880715 965710769120714427613255 := by
  unfold tailWord_1880715
  simp only [CollatzResearch.WordTrace]
  refine ⟨68595311381498230395027599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45730207587665486930018399 68595311381498230395027599)
  ·
    refine ⟨102892967072247345592541399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68595311381498230395027599 102892967072247345592541399)
    ·
      refine ⟨154339450608371018388812099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102892967072247345592541399 154339450608371018388812099)
      ·
        refine ⟨231509175912556527583218149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154339450608371018388812099 231509175912556527583218149)
        ·
          refine ⟨43407970483604348921853403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231509175912556527583218149 43407970483604348921853403)
          ·
            refine ⟨65111955725406523382780105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43407970483604348921853403 65111955725406523382780105)
            ·
              refine ⟨48833966794054892537085079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65111955725406523382780105 48833966794054892537085079)
              ·
                refine ⟨73250950191082338805627619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48833966794054892537085079 73250950191082338805627619)
                ·
                  refine ⟨109876425286623508208441429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73250950191082338805627619 109876425286623508208441429)
                  ·
                    refine ⟨1287614358827619236817673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109876425286623508208441429 1287614358827619236817673)
                    ·
                      refine ⟨965710769120714427613255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287614358827619236817673 965710769120714427613255)
                      ·
                        rfl

theorem cell23_1880715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8, 2].length) (baseStart_1880715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880715 prefixEnd_1880715 := by exact prefixLift 1880715
  have htrace : WordTrace (prefixWord ++ tailWord_1880715) baseStart_1880715 baseEnd_1880715 := by
    simpa [prefixWord, tailWord_1880715, baseEnd_1880715] using wordTrace_append hprefix tailTrace_1880715
  have hstable : (prefixWord ++ tailWord_1880715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880715).length < 2 ^ (prefixWord ++ tailWord_1880715).sum := by decide
  have hdescent : baseEnd_1880715 < baseStart_1880715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880759 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 1, 6]
def baseStart_1880759 : Nat := 118140960795 + 1880759 * 2 ^ 59
def prefixEnd_1880759 : Nat := 4983230072969 + 3 ^ 40 * 1880759 * 2
def baseEnd_1880759 : Nat := 321911120756504085154351

theorem tailTrace_1880759 : CollatzResearch.WordTrace tailWord_1880759 prefixEnd_1880759 321911120756504085154351 := by
  unfold tailWord_1880759
  simp only [CollatzResearch.WordTrace]
  refine ⟨68596916193338825909629331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45731277462225883939752887 68596916193338825909629331)
  ·
    refine ⟨102895374290008238864443997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68596916193338825909629331 102895374290008238864443997)
    ·
      refine ⟨38585765358753089574166499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102895374290008238864443997 38585765358753089574166499)
      ·
        refine ⟨57878648038129634361249749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38585765358753089574166499 57878648038129634361249749)
        ·
          refine ⟨1356530813393663305341791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57878648038129634361249749 1356530813393663305341791)
          ·
            refine ⟨2034796220090494958012687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356530813393663305341791 2034796220090494958012687)
            ·
              refine ⟨3052194330135742437019031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034796220090494958012687 3052194330135742437019031)
              ·
                refine ⟨4578291495203613655528547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052194330135742437019031 4578291495203613655528547)
                ·
                  refine ⟨6867437242805420483292821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578291495203613655528547 6867437242805420483292821)
                  ·
                    refine ⟨321911120756504085154351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6867437242805420483292821 321911120756504085154351)
                    ·
                      rfl

theorem cell23_1880759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_1880759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880759 prefixEnd_1880759 := by exact prefixLift 1880759
  have htrace : WordTrace (prefixWord ++ tailWord_1880759) baseStart_1880759 baseEnd_1880759 := by
    simpa [prefixWord, tailWord_1880759, baseEnd_1880759] using wordTrace_append hprefix tailTrace_1880759
  have hstable : (prefixWord ++ tailWord_1880759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880759).length < 2 ^ (prefixWord ++ tailWord_1880759).sum := by decide
  have hdescent : baseEnd_1880759 < baseStart_1880759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880772 : List Nat := [2, 3, 3, 1, 1, 2, 4, 7]
def baseStart_1880772 : Nat := 118140960795 + 1880772 * 2 ^ 59
def prefixEnd_1880772 : Nat := 4983230072969 + 3 ^ 40 * 1880772 * 2
def baseEnd_1880772 : Nat := 35768149537704470540759

theorem tailTrace_1880772 : CollatzResearch.WordTrace tailWord_1880772 prefixEnd_1880772 35768149537704470540759 := by
  unfold tailWord_1880772
  simp only [CollatzResearch.WordTrace]
  refine ⟨34298695171145864564926285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45731593561527819419901713 34298695171145864564926285)
  ·
    refine ⟨12862010689179699211847357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34298695171145864564926285 12862010689179699211847357)
    ·
      refine ⟨4823254008442387204442759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12862010689179699211847357 4823254008442387204442759)
      ·
        refine ⟨7234881012663580806664139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823254008442387204442759 7234881012663580806664139)
        ·
          refine ⟨10852321518995371209996209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234881012663580806664139 10852321518995371209996209)
          ·
            refine ⟨8139241139246528407497157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10852321518995371209996209 8139241139246528407497157)
            ·
              refine ⟨1526107713608724076405717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8139241139246528407497157 1526107713608724076405717)
              ·
                refine ⟨35768149537704470540759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1526107713608724076405717 35768149537704470540759)
                ·
                  rfl

theorem cell23_1880772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 7].length) (baseStart_1880772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880772 prefixEnd_1880772 := by exact prefixLift 1880772
  have htrace : WordTrace (prefixWord ++ tailWord_1880772) baseStart_1880772 baseEnd_1880772 := by
    simpa [prefixWord, tailWord_1880772, baseEnd_1880772] using wordTrace_append hprefix tailTrace_1880772
  have hstable : (prefixWord ++ tailWord_1880772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880772).length < 2 ^ (prefixWord ++ tailWord_1880772).sum := by decide
  have hdescent : baseEnd_1880772 < baseStart_1880772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880789 : List Nat := [1, 3, 2, 5, 2, 1, 9]
def baseStart_1880789 : Nat := 118140960795 + 1880789 * 2 ^ 59
def prefixEnd_1880789 : Nat := 4983230072969 + 3 ^ 40 * 1880789 * 2
def baseEnd_1880789 : Nat := 11922824280112927630715

theorem tailTrace_1880789 : CollatzResearch.WordTrace tailWord_1880789 prefixEnd_1880789 11922824280112927630715 := by
  unfold tailWord_1880789
  simp only [CollatzResearch.WordTrace]
  refine ⟨68598010383230141033221421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45732006922153427355480947 68598010383230141033221421)
  ·
    refine ⟨25724253893711302887458033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68598010383230141033221421 25724253893711302887458033)
    ·
      refine ⟨19293190420283477165593525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25724253893711302887458033 19293190420283477165593525)
      ·
        refine ⟨1808736601901575984274393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19293190420283477165593525 1808736601901575984274393)
        ·
          refine ⟨1356552451426181988205795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808736601901575984274393 1356552451426181988205795)
          ·
            refine ⟨2034828677139272982308693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356552451426181988205795 2034828677139272982308693)
            ·
              refine ⟨11922824280112927630715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2034828677139272982308693 11922824280112927630715)
              ·
                rfl

theorem cell23_1880789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 9].length) (baseStart_1880789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880789 prefixEnd_1880789 := by exact prefixLift 1880789
  have htrace : WordTrace (prefixWord ++ tailWord_1880789) baseStart_1880789 baseEnd_1880789 := by
    simpa [prefixWord, tailWord_1880789, baseEnd_1880789] using wordTrace_append hprefix tailTrace_1880789
  have hstable : (prefixWord ++ tailWord_1880789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880789).length < 2 ^ (prefixWord ++ tailWord_1880789).sum := by decide
  have hdescent : baseEnd_1880789 < baseStart_1880789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880820 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1880820 : Nat := 118140960795 + 1880820 * 2 ^ 59
def prefixEnd_1880820 : Nat := 4983230072969 + 3 ^ 40 * 1880820 * 2
def baseEnd_1880820 : Nat := 965764684589436516800273

theorem tailTrace_1880820 : CollatzResearch.WordTrace tailWord_1880820 prefixEnd_1880820 965764684589436516800273 := by
  unfold tailWord_1880820
  simp only [CollatzResearch.WordTrace]
  refine ⟨34299570523058916663799957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45732760697411888885066609 34299570523058916663799957)
  ·
    refine ⟨1607792368268386718615623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34299570523058916663799957 1607792368268386718615623)
    ·
      refine ⟨2411688552402580077923435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1607792368268386718615623 2411688552402580077923435)
      ·
        refine ⟨3617532828603870116885153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411688552402580077923435 3617532828603870116885153)
        ·
          refine ⟨2713149621452902587663865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3617532828603870116885153 2713149621452902587663865)
          ·
            refine ⟨2034862216089676940747899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2713149621452902587663865 2034862216089676940747899)
            ·
              refine ⟨3052293324134515411121849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034862216089676940747899 3052293324134515411121849)
              ·
                refine ⟨2289219993100886558341387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052293324134515411121849 2289219993100886558341387)
                ·
                  refine ⟨3433829989651329837512081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289219993100886558341387 3433829989651329837512081)
                  ·
                    refine ⟨2575372492238497378134061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3433829989651329837512081 2575372492238497378134061)
                    ·
                      refine ⟨965764684589436516800273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575372492238497378134061 965764684589436516800273)
                      ·
                        rfl

theorem cell23_1880820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1880820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880820 prefixEnd_1880820 := by exact prefixLift 1880820
  have htrace : WordTrace (prefixWord ++ tailWord_1880820) baseStart_1880820 baseEnd_1880820 := by
    simpa [prefixWord, tailWord_1880820, baseEnd_1880820] using wordTrace_append hprefix tailTrace_1880820
  have hstable : (prefixWord ++ tailWord_1880820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880820).length < 2 ^ (prefixWord ++ tailWord_1880820).sum := by decide
  have hdescent : baseEnd_1880820 < baseStart_1880820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880835 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_1880835 : Nat := 118140960795 + 1880835 * 2 ^ 59
def prefixEnd_1880835 : Nat := 4983230072969 + 3 ^ 40 * 1880835 * 2
def baseEnd_1880835 : Nat := 965772386799253958112703

theorem tailTrace_1880835 : CollatzResearch.WordTrace tailWord_1880835 prefixEnd_1880835 965772386799253958112703 := by
  unfold tailWord_1880835
  simp only [CollatzResearch.WordTrace]
  refine ⟨68599688141063490889395959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45733125427375660592930639 68599688141063490889395959)
  ·
    refine ⟨102899532211595236334093939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68599688141063490889395959 102899532211595236334093939)
    ·
      refine ⟨154349298317392854501140909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102899532211595236334093939 154349298317392854501140909)
      ·
        refine ⟨57880986869022320437927841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154349298317392854501140909 57880986869022320437927841)
        ·
          refine ⟨43410740151766740328445881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57880986869022320437927841 43410740151766740328445881)
          ·
            refine ⟨32558055113825055246334411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43410740151766740328445881 32558055113825055246334411)
            ·
              refine ⟨48837082670737582869501617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32558055113825055246334411 48837082670737582869501617)
              ·
                refine ⟨36627812003053187152126213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48837082670737582869501617 36627812003053187152126213)
                ·
                  refine ⟨6867714750572472591023665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36627812003053187152126213 6867714750572472591023665)
                  ·
                    refine ⟨5150786062929354443267749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867714750572472591023665 5150786062929354443267749)
                    ·
                      refine ⟨965772386799253958112703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5150786062929354443267749 965772386799253958112703)
                      ·
                        rfl

theorem cell23_1880835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_1880835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880835 prefixEnd_1880835 := by exact prefixLift 1880835
  have htrace : WordTrace (prefixWord ++ tailWord_1880835) baseStart_1880835 baseEnd_1880835 := by
    simpa [prefixWord, tailWord_1880835, baseEnd_1880835] using wordTrace_append hprefix tailTrace_1880835
  have hstable : (prefixWord ++ tailWord_1880835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880835).length < 2 ^ (prefixWord ++ tailWord_1880835).sum := by decide
  have hdescent : baseEnd_1880835 < baseStart_1880835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880839 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1880839 : Nat := 118140960795 + 1880839 * 2 ^ 59
def prefixEnd_1880839 : Nat := 4983230072969 + 3 ^ 40 * 1880839 * 2
def baseEnd_1880839 : Nat := 965774440721871942462685

theorem tailTrace_1880839 : CollatzResearch.WordTrace tailWord_1880839 prefixEnd_1880839 965774440721871942462685 := by
  unfold tailWord_1880839
  simp only [CollatzResearch.WordTrace]
  refine ⟨68599834033048999572541571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45733222688699333048361047 68599834033048999572541571)
  ·
    refine ⟨102899751049573499358812357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68599834033048999572541571 102899751049573499358812357)
    ·
      refine ⟨19293703321795031129777317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102899751049573499358812357 19293703321795031129777317)
      ·
        refine ⟨3617569372836568336833247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19293703321795031129777317 3617569372836568336833247)
        ·
          refine ⟨5426354059254852505249871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617569372836568336833247 5426354059254852505249871)
          ·
            refine ⟨8139531088882278757874807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426354059254852505249871 8139531088882278757874807)
            ·
              refine ⟨12209296633323418136812211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139531088882278757874807 12209296633323418136812211)
              ·
                refine ⟨18313944949985127205218317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209296633323418136812211 18313944949985127205218317)
                ·
                  refine ⟨6867729356244422701956869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18313944949985127205218317 6867729356244422701956869)
                  ·
                    refine ⟨1287699254295829256616913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867729356244422701956869 1287699254295829256616913)
                    ·
                      refine ⟨965774440721871942462685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287699254295829256616913 965774440721871942462685)
                      ·
                        rfl

theorem cell23_1880839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1880839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880839 prefixEnd_1880839 := by exact prefixLift 1880839
  have htrace : WordTrace (prefixWord ++ tailWord_1880839) baseStart_1880839 baseEnd_1880839 := by
    simpa [prefixWord, tailWord_1880839, baseEnd_1880839] using wordTrace_append hprefix tailTrace_1880839
  have hstable : (prefixWord ++ tailWord_1880839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880839).length < 2 ^ (prefixWord ++ tailWord_1880839).sum := by decide
  have hdescent : baseEnd_1880839 < baseStart_1880839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880875 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 6, 5]
def baseStart_1880875 : Nat := 118140960795 + 1880875 * 2 ^ 59
def prefixEnd_1880875 : Nat := 4983230072969 + 3 ^ 40 * 1880875 * 2
def baseEnd_1880875 : Nat := 321930975341811267204173

theorem tailTrace_1880875 : CollatzResearch.WordTrace tailWord_1880875 prefixEnd_1880875 321930975341811267204173 := by
  unfold tailWord_1880875
  simp only [CollatzResearch.WordTrace]
  refine ⟨68601147060918577720852079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45734098040612385147234719 68601147060918577720852079)
  ·
    refine ⟨102901720591377866581278119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68601147060918577720852079 102901720591377866581278119)
    ·
      refine ⟨154352580887066799871917179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102901720591377866581278119 154352580887066799871917179)
      ·
        refine ⟨231528871330600199807875769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154352580887066799871917179 231528871330600199807875769)
        ·
          refine ⟨173646653497950149855906827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231528871330600199807875769 173646653497950149855906827)
          ·
            refine ⟨260469980246925224783860241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173646653497950149855906827 260469980246925224783860241)
            ·
              refine ⟨195352485185193918587895181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260469980246925224783860241 195352485185193918587895181)
              ·
                refine ⟨73257181944447719470460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195352485185193918587895181 73257181944447719470460693)
                ·
                  refine ⟨3433930403645986850177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73257181944447719470460693 3433930403645986850177845)
                  ·
                    refine ⟨321930975341811267204173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3433930403645986850177845 321930975341811267204173)
                    ·
                      rfl

theorem cell23_1880875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 5].length) (baseStart_1880875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880875 prefixEnd_1880875 := by exact prefixLift 1880875
  have htrace : WordTrace (prefixWord ++ tailWord_1880875) baseStart_1880875 baseEnd_1880875 := by
    simpa [prefixWord, tailWord_1880875, baseEnd_1880875] using wordTrace_append hprefix tailTrace_1880875
  have hstable : (prefixWord ++ tailWord_1880875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880875).length < 2 ^ (prefixWord ++ tailWord_1880875).sum := by decide
  have hdescent : baseEnd_1880875 < baseStart_1880875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880912 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1880912 : Nat := 118140960795 + 1880912 * 2 ^ 59
def prefixEnd_1880912 : Nat := 4983230072969 + 3 ^ 40 * 1880912 * 2
def baseEnd_1880912 : Nat := 965811924809650156849849

theorem tailTrace_1880912 : CollatzResearch.WordTrace tailWord_1880912 prefixEnd_1880912 965811924809650156849849 := by
  unfold tailWord_1880912
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301248280892266519974495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45734997707856355359965993 34301248280892266519974495)
  ·
    refine ⟨51451872421338399779961743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34301248280892266519974495 51451872421338399779961743)
    ·
      refine ⟨77177808632007599669942615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51451872421338399779961743 77177808632007599669942615)
      ·
        refine ⟨115766712948011399504913923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77177808632007599669942615 115766712948011399504913923)
        ·
          refine ⟨173650069422017099257370885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115766712948011399504913923 173650069422017099257370885)
          ·
            refine ⟨32559388016628206110757041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173650069422017099257370885 32559388016628206110757041)
            ·
              refine ⟨24419541012471154583067781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32559388016628206110757041 24419541012471154583067781)
              ·
                refine ⟨4578663939838341484325209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24419541012471154583067781 4578663939838341484325209)
                ·
                  refine ⟨3433997954878756113243907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578663939838341484325209 3433997954878756113243907)
                  ·
                    refine ⟨5150996932318134169865861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3433997954878756113243907 5150996932318134169865861)
                    ·
                      refine ⟨965811924809650156849849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5150996932318134169865861 965811924809650156849849)
                      ·
                        rfl

theorem cell23_1880912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1880912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880912 prefixEnd_1880912 := by exact prefixLift 1880912
  have htrace : WordTrace (prefixWord ++ tailWord_1880912) baseStart_1880912 baseEnd_1880912 := by
    simpa [prefixWord, tailWord_1880912, baseEnd_1880912] using wordTrace_append hprefix tailTrace_1880912
  have hstable : (prefixWord ++ tailWord_1880912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880912).length < 2 ^ (prefixWord ++ tailWord_1880912).sum := by decide
  have hdescent : baseEnd_1880912 < baseStart_1880912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880915 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_1880915 : Nat := 118140960795 + 1880915 * 2 ^ 59
def prefixEnd_1880915 : Nat := 4983230072969 + 3 ^ 40 * 1880915 * 2
def baseEnd_1880915 : Nat := 965813465251613645112335

theorem tailTrace_1880915 : CollatzResearch.WordTrace tailWord_1880915 prefixEnd_1880915 965813465251613645112335 := by
  unfold tailWord_1880915
  simp only [CollatzResearch.WordTrace]
  refine ⟨68602605980773664552308199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45735070653849109701538799 68602605980773664552308199)
  ·
    refine ⟨102903908971160496828462299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68602605980773664552308199 102903908971160496828462299)
    ·
      refine ⟨154355863456740745242693449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102903908971160496828462299 154355863456740745242693449)
      ·
        refine ⟨115766897592555558932020087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154355863456740745242693449 115766897592555558932020087)
        ·
          refine ⟨173650346388833338398030131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115766897592555558932020087 173650346388833338398030131)
          ·
            refine ⟨260475519583250007597045197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173650346388833338398030131 260475519583250007597045197)
            ·
              refine ⟨97678319843718752848891949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260475519583250007597045197 97678319843718752848891949)
              ·
                refine ⟨36629369941394532318334481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97678319843718752848891949 36629369941394532318334481)
                ·
                  refine ⟨27472027456045899238750861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36629369941394532318334481 27472027456045899238750861)
                  ·
                    refine ⟨10302010296017212214531573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27472027456045899238750861 10302010296017212214531573)
                    ·
                      refine ⟨965813465251613645112335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10302010296017212214531573 965813465251613645112335)
                      ·
                        rfl

theorem cell23_1880915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_1880915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880915 prefixEnd_1880915 := by exact prefixLift 1880915
  have htrace : WordTrace (prefixWord ++ tailWord_1880915) baseStart_1880915 baseEnd_1880915 := by
    simpa [prefixWord, tailWord_1880915, baseEnd_1880915] using wordTrace_append hprefix tailTrace_1880915
  have hstable : (prefixWord ++ tailWord_1880915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880915).length < 2 ^ (prefixWord ++ tailWord_1880915).sum := by decide
  have hdescent : baseEnd_1880915 < baseStart_1880915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880949 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1880949 : Nat := 118140960795 + 1880949 * 2 ^ 59
def prefixEnd_1880949 : Nat := 4983230072969 + 3 ^ 40 * 1880949 * 2
def baseEnd_1880949 : Nat := 965830923593866512087179

theorem tailTrace_1880949 : CollatzResearch.WordTrace tailWord_1880949 prefixEnd_1880949 965830923593866512087179 := by
  unfold tailWord_1880949
  simp only [CollatzResearch.WordTrace]
  refine ⟨68603846062650488359045901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45735897375100325572697267 68603846062650488359045901)
  ·
    refine ⟨25726442273493933134642213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68603846062650488359045901 25726442273493933134642213)
    ·
      refine ⟨4823707926280112462745415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25726442273493933134642213 4823707926280112462745415)
      ·
        refine ⟨7235561889420168694118123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823707926280112462745415 7235561889420168694118123)
        ·
          refine ⟨10853342834130253041177185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235561889420168694118123 10853342834130253041177185)
          ·
            refine ⟨8140007125597689780882889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10853342834130253041177185 8140007125597689780882889)
            ·
              refine ⟨6105005344198267335662167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140007125597689780882889 6105005344198267335662167)
              ·
                refine ⟨9157508016297401003493251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105005344198267335662167 9157508016297401003493251)
                ·
                  refine ⟨13736262024446101505239877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9157508016297401003493251 13736262024446101505239877)
                  ·
                    refine ⟨2575549129583644032232477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13736262024446101505239877 2575549129583644032232477)
                    ·
                      refine ⟨965830923593866512087179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575549129583644032232477 965830923593866512087179)
                      ·
                        rfl

theorem cell23_1880949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1880949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880949 prefixEnd_1880949 := by exact prefixLift 1880949
  have htrace : WordTrace (prefixWord ++ tailWord_1880949) baseStart_1880949 baseEnd_1880949 := by
    simpa [prefixWord, tailWord_1880949, baseEnd_1880949] using wordTrace_append hprefix tailTrace_1880949
  have hstable : (prefixWord ++ tailWord_1880949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880949).length < 2 ^ (prefixWord ++ tailWord_1880949).sum := by decide
  have hdescent : baseEnd_1880949 < baseStart_1880949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880979 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 3]
def baseStart_1880979 : Nat := 118140960795 + 1880979 * 2 ^ 59
def prefixEnd_1880979 : Nat := 4983230072969 + 3 ^ 40 * 1880979 * 2
def baseEnd_1880979 : Nat := 965846328013501394712041

theorem tailTrace_1880979 : CollatzResearch.WordTrace tailWord_1880979 prefixEnd_1880979 965846328013501394712041 := by
  unfold tailWord_1880979
  simp only [CollatzResearch.WordTrace]
  refine ⟨68604940252541803482637991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45736626835027868988425327 68604940252541803482637991)
  ·
    refine ⟨102907410378812705223956987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68604940252541803482637991 102907410378812705223956987)
    ·
      refine ⟨154361115568219057835935481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102907410378812705223956987 154361115568219057835935481)
      ·
        refine ⟨115770836676164293376951611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154361115568219057835935481 115770836676164293376951611)
        ·
          refine ⟨173656255014246440065427417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115770836676164293376951611 173656255014246440065427417)
          ·
            refine ⟨130242191260684830049070563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173656255014246440065427417 130242191260684830049070563)
            ·
              refine ⟨195363286891027245073605845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130242191260684830049070563 195363286891027245073605845)
              ·
                refine ⟨4578827036508451056412637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195363286891027245073605845 4578827036508451056412637)
                ·
                  refine ⟨1717060138690669146154739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4578827036508451056412637 1717060138690669146154739)
                  ·
                    refine ⟨2575590208036003719232109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1717060138690669146154739 2575590208036003719232109)
                    ·
                      refine ⟨965846328013501394712041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575590208036003719232109 965846328013501394712041)
                      ·
                        rfl

theorem cell23_1880979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_1880979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880979 prefixEnd_1880979 := by exact prefixLift 1880979
  have htrace : WordTrace (prefixWord ++ tailWord_1880979) baseStart_1880979 baseEnd_1880979 := by
    simpa [prefixWord, tailWord_1880979, baseEnd_1880979] using wordTrace_append hprefix tailTrace_1880979
  have hstable : (prefixWord ++ tailWord_1880979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880979).length < 2 ^ (prefixWord ++ tailWord_1880979).sum := by decide
  have hdescent : baseEnd_1880979 < baseStart_1880979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881013 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1881013 : Nat := 118140960795 + 1881013 * 2 ^ 59
def prefixEnd_1881013 : Nat := 4983230072969 + 3 ^ 40 * 1881013 * 2
def baseEnd_1881013 : Nat := 965863786355754261686885

theorem tailTrace_1881013 : CollatzResearch.WordTrace tailWord_1881013 prefixEnd_1881013 965863786355754261686885 := by
  unfold tailWord_1881013
  simp only [CollatzResearch.WordTrace]
  refine ⟨68606180334418627289375693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45737453556279084859583795 68606180334418627289375693)
  ·
    refine ⟨25727317625406985233515885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68606180334418627289375693 25727317625406985233515885)
    ·
      refine ⟨9647744109527619462568457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25727317625406985233515885 9647744109527619462568457)
      ·
        refine ⟨7235808082145714596926343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9647744109527619462568457 7235808082145714596926343)
        ·
          refine ⟨10853712123218571895389515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235808082145714596926343 10853712123218571895389515)
          ·
            refine ⟨16280568184827857843084273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853712123218571895389515 16280568184827857843084273)
            ·
              refine ⟨12210426138620893382313205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16280568184827857843084273 12210426138620893382313205)
              ·
                refine ⟨1144727450495708754591863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12210426138620893382313205 1144727450495708754591863)
                ·
                  refine ⟨1717091175743563131887795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144727450495708754591863 1717091175743563131887795)
                  ·
                    refine ⟨2575636763615344697831693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1717091175743563131887795 2575636763615344697831693)
                    ·
                      refine ⟨965863786355754261686885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575636763615344697831693 965863786355754261686885)
                      ·
                        rfl

theorem cell23_1881013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1881013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881013 prefixEnd_1881013 := by exact prefixLift 1881013
  have htrace : WordTrace (prefixWord ++ tailWord_1881013) baseStart_1881013 baseEnd_1881013 := by
    simpa [prefixWord, tailWord_1881013, baseEnd_1881013] using wordTrace_append hprefix tailTrace_1881013
  have hstable : (prefixWord ++ tailWord_1881013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881013).length < 2 ^ (prefixWord ++ tailWord_1881013).sum := by decide
  have hdescent : baseEnd_1881013 < baseStart_1881013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881016 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 1, 5]
def baseStart_1881016 : Nat := 118140960795 + 1881016 * 2 ^ 59
def prefixEnd_1881016 : Nat := 4983230072969 + 3 ^ 40 * 1881016 * 2
def baseEnd_1881016 : Nat := 321955108932572583316457

theorem tailTrace_1881016 : CollatzResearch.WordTrace tailWord_1881016 prefixEnd_1881016 321955108932572583316457 := by
  unfold tailWord_1881016
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303144876703879400867451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45737526502271839201156601 34303144876703879400867451)
  ·
    refine ⟨51454717315055819101301177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34303144876703879400867451 51454717315055819101301177)
    ·
      refine ⟨38591037986291864325975883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51454717315055819101301177 38591037986291864325975883)
      ·
        refine ⟨57886556979437796488963825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38591037986291864325975883 57886556979437796488963825)
        ·
          refine ⟨43414917734578347366722869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57886556979437796488963825 43414917734578347366722869)
          ·
            refine ⟨4070148537616720065630269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43414917734578347366722869 4070148537616720065630269)
            ·
              refine ⟨1526305701606270024611351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4070148537616720065630269 1526305701606270024611351)
              ·
                refine ⟨2289458552409405036917027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526305701606270024611351 2289458552409405036917027)
                ·
                  refine ⟨3434187828614107555375541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289458552409405036917027 3434187828614107555375541)
                  ·
                    refine ⟨321955108932572583316457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3434187828614107555375541 321955108932572583316457)
                    ·
                      rfl

theorem cell23_1881016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_1881016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881016 prefixEnd_1881016 := by exact prefixLift 1881016
  have htrace : WordTrace (prefixWord ++ tailWord_1881016) baseStart_1881016 baseEnd_1881016 := by
    simpa [prefixWord, tailWord_1881016, baseEnd_1881016] using wordTrace_append hprefix tailTrace_1881016
  have hstable : (prefixWord ++ tailWord_1881016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881016).length < 2 ^ (prefixWord ++ tailWord_1881016).sum := by decide
  have hdescent : baseEnd_1881016 < baseStart_1881016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881039 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_1881039 : Nat := 118140960795 + 1881039 * 2 ^ 59
def prefixEnd_1881039 : Nat := 4983230072969 + 3 ^ 40 * 1881039 * 2
def baseEnd_1881039 : Nat := 965877136852771159961765

theorem tailTrace_1881039 : CollatzResearch.WordTrace tailWord_1881039 prefixEnd_1881039 965877136852771159961765 := by
  unfold tailWord_1881039
  simp only [CollatzResearch.WordTrace]
  refine ⟨68607128632324433729822171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45738085754882955819881447 68607128632324433729822171)
  ·
    refine ⟨102910692948486650594733257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68607128632324433729822171 102910692948486650594733257)
    ·
      refine ⟨77183019711364987946049943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102910692948486650594733257 77183019711364987946049943)
      ·
        refine ⟨115774529567047481919074915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77183019711364987946049943 115774529567047481919074915)
        ·
          refine ⟨173661794350571222878612373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115774529567047481919074915 173661794350571222878612373)
          ·
            refine ⟨8140396610183026072434955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173661794350571222878612373 8140396610183026072434955)
            ·
              refine ⟨12210594915274539108652433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140396610183026072434955 12210594915274539108652433)
              ·
                refine ⟨9157946186455904331489325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210594915274539108652433 9157946186455904331489325)
                ·
                  refine ⟨3434229819920964124308497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9157946186455904331489325 3434229819920964124308497)
                  ·
                    refine ⟨2575672364940723093231373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3434229819920964124308497 2575672364940723093231373)
                    ·
                      refine ⟨965877136852771159961765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575672364940723093231373 965877136852771159961765)
                      ·
                        rfl

theorem cell23_1881039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_1881039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881039 prefixEnd_1881039 := by exact prefixLift 1881039
  have htrace : WordTrace (prefixWord ++ tailWord_1881039) baseStart_1881039 baseEnd_1881039 := by
    simpa [prefixWord, tailWord_1881039, baseEnd_1881039] using wordTrace_append hprefix tailTrace_1881039
  have hstable : (prefixWord ++ tailWord_1881039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881039).length < 2 ^ (prefixWord ++ tailWord_1881039).sum := by decide
  have hdescent : baseEnd_1881039 < baseStart_1881039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881046 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1881046 : Nat := 118140960795 + 1881046 * 2 ^ 59
def prefixEnd_1881046 : Nat := 4983230072969 + 3 ^ 40 * 1881046 * 2
def baseEnd_1881046 : Nat := 321960243739117544191411

theorem tailTrace_1881046 : CollatzResearch.WordTrace tailWord_1881046 prefixEnd_1881046 321960243739117544191411 := by
  unfold tailWord_1881046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287961496456192120332937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45738255962199382616884661 4287961496456192120332937)
  ·
    refine ⟨3215971122342144090249703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4287961496456192120332937 3215971122342144090249703)
    ·
      refine ⟨4823956683513216135374555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215971122342144090249703 4823956683513216135374555)
      ·
        refine ⟨7235935025269824203061833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823956683513216135374555 7235935025269824203061833)
        ·
          refine ⟨5426951268952368152296375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235935025269824203061833 5426951268952368152296375)
          ·
            refine ⟨8140426903428552228444563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426951268952368152296375 8140426903428552228444563)
            ·
              refine ⟨12210640355142828342666845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140426903428552228444563 12210640355142828342666845)
              ·
                refine ⟨4578990133178560628500067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12210640355142828342666845 4578990133178560628500067)
                ·
                  refine ⟨6868485199767840942750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578990133178560628500067 6868485199767840942750101)
                  ·
                    refine ⟨321960243739117544191411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6868485199767840942750101 321960243739117544191411)
                    ·
                      rfl

theorem cell23_1881046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1881046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881046 prefixEnd_1881046 := by exact prefixLift 1881046
  have htrace : WordTrace (prefixWord ++ tailWord_1881046) baseStart_1881046 baseEnd_1881046 := by
    simpa [prefixWord, tailWord_1881046, baseEnd_1881046] using wordTrace_append hprefix tailTrace_1881046
  have hstable : (prefixWord ++ tailWord_1881046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881046).length < 2 ^ (prefixWord ++ tailWord_1881046).sum := by decide
  have hdescent : baseEnd_1881046 < baseStart_1881046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881049 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1881049 : Nat := 118140960795 + 1881049 * 2 ^ 59
def prefixEnd_1881049 : Nat := 4983230072969 + 3 ^ 40 * 1881049 * 2
def baseEnd_1881049 : Nat := 965882271659316120836719

theorem tailTrace_1881049 : CollatzResearch.WordTrace tailWord_1881049 prefixEnd_1881049 965882271659316120836719 := by
  unfold tailWord_1881049
  simp only [CollatzResearch.WordTrace]
  refine ⟨68607493362288205437686201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45738328908192136958457467 68607493362288205437686201)
  ·
    refine ⟨51455620021716154078264651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68607493362288205437686201 51455620021716154078264651)
    ·
      refine ⟨77183430032574231117396977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51455620021716154078264651 77183430032574231117396977)
      ·
        refine ⟨57887572524430673338047733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77183430032574231117396977 57887572524430673338047733)
        ·
          refine ⟨5426959924165375625441975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57887572524430673338047733 5426959924165375625441975)
          ·
            refine ⟨8140439886248063438162963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426959924165375625441975 8140439886248063438162963)
            ·
              refine ⟨12210659829372095157244445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140439886248063438162963 12210659829372095157244445)
              ·
                refine ⟨4578997436014535683966667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12210659829372095157244445 4578997436014535683966667)
                ·
                  refine ⟨6868496154021803525950001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578997436014535683966667 6868496154021803525950001)
                  ·
                    refine ⟨5151372115516352644462501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868496154021803525950001 5151372115516352644462501)
                    ·
                      refine ⟨965882271659316120836719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5151372115516352644462501 965882271659316120836719)
                      ·
                        rfl

theorem cell23_1881049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1881049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881049 prefixEnd_1881049 := by exact prefixLift 1881049
  have htrace : WordTrace (prefixWord ++ tailWord_1881049) baseStart_1881049 baseEnd_1881049 := by
    simpa [prefixWord, tailWord_1881049, baseEnd_1881049] using wordTrace_append hprefix tailTrace_1881049
  have hstable : (prefixWord ++ tailWord_1881049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881049).length < 2 ^ (prefixWord ++ tailWord_1881049).sum := by decide
  have hdescent : baseEnd_1881049 < baseStart_1881049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881053 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1881053 : Nat := 118140960795 + 1881053 * 2 ^ 59
def prefixEnd_1881053 : Nat := 4983230072969 + 3 ^ 40 * 1881053 * 2
def baseEnd_1881053 : Nat := 965884325581934105186701

theorem tailTrace_1881053 : CollatzResearch.WordTrace tailWord_1881053 prefixEnd_1881053 965884325581934105186701 := by
  unfold tailWord_1881053
  simp only [CollatzResearch.WordTrace]
  refine ⟨68607639254273714120831813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45738426169515809413887875 68607639254273714120831813)
  ·
    refine ⟨12863932360176321397655965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68607639254273714120831813 12863932360176321397655965)
    ·
      refine ⟨4823974635066120524120987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12863932360176321397655965 4823974635066120524120987)
      ·
        refine ⟨7235961952599180786181481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823974635066120524120987 7235961952599180786181481)
        ·
          refine ⟨5426971464449385589636111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235961952599180786181481 5426971464449385589636111)
          ·
            refine ⟨8140457196674078384454167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426971464449385589636111 8140457196674078384454167)
            ·
              refine ⟨12210685795011117576681251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140457196674078384454167 12210685795011117576681251)
              ·
                refine ⟨18316028692516676365021877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210685795011117576681251 18316028692516676365021877)
                ·
                  refine ⟨1717127689923438409220801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18316028692516676365021877 1717127689923438409220801)
                  ·
                    refine ⟨1287845767442578806915601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1717127689923438409220801 1287845767442578806915601)
                    ·
                      refine ⟨965884325581934105186701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287845767442578806915601 965884325581934105186701)
                      ·
                        rfl

theorem cell23_1881053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1881053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881053 prefixEnd_1881053 := by exact prefixLift 1881053
  have htrace : WordTrace (prefixWord ++ tailWord_1881053) baseStart_1881053 baseEnd_1881053 := by
    simpa [prefixWord, tailWord_1881053, baseEnd_1881053] using wordTrace_append hprefix tailTrace_1881053
  have hstable : (prefixWord ++ tailWord_1881053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881053).length < 2 ^ (prefixWord ++ tailWord_1881053).sum := by decide
  have hdescent : baseEnd_1881053 < baseStart_1881053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881059 : List Nat := [1, 1, 1, 6, 1, 1, 5, 7]
def baseStart_1881059 : Nat := 118140960795 + 1881059 * 2 ^ 59
def prefixEnd_1881059 : Nat := 4983230072969 + 3 ^ 40 * 1881059 * 2
def baseEnd_1881059 : Nat := 35773607646883743767099

theorem tailTrace_1881059 : CollatzResearch.WordTrace tailWord_1881059 prefixEnd_1881059 35773607646883743767099 := by
  unfold tailWord_1881059
  simp only [CollatzResearch.WordTrace]
  refine ⟨68607858092251977145550231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45738572061501318097033487 68607858092251977145550231)
  ·
    refine ⟨102911787138377965718325347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68607858092251977145550231 102911787138377965718325347)
    ·
      refine ⟨154367680707566948577488021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102911787138377965718325347 154367680707566948577488021)
      ·
        refine ⟨7235985033167200714569751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154367680707566948577488021 7235985033167200714569751)
        ·
          refine ⟨10853977549750801071854627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235985033167200714569751 10853977549750801071854627)
          ·
            refine ⟨16280966324626201607781941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853977549750801071854627 16280966324626201607781941)
            ·
              refine ⟨1526340592933706400729557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16280966324626201607781941 1526340592933706400729557)
              ·
                refine ⟨35773607646883743767099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1526340592933706400729557 35773607646883743767099)
                ·
                  rfl

theorem cell23_1881059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 7].length) (baseStart_1881059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881059 prefixEnd_1881059 := by exact prefixLift 1881059
  have htrace : WordTrace (prefixWord ++ tailWord_1881059) baseStart_1881059 baseEnd_1881059 := by
    simpa [prefixWord, tailWord_1881059, baseEnd_1881059] using wordTrace_append hprefix tailTrace_1881059
  have hstable : (prefixWord ++ tailWord_1881059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881059).length < 2 ^ (prefixWord ++ tailWord_1881059).sum := by decide
  have hdescent : baseEnd_1881059 < baseStart_1881059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881070 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_1881070 : Nat := 118140960795 + 1881070 * 2 ^ 59
def prefixEnd_1881070 : Nat := 4983230072969 + 3 ^ 40 * 1881070 * 2
def baseEnd_1881070 : Nat := 965893054753060538674123

theorem tailTrace_1881070 : CollatzResearch.WordTrace tailWord_1881070 prefixEnd_1881070 965893054753060538674123 := by
  unfold tailWord_1881070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576032411901515753025083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45738839530141417349467109 8576032411901515753025083)
  ·
    refine ⟨12864048617852273629537625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8576032411901515753025083 12864048617852273629537625)
    ·
      refine ⟨9648036463389205222153219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12864048617852273629537625 9648036463389205222153219)
      ·
        refine ⟨14472054695083807833229829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9648036463389205222153219 14472054695083807833229829)
        ·
          refine ⟨2713510255328213968730593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14472054695083807833229829 2713510255328213968730593)
          ·
            refine ⟨2035132691496160476547945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2713510255328213968730593 2035132691496160476547945)
            ·
              refine ⟨1526349518622120357410959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035132691496160476547945 1526349518622120357410959)
              ·
                refine ⟨2289524277933180536116439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526349518622120357410959 2289524277933180536116439)
                ·
                  refine ⟨3434286416899770804174659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289524277933180536116439 3434286416899770804174659)
                  ·
                    refine ⟨5151429625349656206261989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434286416899770804174659 5151429625349656206261989)
                    ·
                      refine ⟨965893054753060538674123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5151429625349656206261989 965893054753060538674123)
                      ·
                        rfl

theorem cell23_1881070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_1881070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881070 prefixEnd_1881070 := by exact prefixLift 1881070
  have htrace : WordTrace (prefixWord ++ tailWord_1881070) baseStart_1881070 baseEnd_1881070 := by
    simpa [prefixWord, tailWord_1881070, baseEnd_1881070] using wordTrace_append hprefix tailTrace_1881070
  have hstable : (prefixWord ++ tailWord_1881070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881070).length < 2 ^ (prefixWord ++ tailWord_1881070).sum := by decide
  have hdescent : baseEnd_1881070 < baseStart_1881070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881073 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_1881073 : Nat := 118140960795 + 1881073 * 2 ^ 59
def prefixEnd_1881073 : Nat := 4983230072969 + 3 ^ 40 * 1881073 * 2
def baseEnd_1881073 : Nat := 965894595195024026936609

theorem tailTrace_1881073 : CollatzResearch.WordTrace tailWord_1881073 prefixEnd_1881073 965894595195024026936609 := by
  unfold tailWord_1881073
  simp only [CollatzResearch.WordTrace]
  refine ⟨68608368714201257536559873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45738912476134171691039915 68608368714201257536559873)
  ·
    refine ⟨51456276535650943152419905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68608368714201257536559873 51456276535650943152419905)
    ·
      refine ⟨38592207401738207364314929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51456276535650943152419905 38592207401738207364314929)
      ·
        refine ⟨28944155551303655523236197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38592207401738207364314929 28944155551303655523236197)
        ·
          refine ⟨5427029165869435410606787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28944155551303655523236197 5427029165869435410606787)
          ·
            refine ⟨8140543748804153115910181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427029165869435410606787 8140543748804153115910181)
            ·
              refine ⟨1526351952900778709233159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8140543748804153115910181 1526351952900778709233159)
              ·
                refine ⟨2289527929351168063849739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526351952900778709233159 2289527929351168063849739)
                ·
                  refine ⟨3434291894026752095774609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289527929351168063849739 3434291894026752095774609)
                  ·
                    refine ⟨2575718920520064071830957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3434291894026752095774609 2575718920520064071830957)
                    ·
                      refine ⟨965894595195024026936609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2575718920520064071830957 965894595195024026936609)
                      ·
                        rfl

theorem cell23_1881073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_1881073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881073 prefixEnd_1881073 := by exact prefixLift 1881073
  have htrace : WordTrace (prefixWord ++ tailWord_1881073) baseStart_1881073 baseEnd_1881073 := by
    simpa [prefixWord, tailWord_1881073, baseEnd_1881073] using wordTrace_append hprefix tailTrace_1881073
  have hstable : (prefixWord ++ tailWord_1881073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881073).length < 2 ^ (prefixWord ++ tailWord_1881073).sum := by decide
  have hdescent : baseEnd_1881073 < baseStart_1881073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881143 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_1881143 : Nat := 118140960795 + 1881143 * 2 ^ 59
def prefixEnd_1881143 : Nat := 4983230072969 + 3 ^ 40 * 1881143 * 2
def baseEnd_1881143 : Nat := 965930538840838753061287

theorem tailTrace_1881143 : CollatzResearch.WordTrace tailWord_1881143 prefixEnd_1881143 965930538840838753061287 := by
  unfold tailWord_1881143
  simp only [CollatzResearch.WordTrace]
  refine ⟨68610921823947659491608083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45740614549298439661072055 68610921823947659491608083)
  ·
    refine ⟨102916382735921489237412125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68610921823947659491608083 102916382735921489237412125)
    ·
      refine ⟨38593643525970558464029547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102916382735921489237412125 38593643525970558464029547)
      ·
        refine ⟨57890465288955837696044321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38593643525970558464029547 57890465288955837696044321)
        ·
          refine ⟨43417848966716878272033241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57890465288955837696044321 43417848966716878272033241)
          ·
            refine ⟨32563386725037658704024931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43417848966716878272033241 32563386725037658704024931)
            ·
              refine ⟨48845080087556488056037397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32563386725037658704024931 48845080087556488056037397)
              ·
                refine ⟨2289613129104210377626753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48845080087556488056037397 2289613129104210377626753)
                ·
                  refine ⟨1717209846828157783220065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2289613129104210377626753 1717209846828157783220065)
                  ·
                    refine ⟨1287907385121118337415049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1717209846828157783220065 1287907385121118337415049)
                    ·
                      refine ⟨965930538840838753061287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287907385121118337415049 965930538840838753061287)
                      ·
                        rfl

theorem cell23_1881143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_1881143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881143 prefixEnd_1881143 := by exact prefixLift 1881143
  have htrace : WordTrace (prefixWord ++ tailWord_1881143) baseStart_1881143 baseEnd_1881143 := by
    simpa [prefixWord, tailWord_1881143, baseEnd_1881143] using wordTrace_append hprefix tailTrace_1881143
  have hstable : (prefixWord ++ tailWord_1881143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881143).length < 2 ^ (prefixWord ++ tailWord_1881143).sum := by decide
  have hdescent : baseEnd_1881143 < baseStart_1881143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881189 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1881189 : Nat := 118140960795 + 1881189 * 2 ^ 59
def prefixEnd_1881189 : Nat := 4983230072969 + 3 ^ 40 * 1881189 * 2
def baseEnd_1881189 : Nat := 965954158950945573086075

theorem tailTrace_1881189 : CollatzResearch.WordTrace tailWord_1881189 prefixEnd_1881189 965954158950945573086075 := by
  unfold tailWord_1881189
  simp only [CollatzResearch.WordTrace]
  refine ⟨68612599581781009347782621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45741733054520672898521747 68612599581781009347782621)
  ·
    refine ⟨25729724843167878505418483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68612599581781009347782621 25729724843167878505418483)
    ·
      refine ⟨38594587264751817758127725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25729724843167878505418483 38594587264751817758127725)
      ·
        refine ⟨14472970224281931659297897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38594587264751817758127725 14472970224281931659297897)
        ·
          refine ⟨10854727668211448744473423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14472970224281931659297897 10854727668211448744473423)
          ·
            refine ⟨16282091502317173116710135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10854727668211448744473423 16282091502317173116710135)
            ·
              refine ⟨24423137253475759675065203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16282091502317173116710135 24423137253475759675065203)
              ·
                refine ⟨36634705880213639512597805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24423137253475759675065203 36634705880213639512597805)
                ·
                  refine ⟨13738014705080114817224177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36634705880213639512597805 13738014705080114817224177)
                  ·
                    refine ⟨10303511028810086112918133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13738014705080114817224177 10303511028810086112918133)
                    ·
                      refine ⟨965954158950945573086075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10303511028810086112918133 965954158950945573086075)
                      ·
                        rfl

theorem cell23_1881189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1881189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881189 prefixEnd_1881189 := by exact prefixLift 1881189
  have htrace : WordTrace (prefixWord ++ tailWord_1881189) baseStart_1881189 baseEnd_1881189 := by
    simpa [prefixWord, tailWord_1881189, baseEnd_1881189] using wordTrace_append hprefix tailTrace_1881189
  have hstable : (prefixWord ++ tailWord_1881189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881189).length < 2 ^ (prefixWord ++ tailWord_1881189).sum := by decide
  have hdescent : baseEnd_1881189 < baseStart_1881189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881206 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1881206 : Nat := 118140960795 + 1881206 * 2 ^ 59
def prefixEnd_1881206 : Nat := 4983230072969 + 3 ^ 40 * 1881206 * 2
def baseEnd_1881206 : Nat := 965962888122072006573497

theorem tailTrace_1881206 : CollatzResearch.WordTrace tailWord_1881206 prefixEnd_1881206 965962888122072006573497 := by
  unfold tailWord_1881206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288326226419963828196967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45742146415146280834100981 4288326226419963828196967)
  ·
    refine ⟨6432489339629945742295451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288326226419963828196967 6432489339629945742295451)
    ·
      refine ⟨9648734009444918613443177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432489339629945742295451 9648734009444918613443177)
      ·
        refine ⟨7236550507083688960082383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9648734009444918613443177 7236550507083688960082383)
        ·
          refine ⟨10854825760625533440123575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236550507083688960082383 10854825760625533440123575)
          ·
            refine ⟨16282238640938300160185363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10854825760625533440123575 16282238640938300160185363)
            ·
              refine ⟨24423357961407450240278045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16282238640938300160185363 24423357961407450240278045)
              ·
                refine ⟨9158759235527793840104267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24423357961407450240278045 9158759235527793840104267)
                ·
                  refine ⟨13738138853291690760156401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158759235527793840104267 13738138853291690760156401)
                  ·
                    refine ⟨10303604139968768070117301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13738138853291690760156401 10303604139968768070117301)
                    ·
                      refine ⟨965962888122072006573497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10303604139968768070117301 965962888122072006573497)
                      ·
                        rfl

theorem cell23_1881206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1881206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881206 prefixEnd_1881206 := by exact prefixLift 1881206
  have htrace : WordTrace (prefixWord ++ tailWord_1881206) baseStart_1881206 baseEnd_1881206 := by
    simpa [prefixWord, tailWord_1881206, baseEnd_1881206] using wordTrace_append hprefix tailTrace_1881206
  have hstable : (prefixWord ++ tailWord_1881206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881206).length < 2 ^ (prefixWord ++ tailWord_1881206).sum := by decide
  have hdescent : baseEnd_1881206 < baseStart_1881206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881216 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2]
def baseStart_1881216 : Nat := 118140960795 + 1881216 * 2 ^ 59
def prefixEnd_1881216 : Nat := 4983230072969 + 3 ^ 40 * 1881216 * 2
def baseEnd_1881216 : Nat := 965968022928616967448451

theorem tailTrace_1881216 : CollatzResearch.WordTrace tailWord_1881216 prefixEnd_1881216 965968022928616967448451 := by
  unfold tailWord_1881216
  simp only [CollatzResearch.WordTrace]
  refine ⟨34306792176341596479507751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45742389568455461972677001 34306792176341596479507751)
  ·
    refine ⟨51460188264512394719261627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34306792176341596479507751 51460188264512394719261627)
    ·
      refine ⟨77190282396768592078892441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51460188264512394719261627 77190282396768592078892441)
      ·
        refine ⟨57892711797576444059169331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77190282396768592078892441 57892711797576444059169331)
        ·
          refine ⟨86839067696364666088753997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57892711797576444059169331 86839067696364666088753997)
          ·
            refine ⟨32564650386136749783282749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86839067696364666088753997 32564650386136749783282749)
            ·
              refine ⟨12211743894801281168731031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32564650386136749783282749 12211743894801281168731031)
              ·
                refine ⟨18317615842201921753096547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12211743894801281168731031 18317615842201921753096547)
                ·
                  refine ⟨27476423763302882629644821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18317615842201921753096547 27476423763302882629644821)
                  ·
                    refine ⟨1287957363904822623264601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27476423763302882629644821 1287957363904822623264601)
                    ·
                      refine ⟨965968022928616967448451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287957363904822623264601 965968022928616967448451)
                      ·
                        rfl

theorem cell23_1881216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_1881216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881216 prefixEnd_1881216 := by exact prefixLift 1881216
  have htrace : WordTrace (prefixWord ++ tailWord_1881216) baseStart_1881216 baseEnd_1881216 := by
    simpa [prefixWord, tailWord_1881216, baseEnd_1881216] using wordTrace_append hprefix tailTrace_1881216
  have hstable : (prefixWord ++ tailWord_1881216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881216).length < 2 ^ (prefixWord ++ tailWord_1881216).sum := by decide
  have hdescent : baseEnd_1881216 < baseStart_1881216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881273 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 6]
def baseStart_1881273 : Nat := 118140960795 + 1881273 * 2 ^ 59
def prefixEnd_1881273 : Nat := 4983230072969 + 3 ^ 40 * 1881273 * 2
def baseEnd_1881273 : Nat := 107333032369547027159521

theorem tailTrace_1881273 : CollatzResearch.WordTrace tailWord_1881273 prefixEnd_1881273 107333032369547027159521 := by
  unfold tailWord_1881273
  simp only [CollatzResearch.WordTrace]
  refine ⟨68615663313476691693840473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45743775542317794462560315 68615663313476691693840473)
  ·
    refine ⟨51461747485107518770380355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68615663313476691693840473 51461747485107518770380355)
    ·
      refine ⟨77192621227661278155570533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51461747485107518770380355 77192621227661278155570533)
      ·
        refine ⟨14473616480186489654169475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77192621227661278155570533 14473616480186489654169475)
        ·
          refine ⟨21710424720279734481254213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14473616480186489654169475 21710424720279734481254213)
          ·
            refine ⟨4070704635052450215235165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21710424720279734481254213 4070704635052450215235165)
            ·
              refine ⟨1526514238144668830713187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4070704635052450215235165 1526514238144668830713187)
              ·
                refine ⟨2289771357217003246069781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526514238144668830713187 2289771357217003246069781)
                ·
                  refine ⟨107333032369547027159521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2289771357217003246069781 107333032369547027159521)
                  ·
                    rfl

theorem cell23_1881273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 6].length) (baseStart_1881273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881273 prefixEnd_1881273 := by exact prefixLift 1881273
  have htrace : WordTrace (prefixWord ++ tailWord_1881273) baseStart_1881273 baseEnd_1881273 := by
    simpa [prefixWord, tailWord_1881273, baseEnd_1881273] using wordTrace_append hprefix tailTrace_1881273
  have hstable : (prefixWord ++ tailWord_1881273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881273).length < 2 ^ (prefixWord ++ tailWord_1881273).sum := by decide
  have hdescent : baseEnd_1881273 < baseStart_1881273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881279 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1881279 : Nat := 118140960795 + 1881279 * 2 ^ 59
def prefixEnd_1881279 : Nat := 4983230072969 + 3 ^ 40 * 1881279 * 2
def baseEnd_1881279 : Nat := 966000372209850220960661

theorem tailTrace_1881279 : CollatzResearch.WordTrace tailWord_1881279 prefixEnd_1881279 966000372209850220960661 := by
  unfold tailWord_1881279
  simp only [CollatzResearch.WordTrace]
  refine ⟨68615882151454954718558891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45743921434303303145705927 68615882151454954718558891)
  ·
    refine ⟨102923823227182432077838337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68615882151454954718558891 102923823227182432077838337)
    ·
      refine ⟨77192867420386824058378753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102923823227182432077838337 77192867420386824058378753)
      ·
        refine ⟨57894650565290118043784065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77192867420386824058378753 57894650565290118043784065)
        ·
          refine ⟨43420987923967588532838049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57894650565290118043784065 43420987923967588532838049)
          ·
            refine ⟨32565740942975691399628537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43420987923967588532838049 32565740942975691399628537)
            ·
              refine ⟨24424305707231768549721403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32565740942975691399628537 24424305707231768549721403)
              ·
                refine ⟨36636458560847652824582105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24424305707231768549721403 36636458560847652824582105)
                ·
                  refine ⟨27477343920635739618436579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36636458560847652824582105 27477343920635739618436579)
                  ·
                    refine ⟨41216015880953609427654869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27477343920635739618436579 41216015880953609427654869)
                    ·
                      refine ⟨966000372209850220960661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41216015880953609427654869 966000372209850220960661)
                      ·
                        rfl

theorem cell23_1881279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1881279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881279 prefixEnd_1881279 := by exact prefixLift 1881279
  have htrace : WordTrace (prefixWord ++ tailWord_1881279) baseStart_1881279 baseEnd_1881279 := by
    simpa [prefixWord, tailWord_1881279, baseEnd_1881279] using wordTrace_append hprefix tailTrace_1881279
  have hstable : (prefixWord ++ tailWord_1881279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881279).length < 2 ^ (prefixWord ++ tailWord_1881279).sum := by decide
  have hdescent : baseEnd_1881279 < baseStart_1881279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881294 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_1881294 : Nat := 118140960795 + 1881294 * 2 ^ 59
def prefixEnd_1881294 : Nat := 4983230072969 + 3 ^ 40 * 1881294 * 2
def baseEnd_1881294 : Nat := 322002691473222554091031

theorem tailTrace_1881294 : CollatzResearch.WordTrace tailWord_1881294 prefixEnd_1881294 322002691473222554091031 := by
  unfold tailWord_1881294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8577053655800076535044367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45744286164267074853569957 8577053655800076535044367)
  ·
    refine ⟨12865580483700114802566551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8577053655800076535044367 12865580483700114802566551)
    ·
      refine ⟨19298370725550172203849827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12865580483700114802566551 19298370725550172203849827)
      ·
        refine ⟨28947556088325258305774741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19298370725550172203849827 28947556088325258305774741)
        ·
          refine ⟨1356916691640246483083191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28947556088325258305774741 1356916691640246483083191)
          ·
            refine ⟨2035375037460369724624787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356916691640246483083191 2035375037460369724624787)
            ·
              refine ⟨3053062556190554586937181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035375037460369724624787 3053062556190554586937181)
              ·
                refine ⟨1144898458571457970101443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3053062556190554586937181 1144898458571457970101443)
                ·
                  refine ⟨1717347687857186955152165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144898458571457970101443 1717347687857186955152165)
                  ·
                    refine ⟨322002691473222554091031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717347687857186955152165 322002691473222554091031)
                    ·
                      rfl

theorem cell23_1881294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_1881294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881294 prefixEnd_1881294 := by exact prefixLift 1881294
  have htrace : WordTrace (prefixWord ++ tailWord_1881294) baseStart_1881294 baseEnd_1881294 := by
    simpa [prefixWord, tailWord_1881294, baseEnd_1881294] using wordTrace_append hprefix tailTrace_1881294
  have hstable : (prefixWord ++ tailWord_1881294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881294).length < 2 ^ (prefixWord ++ tailWord_1881294).sum := by decide
  have hdescent : baseEnd_1881294 < baseStart_1881294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881306 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1881306 : Nat := 118140960795 + 1881306 * 2 ^ 59
def prefixEnd_1881306 : Nat := 4983230072969 + 3 ^ 40 * 1881306 * 2
def baseEnd_1881306 : Nat := 966014236187521615323037

theorem tailTrace_1881306 : CollatzResearch.WordTrace tailWord_1881306 prefixEnd_1881306 966014236187521615323037 := by
  unfold tailWord_1881306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17154216730589284582447943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45744577948238092219861181 17154216730589284582447943)
  ·
    refine ⟨25731325095883926873671915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17154216730589284582447943 25731325095883926873671915)
    ·
      refine ⟨38596987643825890310507873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25731325095883926873671915 38596987643825890310507873)
      ·
        refine ⟨28947740732869417732880905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38596987643825890310507873 28947740732869417732880905)
        ·
          refine ⟨21710805549652063299660679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28947740732869417732880905 21710805549652063299660679)
          ·
            refine ⟨32566208324478094949491019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21710805549652063299660679 32566208324478094949491019)
            ·
              refine ⟨48849312486717142424236529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32566208324478094949491019 48849312486717142424236529)
              ·
                refine ⟨36636984365037856818177397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48849312486717142424236529 36636984365037856818177397)
                ·
                  refine ⟨3434717284222299076704131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36636984365037856818177397 3434717284222299076704131)
                  ·
                    refine ⟨5152075926333448615056197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434717284222299076704131 5152075926333448615056197)
                    ·
                      refine ⟨966014236187521615323037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5152075926333448615056197 966014236187521615323037)
                      ·
                        rfl

theorem cell23_1881306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1881306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881306 prefixEnd_1881306 := by exact prefixLift 1881306
  have htrace : WordTrace (prefixWord ++ tailWord_1881306) baseStart_1881306 baseEnd_1881306 := by
    simpa [prefixWord, tailWord_1881306, baseEnd_1881306] using wordTrace_append hprefix tailTrace_1881306
  have hstable : (prefixWord ++ tailWord_1881306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881306).length < 2 ^ (prefixWord ++ tailWord_1881306).sum := by decide
  have hdescent : baseEnd_1881306 < baseStart_1881306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881317 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1881317 : Nat := 118140960795 + 1881317 * 2 ^ 59
def prefixEnd_1881317 : Nat := 4983230072969 + 3 ^ 40 * 1881317 * 2
def baseEnd_1881317 : Nat := 966019884474721072285487

theorem tailTrace_1881317 : CollatzResearch.WordTrace tailWord_1881317 prefixEnd_1881317 966019884474721072285487 := by
  unfold tailWord_1881317
  simp only [CollatzResearch.WordTrace]
  refine ⟨68617268125317287208442205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45744845416878191472294803 68617268125317287208442205)
  ·
    refine ⟨25731475546993982703165827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68617268125317287208442205 25731475546993982703165827)
    ·
      refine ⟨38597213320490974054748741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25731475546993982703165827 38597213320490974054748741)
      ·
        refine ⟨7236977497592057635265389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38597213320490974054748741 7236977497592057635265389)
        ·
          refine ⟨2713866561597021613224521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7236977497592057635265389 2713866561597021613224521)
          ·
            refine ⟨2035399921197766209918391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2713866561597021613224521 2035399921197766209918391)
            ·
              refine ⟨3053099881796649314877587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035399921197766209918391 3053099881796649314877587)
              ·
                refine ⟨4579649822694973972316381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053099881796649314877587 4579649822694973972316381)
                ·
                  refine ⟨1717368683510615239618643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4579649822694973972316381 1717368683510615239618643)
                  ·
                    refine ⟨2576053025265922859427965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1717368683510615239618643 2576053025265922859427965)
                    ·
                      refine ⟨966019884474721072285487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2576053025265922859427965 966019884474721072285487)
                      ·
                        rfl

theorem cell23_1881317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1881317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881317 prefixEnd_1881317 := by exact prefixLift 1881317
  have htrace : WordTrace (prefixWord ++ tailWord_1881317) baseStart_1881317 baseEnd_1881317 := by
    simpa [prefixWord, tailWord_1881317, baseEnd_1881317] using wordTrace_append hprefix tailTrace_1881317
  have hstable : (prefixWord ++ tailWord_1881317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881317).length < 2 ^ (prefixWord ++ tailWord_1881317).sum := by decide
  have hdescent : baseEnd_1881317 < baseStart_1881317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881343 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_1881343 : Nat := 118140960795 + 1881343 * 2 ^ 59
def prefixEnd_1881343 : Nat := 4983230072969 + 3 ^ 40 * 1881343 * 2
def baseEnd_1881343 : Nat := 966033234971737970560367

theorem tailTrace_1881343 : CollatzResearch.WordTrace tailWord_1881343 prefixEnd_1881343 966033234971737970560367 := by
  unfold tailWord_1881343
  simp only [CollatzResearch.WordTrace]
  refine ⟨68618216423223093648888683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45745477615482062432592455 68618216423223093648888683)
  ·
    refine ⟨102927324634834640473333025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68618216423223093648888683 102927324634834640473333025)
    ·
      refine ⟨77195493476125980354999769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102927324634834640473333025 77195493476125980354999769)
      ·
        refine ⟨57896620107094485266249827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77195493476125980354999769 57896620107094485266249827)
        ·
          refine ⟨86844930160641727899374741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57896620107094485266249827 86844930160641727899374741)
          ·
            refine ⟨4070856101280080995283191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86844930160641727899374741 4070856101280080995283191)
            ·
              refine ⟨6106284151920121492924787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070856101280080995283191 6106284151920121492924787)
              ·
                refine ⟨9159426227880182239387181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106284151920121492924787 9159426227880182239387181)
                ·
                  refine ⟨3434784835455068339770193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9159426227880182239387181 3434784835455068339770193)
                  ·
                    refine ⟨2576088626591301254827645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3434784835455068339770193 2576088626591301254827645)
                    ·
                      refine ⟨966033234971737970560367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2576088626591301254827645 966033234971737970560367)
                      ·
                        rfl

theorem cell23_1881343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_1881343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881343 prefixEnd_1881343 := by exact prefixLift 1881343
  have htrace : WordTrace (prefixWord ++ tailWord_1881343) baseStart_1881343 baseEnd_1881343 := by
    simpa [prefixWord, tailWord_1881343, baseEnd_1881343] using wordTrace_append hprefix tailTrace_1881343
  have hstable : (prefixWord ++ tailWord_1881343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881343).length < 2 ^ (prefixWord ++ tailWord_1881343).sum := by decide
  have hdescent : baseEnd_1881343 < baseStart_1881343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881400 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_1881400 : Nat := 118140960795 + 1881400 * 2 ^ 59
def prefixEnd_1881400 : Nat := 4983230072969 + 3 ^ 40 * 1881400 * 2
def baseEnd_1881400 : Nat := 966062503369044247547605

theorem tailTrace_1881400 : CollatzResearch.WordTrace tailWord_1881400 prefixEnd_1881400 966062503369044247547605 := by
  unfold tailWord_1881400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34310147692008296191856827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45746863589344394922475769 34310147692008296191856827)
  ·
    refine ⟨51465221538012444287785241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34310147692008296191856827 51465221538012444287785241)
    ·
      refine ⟨38598916153509333215838931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51465221538012444287785241 38598916153509333215838931)
      ·
        refine ⟨57898374230263999823758397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38598916153509333215838931 57898374230263999823758397)
        ·
          refine ⟨21711890336348999933909399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57898374230263999823758397 21711890336348999933909399)
          ·
            refine ⟨32567835504523499900864099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21711890336348999933909399 32567835504523499900864099)
            ·
              refine ⟨48851753256785249851296149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32567835504523499900864099 48851753256785249851296149)
              ·
                refine ⟨2289925933911808586779507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48851753256785249851296149 2289925933911808586779507)
                ·
                  refine ⟨3434888900867712880169261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289925933911808586779507 3434888900867712880169261)
                  ·
                    refine ⟨1288083337825392330063473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434888900867712880169261 1288083337825392330063473)
                    ·
                      refine ⟨966062503369044247547605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288083337825392330063473 966062503369044247547605)
                      ·
                        rfl

theorem cell23_1881400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_1881400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881400 prefixEnd_1881400 := by exact prefixLift 1881400
  have htrace : WordTrace (prefixWord ++ tailWord_1881400) baseStart_1881400 baseEnd_1881400 := by
    simpa [prefixWord, tailWord_1881400, baseEnd_1881400] using wordTrace_append hprefix tailTrace_1881400
  have hstable : (prefixWord ++ tailWord_1881400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881400).length < 2 ^ (prefixWord ++ tailWord_1881400).sum := by decide
  have hdescent : baseEnd_1881400 < baseStart_1881400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881416 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1881416 : Nat := 118140960795 + 1881416 * 2 ^ 59
def prefixEnd_1881416 : Nat := 4983230072969 + 3 ^ 40 * 1881416 * 2
def baseEnd_1881416 : Nat := 966070719059516184947531

theorem tailTrace_1881416 : CollatzResearch.WordTrace tailWord_1881416 prefixEnd_1881416 966070719059516184947531 := by
  unfold tailWord_1881416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34310439475979313558148051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45747252634639084744197401 34310439475979313558148051)
  ·
    refine ⟨51465659213968970337222077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34310439475979313558148051 51465659213968970337222077)
    ·
      refine ⟨19299622205238363876458279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51465659213968970337222077 19299622205238363876458279)
      ·
        refine ⟨28949433307857545814687419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19299622205238363876458279 28949433307857545814687419)
        ·
          refine ⟨43424149961786318722031129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28949433307857545814687419 43424149961786318722031129)
          ·
            refine ⟨32568112471339739041523347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43424149961786318722031129 32568112471339739041523347)
            ·
              refine ⟨48852168707009608562285021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32568112471339739041523347 48852168707009608562285021)
              ·
                refine ⟨18319563265128603210856883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48852168707009608562285021 18319563265128603210856883)
                ·
                  refine ⟨27479344897692904816285325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18319563265128603210856883 27479344897692904816285325)
                  ·
                    refine ⟨10304754336634839306106997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27479344897692904816285325 10304754336634839306106997)
                    ·
                      refine ⟨966070719059516184947531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10304754336634839306106997 966070719059516184947531)
                      ·
                        rfl

theorem cell23_1881416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1881416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881416 prefixEnd_1881416 := by exact prefixLift 1881416
  have htrace : WordTrace (prefixWord ++ tailWord_1881416) baseStart_1881416 baseEnd_1881416 := by
    simpa [prefixWord, tailWord_1881416, baseEnd_1881416] using wordTrace_append hprefix tailTrace_1881416
  have hstable : (prefixWord ++ tailWord_1881416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881416).length < 2 ^ (prefixWord ++ tailWord_1881416).sum := by decide
  have hdescent : baseEnd_1881416 < baseStart_1881416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881417 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 1, 3, 2]
def baseStart_1881417 : Nat := 118140960795 + 1881417 * 2 ^ 59
def prefixEnd_1881417 : Nat := 4983230072969 + 3 ^ 40 * 1881417 * 2
def baseEnd_1881417 : Nat := 966071232540170681035027

theorem tailTrace_1881417 : CollatzResearch.WordTrace tailWord_1881417 prefixEnd_1881417 966071232540170681035027 := by
  unfold tailWord_1881417
  simp only [CollatzResearch.WordTrace]
  refine ⟨68620915424955004287082505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45747276949970002858055003 68620915424955004287082505)
  ·
    refine ⟨51465686568716253215311879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68620915424955004287082505 51465686568716253215311879)
    ·
      refine ⟨77198529853074379822967819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51465686568716253215311879 77198529853074379822967819)
      ·
        refine ⟨115797794779611569734451729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77198529853074379822967819 115797794779611569734451729)
        ·
          refine ⟨86848346084708677300838797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115797794779611569734451729 86848346084708677300838797)
          ·
            refine ⟨32568129781765753987814549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86848346084708677300838797 32568129781765753987814549)
            ·
              refine ⟨1526631083520269718178807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32568129781765753987814549 1526631083520269718178807)
              ·
                refine ⟨2289946625280404577268211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526631083520269718178807 2289946625280404577268211)
                ·
                  refine ⟨3434919937920606865902317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289946625280404577268211 3434919937920606865902317)
                  ·
                    refine ⟨1288094976720227574713369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434919937920606865902317 1288094976720227574713369)
                    ·
                      refine ⟨966071232540170681035027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288094976720227574713369 966071232540170681035027)
                      ·
                        rfl

theorem cell23_1881417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 3, 2].length) (baseStart_1881417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881417 prefixEnd_1881417 := by exact prefixLift 1881417
  have htrace : WordTrace (prefixWord ++ tailWord_1881417) baseStart_1881417 baseEnd_1881417 := by
    simpa [prefixWord, tailWord_1881417, baseEnd_1881417] using wordTrace_append hprefix tailTrace_1881417
  have hstable : (prefixWord ++ tailWord_1881417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881417).length < 2 ^ (prefixWord ++ tailWord_1881417).sum := by decide
  have hdescent : baseEnd_1881417 < baseStart_1881417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881443 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1881443 : Nat := 118140960795 + 1881443 * 2 ^ 59
def prefixEnd_1881443 : Nat := 4983230072969 + 3 ^ 40 * 1881443 * 2
def baseEnd_1881443 : Nat := 966084583037187579309907

theorem tailTrace_1881443 : CollatzResearch.WordTrace tailWord_1881443 prefixEnd_1881443 966084583037187579309907 := by
  unfold tailWord_1881443
  simp only [CollatzResearch.WordTrace]
  refine ⟨68621863722860810727528983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45747909148573873818352655 68621863722860810727528983)
  ·
    refine ⟨102932795584291216091293475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68621863722860810727528983 102932795584291216091293475)
    ·
      refine ⟨154399193376436824136940213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102932795584291216091293475 154399193376436824136940213)
      ·
        refine ⟨14474924379040952262838145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154399193376436824136940213 14474924379040952262838145)
        ·
          refine ⟨10856193284280714197128609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14474924379040952262838145 10856193284280714197128609)
          ·
            refine ⟨8142144963210535647846457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10856193284280714197128609 8142144963210535647846457)
            ·
              refine ⟨6106608722407901735884843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8142144963210535647846457 6106608722407901735884843)
              ·
                refine ⟨9159913083611852603827265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106608722407901735884843 9159913083611852603827265)
                ·
                  refine ⟨6869934812708889452870449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9159913083611852603827265 6869934812708889452870449)
                  ·
                    refine ⟨5152451109531667089652837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6869934812708889452870449 5152451109531667089652837)
                    ·
                      refine ⟨966084583037187579309907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5152451109531667089652837 966084583037187579309907)
                      ·
                        rfl

theorem cell23_1881443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1881443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881443 prefixEnd_1881443 := by exact prefixLift 1881443
  have htrace : WordTrace (prefixWord ++ tailWord_1881443) baseStart_1881443 baseEnd_1881443 := by
    simpa [prefixWord, tailWord_1881443, baseEnd_1881443] using wordTrace_append hprefix tailTrace_1881443
  have hstable : (prefixWord ++ tailWord_1881443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881443).length < 2 ^ (prefixWord ++ tailWord_1881443).sum := by decide
  have hdescent : baseEnd_1881443 < baseStart_1881443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881453 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1881453 : Nat := 118140960795 + 1881453 * 2 ^ 59
def prefixEnd_1881453 : Nat := 4983230072969 + 3 ^ 40 * 1881453 * 2
def baseEnd_1881453 : Nat := 107343301982636948909429

theorem tailTrace_1881453 : CollatzResearch.WordTrace tailWord_1881453 prefixEnd_1881453 107343301982636948909429 := by
  unfold tailWord_1881453
  simp only [CollatzResearch.WordTrace]
  refine ⟨68622228452824582435393013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45748152301883054956928675 68622228452824582435393013)
  ·
    refine ⟨6433333917452304603318095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68622228452824582435393013 6433333917452304603318095)
    ·
      refine ⟨9650000876178456904977143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433333917452304603318095 9650000876178456904977143)
      ·
        refine ⟨14475001314267685357465715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650000876178456904977143 14475001314267685357465715)
        ·
          refine ⟨21712501971401528036198573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475001314267685357465715 21712501971401528036198573)
          ·
            refine ⟨8142188239275573013574465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21712501971401528036198573 8142188239275573013574465)
            ·
              refine ⟨6106641179456679760180849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8142188239275573013574465 6106641179456679760180849)
              ·
                refine ⟨4579980884592509820135637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6106641179456679760180849 4579980884592509820135637)
                ·
                  refine ⟨107343301982636948909429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4579980884592509820135637 107343301982636948909429)
                  ·
                    rfl

theorem cell23_1881453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1881453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881453 prefixEnd_1881453 := by exact prefixLift 1881453
  have htrace : WordTrace (prefixWord ++ tailWord_1881453) baseStart_1881453 baseEnd_1881453 := by
    simpa [prefixWord, tailWord_1881453, baseEnd_1881453] using wordTrace_append hprefix tailTrace_1881453
  have hstable : (prefixWord ++ tailWord_1881453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881453).length < 2 ^ (prefixWord ++ tailWord_1881453).sum := by decide
  have hdescent : baseEnd_1881453 < baseStart_1881453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881483 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 2, 5]
def baseStart_1881483 : Nat := 118140960795 + 1881483 * 2 ^ 59
def prefixEnd_1881483 : Nat := 4983230072969 + 3 ^ 40 * 1881483 * 2
def baseEnd_1881483 : Nat := 322035040754455807603241

theorem tailTrace_1881483 : CollatzResearch.WordTrace tailWord_1881483 prefixEnd_1881483 322035040754455807603241 := by
  unfold tailWord_1881483
  simp only [CollatzResearch.WordTrace]
  refine ⟨68623322642715897558985103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45748881761810598372656735 68623322642715897558985103)
  ·
    refine ⟨102934983964073846338477655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68623322642715897558985103 102934983964073846338477655)
    ·
      refine ⟨154402475946110769507716483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102934983964073846338477655 154402475946110769507716483)
      ·
        refine ⟨231603713919166154261574725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154402475946110769507716483 231603713919166154261574725)
        ·
          refine ⟨43425696359843653924045261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231603713919166154261574725 43425696359843653924045261)
          ·
            refine ⟨16284636134941370221516973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43425696359843653924045261 16284636134941370221516973)
            ·
              refine ⟨6106738550603013833068865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16284636134941370221516973 6106738550603013833068865)
              ·
                refine ⟨4580053912952260374801649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6106738550603013833068865 4580053912952260374801649)
                ·
                  refine ⟨3435040434714195281101237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580053912952260374801649 3435040434714195281101237)
                  ·
                    refine ⟨322035040754455807603241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3435040434714195281101237 322035040754455807603241)
                    ·
                      rfl

theorem cell23_1881483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 5].length) (baseStart_1881483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881483 prefixEnd_1881483 := by exact prefixLift 1881483
  have htrace : WordTrace (prefixWord ++ tailWord_1881483) baseStart_1881483 baseEnd_1881483 := by
    simpa [prefixWord, tailWord_1881483, baseEnd_1881483] using wordTrace_append hprefix tailTrace_1881483
  have hstable : (prefixWord ++ tailWord_1881483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881483).length < 2 ^ (prefixWord ++ tailWord_1881483).sum := by decide
  have hdescent : baseEnd_1881483 < baseStart_1881483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881517 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1881517 : Nat := 118140960795 + 1881517 * 2 ^ 59
def prefixEnd_1881517 : Nat := 4983230072969 + 3 ^ 40 * 1881517 * 2
def baseEnd_1881517 : Nat := 322040860201873429928189

theorem tailTrace_1881517 : CollatzResearch.WordTrace tailWord_1881517 prefixEnd_1881517 322040860201873429928189 := by
  unfold tailWord_1881517
  simp only [CollatzResearch.WordTrace]
  refine ⟨68624562724592721365722805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45749708483061814243815203 68624562724592721365722805)
  ·
    refine ⟨6433552755430567628036513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68624562724592721365722805 6433552755430567628036513)
    ·
      refine ⟨4825164566572925721027385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6433552755430567628036513 4825164566572925721027385)
      ·
        refine ⟨3618873424929694290770539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4825164566572925721027385 3618873424929694290770539)
        ·
          refine ⟨5428310137394541436155809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618873424929694290770539 5428310137394541436155809)
          ·
            refine ⟨4071232603045906077116857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5428310137394541436155809 4071232603045906077116857)
            ·
              refine ⟨3053424452284429557837643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071232603045906077116857 3053424452284429557837643)
              ·
                refine ⟨4580136678426644336756465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053424452284429557837643 4580136678426644336756465)
                ·
                  refine ⟨3435102508819983252567349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580136678426644336756465 3435102508819983252567349)
                  ·
                    refine ⟨322040860201873429928189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3435102508819983252567349 322040860201873429928189)
                    ·
                      rfl

theorem cell23_1881517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1881517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881517 prefixEnd_1881517 := by exact prefixLift 1881517
  have htrace : WordTrace (prefixWord ++ tailWord_1881517) baseStart_1881517 baseEnd_1881517 := by
    simpa [prefixWord, tailWord_1881517, baseEnd_1881517] using wordTrace_append hprefix tailTrace_1881517
  have hstable : (prefixWord ++ tailWord_1881517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881517).length < 2 ^ (prefixWord ++ tailWord_1881517).sum := by decide
  have hdescent : baseEnd_1881517 < baseStart_1881517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881523 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3]
def baseStart_1881523 : Nat := 118140960795 + 1881523 * 2 ^ 59
def prefixEnd_1881523 : Nat := 4983230072969 + 3 ^ 40 * 1881523 * 2
def baseEnd_1881523 : Nat := 966125661489547266309539

theorem tailTrace_1881523 : CollatzResearch.WordTrace tailWord_1881523 prefixEnd_1881523 966125661489547266309539 := by
  unfold tailWord_1881523
  simp only [CollatzResearch.WordTrace]
  refine ⟨68624781562570984390441223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45749854375047322926960815 68624781562570984390441223)
  ·
    refine ⟨102937172343856476585661835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68624781562570984390441223 102937172343856476585661835)
    ·
      refine ⟨154405758515784714878492753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102937172343856476585661835 154405758515784714878492753)
      ·
        refine ⟨115804318886838536158869565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154405758515784714878492753 115804318886838536158869565)
        ·
          refine ⟨43426619582564451059576087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115804318886838536158869565 43426619582564451059576087)
          ·
            refine ⟨65139929373846676589364131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43426619582564451059576087 65139929373846676589364131)
            ·
              refine ⟨97709894060770014884046197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65139929373846676589364131 97709894060770014884046197)
              ·
                refine ⟨9160302568197188895379331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97709894060770014884046197 9160302568197188895379331)
                ·
                  refine ⟨13740453852295783343068997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9160302568197188895379331 13740453852295783343068997)
                  ·
                    refine ⟨2576335097305459376825437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13740453852295783343068997 2576335097305459376825437)
                    ·
                      refine ⟨966125661489547266309539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2576335097305459376825437 966125661489547266309539)
                      ·
                        rfl

theorem cell23_1881523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_1881523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881523 prefixEnd_1881523 := by exact prefixLift 1881523
  have htrace : WordTrace (prefixWord ++ tailWord_1881523) baseStart_1881523 baseEnd_1881523 := by
    simpa [prefixWord, tailWord_1881523, baseEnd_1881523] using wordTrace_append hprefix tailTrace_1881523
  have hstable : (prefixWord ++ tailWord_1881523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881523).length < 2 ^ (prefixWord ++ tailWord_1881523).sum := by decide
  have hdescent : baseEnd_1881523 < baseStart_1881523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881533 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1881533 : Nat := 118140960795 + 1881533 * 2 ^ 59
def prefixEnd_1881533 : Nat := 4983230072969 + 3 ^ 40 * 1881533 * 2
def baseEnd_1881533 : Nat := 966130796296092227184493

theorem tailTrace_1881533 : CollatzResearch.WordTrace tailWord_1881533 prefixEnd_1881533 966130796296092227184493 := by
  unfold tailWord_1881533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68625146292534756098305253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45750097528356504065536835 68625146292534756098305253)
  ·
    refine ⟨12867214929850266768432235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68625146292534756098305253 12867214929850266768432235)
    ·
      refine ⟨19300822394775400152648353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12867214929850266768432235 19300822394775400152648353)
      ·
        refine ⟨14475616796081550114486265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19300822394775400152648353 14475616796081550114486265)
        ·
          refine ⟨10856712597061162585864699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14475616796081550114486265 10856712597061162585864699)
          ·
            refine ⟨16285068895591743878797049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10856712597061162585864699 16285068895591743878797049)
            ·
              refine ⟨12213801671693807909097787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16285068895591743878797049 12213801671693807909097787)
              ·
                refine ⟨18320702507540711863646681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12213801671693807909097787 18320702507540711863646681)
                ·
                  refine ⟨13740526880655533897735011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18320702507540711863646681 13740526880655533897735011)
                  ·
                    refine ⟨20610790320983300846602517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13740526880655533897735011 20610790320983300846602517)
                    ·
                      refine ⟨966130796296092227184493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20610790320983300846602517 966130796296092227184493)
                      ·
                        rfl

theorem cell23_1881533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1881533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881533 prefixEnd_1881533 := by exact prefixLift 1881533
  have htrace : WordTrace (prefixWord ++ tailWord_1881533) baseStart_1881533 baseEnd_1881533 := by
    simpa [prefixWord, tailWord_1881533, baseEnd_1881533] using wordTrace_append hprefix tailTrace_1881533
  have hstable : (prefixWord ++ tailWord_1881533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881533).length < 2 ^ (prefixWord ++ tailWord_1881533).sum := by decide
  have hdescent : baseEnd_1881533 < baseStart_1881533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881538 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1881538 : Nat := 118140960795 + 1881538 * 2 ^ 59
def prefixEnd_1881538 : Nat := 4983230072969 + 3 ^ 40 * 1881538 * 2
def baseEnd_1881538 : Nat := 107348151522151634180219

theorem tailTrace_1881538 : CollatzResearch.WordTrace tailWord_1881538 prefixEnd_1881538 107348151522151634180219 := by
  unfold tailWord_1881538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17156332164379160488059317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45750219105011094634824845 17156332164379160488059317)
  ·
    refine ⟨1608406140410546295755561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17156332164379160488059317 1608406140410546295755561)
    ·
      refine ⟨1206304605307909721816671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1608406140410546295755561 1206304605307909721816671)
      ·
        refine ⟨1809456907961864582725007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206304605307909721816671 1809456907961864582725007)
        ·
          refine ⟨2714185361942796874087511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809456907961864582725007 2714185361942796874087511)
          ·
            refine ⟨4071278042914195311131267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714185361942796874087511 4071278042914195311131267)
            ·
              refine ⟨6106917064371292966696901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071278042914195311131267 6106917064371292966696901)
              ·
                refine ⟨1145046949569617431255669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6106917064371292966696901 1145046949569617431255669)
                ·
                  refine ⟨107348151522151634180219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1145046949569617431255669 107348151522151634180219)
                  ·
                    rfl

theorem cell23_1881538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1881538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881538 prefixEnd_1881538 := by exact prefixLift 1881538
  have htrace : WordTrace (prefixWord ++ tailWord_1881538) baseStart_1881538 baseEnd_1881538 := by
    simpa [prefixWord, tailWord_1881538, baseEnd_1881538] using wordTrace_append hprefix tailTrace_1881538
  have hstable : (prefixWord ++ tailWord_1881538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881538).length < 2 ^ (prefixWord ++ tailWord_1881538).sum := by decide
  have hdescent : baseEnd_1881538 < baseStart_1881538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881553 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_1881553 : Nat := 118140960795 + 1881553 * 2 ^ 59
def prefixEnd_1881553 : Nat := 4983230072969 + 3 ^ 40 * 1881553 * 2
def baseEnd_1881553 : Nat := 966141065909182148934401

theorem tailTrace_1881553 : CollatzResearch.WordTrace tailWord_1881553 prefixEnd_1881553 966141065909182148934401 := by
  unfold tailWord_1881553
  simp only [CollatzResearch.WordTrace]
  refine ⟨68625875752462299514033313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45750583834974866342688875 68625875752462299514033313)
  ·
    refine ⟨51469406814346724635524985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68625875752462299514033313 51469406814346724635524985)
    ·
      refine ⟨38602055110760043476643739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51469406814346724635524985 38602055110760043476643739)
      ·
        refine ⟨57903082666140065214965609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38602055110760043476643739 57903082666140065214965609)
        ·
          refine ⟨43427311999605048911224207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57903082666140065214965609 43427311999605048911224207)
          ·
            refine ⟨65140967999407573366836311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43427311999605048911224207 65140967999407573366836311)
            ·
              refine ⟨97711451999111360050254467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65140967999407573366836311 97711451999111360050254467)
              ·
                refine ⟨146567177998667040075381701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97711451999111360050254467 146567177998667040075381701)
                ·
                  refine ⟨27481345874750070014134069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146567177998667040075381701 27481345874750070014134069)
                  ·
                    refine ⟨2576376175757819063825069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27481345874750070014134069 2576376175757819063825069)
                    ·
                      refine ⟨966141065909182148934401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2576376175757819063825069 966141065909182148934401)
                      ·
                        rfl

theorem cell23_1881553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_1881553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881553 prefixEnd_1881553 := by exact prefixLift 1881553
  have htrace : WordTrace (prefixWord ++ tailWord_1881553) baseStart_1881553 baseEnd_1881553 := by
    simpa [prefixWord, tailWord_1881553, baseEnd_1881553] using wordTrace_append hprefix tailTrace_1881553
  have hstable : (prefixWord ++ tailWord_1881553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881553).length < 2 ^ (prefixWord ++ tailWord_1881553).sum := by decide
  have hdescent : baseEnd_1881553 < baseStart_1881553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881581 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1881581 : Nat := 118140960795 + 1881581 * 2 ^ 59
def prefixEnd_1881581 : Nat := 4983230072969 + 3 ^ 40 * 1881581 * 2
def baseEnd_1881581 : Nat := 322051814455836013128091

theorem tailTrace_1881581 : CollatzResearch.WordTrace tailWord_1881581 prefixEnd_1881581 322051814455836013128091 := by
  unfold tailWord_1881581
  simp only [CollatzResearch.WordTrace]
  refine ⟨68626896996360860296052597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45751264664240573530701731 68626896996360860296052597)
  ·
    refine ⟨6433771593408830652754931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68626896996360860296052597 6433771593408830652754931)
    ·
      refine ⟨9650657390113245979132397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433771593408830652754931 9650657390113245979132397)
      ·
        refine ⟨3618996521292467242174649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9650657390113245979132397 3618996521292467242174649)
        ·
          refine ⟨2714247390969350431630987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3618996521292467242174649 2714247390969350431630987)
          ·
            refine ⟨4071371086454025647446481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714247390969350431630987 4071371086454025647446481)
            ·
              refine ⟨3053528314840519235584861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071371086454025647446481 3053528314840519235584861)
              ·
                refine ⟨1145073118065194713344323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3053528314840519235584861 1145073118065194713344323)
                ·
                  refine ⟨1717609677097792070016485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145073118065194713344323 1717609677097792070016485)
                  ·
                    refine ⟨322051814455836013128091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717609677097792070016485 322051814455836013128091)
                    ·
                      rfl

theorem cell23_1881581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1881581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881581 prefixEnd_1881581 := by exact prefixLift 1881581
  have htrace : WordTrace (prefixWord ++ tailWord_1881581) baseStart_1881581 baseEnd_1881581 := by
    simpa [prefixWord, tailWord_1881581, baseEnd_1881581] using wordTrace_append hprefix tailTrace_1881581
  have hstable : (prefixWord ++ tailWord_1881581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881581).length < 2 ^ (prefixWord ++ tailWord_1881581).sum := by decide
  have hdescent : baseEnd_1881581 < baseStart_1881581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881671 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 2, 4]
def baseStart_1881671 : Nat := 118140960795 + 1881671 * 2 ^ 59
def prefixEnd_1881671 : Nat := 4983230072969 + 3 ^ 40 * 1881671 * 2
def baseEnd_1881671 : Nat := 322067218875470895752953

theorem tailTrace_1881671 : CollatzResearch.WordTrace tailWord_1881671 prefixEnd_1881671 322067218875470895752953 := by
  unfold tailWord_1881671
  simp only [CollatzResearch.WordTrace]
  refine ⟨68630179566034805666828867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45753453044023203777885911 68630179566034805666828867)
  ·
    refine ⟨102945269349052208500243301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68630179566034805666828867 102945269349052208500243301)
    ·
      refine ⟨19302238002947289093795619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102945269349052208500243301 19302238002947289093795619)
      ·
        refine ⟨28953357004420933640693429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302238002947289093795619 28953357004420933640693429)
        ·
          refine ⟨2714377219164462528815009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28953357004420933640693429 2714377219164462528815009)
          ·
            refine ⟨2035782914373346896611257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714377219164462528815009 2035782914373346896611257)
            ·
              refine ⟨1526837185780010172458443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035782914373346896611257 1526837185780010172458443)
              ·
                refine ⟨2290255778670015258687665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526837185780010172458443 2290255778670015258687665)
                ·
                  refine ⟨1717691834002511444015749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2290255778670015258687665 1717691834002511444015749)
                  ·
                    refine ⟨322067218875470895752953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717691834002511444015749 322067218875470895752953)
                    ·
                      rfl

theorem cell23_1881671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_1881671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881671 prefixEnd_1881671 := by exact prefixLift 1881671
  have htrace : WordTrace (prefixWord ++ tailWord_1881671) baseStart_1881671 baseEnd_1881671 := by
    simpa [prefixWord, tailWord_1881671, baseEnd_1881671] using wordTrace_append hprefix tailTrace_1881671
  have hstable : (prefixWord ++ tailWord_1881671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881671).length < 2 ^ (prefixWord ++ tailWord_1881671).sum := by decide
  have hdescent : baseEnd_1881671 < baseStart_1881671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881717 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1881717 : Nat := 118140960795 + 1881717 * 2 ^ 59
def prefixEnd_1881717 : Nat := 4983230072969 + 3 ^ 40 * 1881717 * 2
def baseEnd_1881717 : Nat := 966225276736519507283647

theorem tailTrace_1881717 : CollatzResearch.WordTrace tailWord_1881717 prefixEnd_1881717 966225276736519507283647 := by
  unfold tailWord_1881717
  simp only [CollatzResearch.WordTrace]
  refine ⟨68631857323868155523003405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45754571549245437015335603 68631857323868155523003405)
  ·
    refine ⟨25736946496450558321126277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68631857323868155523003405 25736946496450558321126277)
    ·
      refine ⟨4825677468084479685211177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25736946496450558321126277 4825677468084479685211177)
      ·
        refine ⟨3619258101063359763908383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4825677468084479685211177 3619258101063359763908383)
        ·
          refine ⟨5428887151595039645862575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619258101063359763908383 5428887151595039645862575)
          ·
            refine ⟨8143330727392559468793863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428887151595039645862575 8143330727392559468793863)
            ·
              refine ⟨12214996091088839203190795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8143330727392559468793863 12214996091088839203190795)
              ·
                refine ⟨18322494136633258804786193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12214996091088839203190795 18322494136633258804786193)
                ·
                  refine ⟨13741870602474944103589645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18322494136633258804786193 13741870602474944103589645)
                  ·
                    refine ⟨5153201475928104038846117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13741870602474944103589645 5153201475928104038846117)
                    ·
                      refine ⟨966225276736519507283647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5153201475928104038846117 966225276736519507283647)
                      ·
                        rfl

theorem cell23_1881717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1881717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881717 prefixEnd_1881717 := by exact prefixLift 1881717
  have htrace : WordTrace (prefixWord ++ tailWord_1881717) baseStart_1881717 baseEnd_1881717 := by
    simpa [prefixWord, tailWord_1881717, baseEnd_1881717] using wordTrace_append hprefix tailTrace_1881717
  have hstable : (prefixWord ++ tailWord_1881717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881717).length < 2 ^ (prefixWord ++ tailWord_1881717).sum := by decide
  have hdescent : baseEnd_1881717 < baseStart_1881717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881740 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 7]
def baseStart_1881740 : Nat := 118140960795 + 1881740 * 2 ^ 59
def prefixEnd_1881740 : Nat := 4983230072969 + 3 ^ 40 * 1881740 * 2
def baseEnd_1881740 : Nat := 107359676310174768588449

theorem tailTrace_1881740 : CollatzResearch.WordTrace tailWord_1881740 prefixEnd_1881740 107359676310174768588449 := by
  unfold tailWord_1881740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34316348101392415225545337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45755130801856553634060449 34316348101392415225545337)
  ·
    refine ⟨25737261076044311419159003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34316348101392415225545337 25737261076044311419159003)
    ·
      refine ⟨38605891614066467128738505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25737261076044311419159003 38605891614066467128738505)
      ·
        refine ⟨28954418710549850346553879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38605891614066467128738505 28954418710549850346553879)
        ·
          refine ⟨43431628065824775519830819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28954418710549850346553879 43431628065824775519830819)
          ·
            refine ⟨65147442098737163279746229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43431628065824775519830819 65147442098737163279746229)
            ·
              refine ⟨6107572696756609057476209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65147442098737163279746229 6107572696756609057476209)
              ·
                refine ⟨4580679522567456793107157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6107572696756609057476209 4580679522567456793107157)
                ·
                  refine ⟨107359676310174768588449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4580679522567456793107157 107359676310174768588449)
                  ·
                    rfl

theorem cell23_1881740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_1881740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881740 prefixEnd_1881740 := by exact prefixLift 1881740
  have htrace : WordTrace (prefixWord ++ tailWord_1881740) baseStart_1881740 baseEnd_1881740 := by
    simpa [prefixWord, tailWord_1881740, baseEnd_1881740] using wordTrace_append hprefix tailTrace_1881740
  have hstable : (prefixWord ++ tailWord_1881740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881740).length < 2 ^ (prefixWord ++ tailWord_1881740).sum := by decide
  have hdescent : baseEnd_1881740 < baseStart_1881740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881800 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1881800 : Nat := 118140960795 + 1881800 * 2 ^ 59
def prefixEnd_1881800 : Nat := 4983230072969 + 3 ^ 40 * 1881800 * 2
def baseEnd_1881800 : Nat := 322089298543614227515255

theorem tailTrace_1881800 : CollatzResearch.WordTrace tailWord_1881800 prefixEnd_1881800 322089298543614227515255 := by
  unfold tailWord_1881800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34317442291283730349137427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45756589721711640465516569 34317442291283730349137427)
  ·
    refine ⟨51476163436925595523706141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34317442291283730349137427 51476163436925595523706141)
    ·
      refine ⟨19303561288847098321389803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51476163436925595523706141 19303561288847098321389803)
      ·
        refine ⟨28955341933270647482084705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19303561288847098321389803 28955341933270647482084705)
        ·
          refine ⟨21716506449952985611563529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28955341933270647482084705 21716506449952985611563529)
          ·
            refine ⟨16287379837464739208672647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21716506449952985611563529 16287379837464739208672647)
            ·
              refine ⟨24431069756197108813008971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16287379837464739208672647 24431069756197108813008971)
              ·
                refine ⟨36646604634295663219513457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24431069756197108813008971 36646604634295663219513457)
                ·
                  refine ⟨27484953475721747414635093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36646604634295663219513457 27484953475721747414635093)
                  ·
                    refine ⟨322089298543614227515255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27484953475721747414635093 322089298543614227515255)
                    ·
                      rfl

theorem cell23_1881800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1881800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881800 prefixEnd_1881800 := by exact prefixLift 1881800
  have htrace : WordTrace (prefixWord ++ tailWord_1881800) baseStart_1881800 baseEnd_1881800 := by
    simpa [prefixWord, tailWord_1881800, baseEnd_1881800] using wordTrace_append hprefix tailTrace_1881800
  have hstable : (prefixWord ++ tailWord_1881800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881800).length < 2 ^ (prefixWord ++ tailWord_1881800).sum := by decide
  have hdescent : baseEnd_1881800 < baseStart_1881800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881807 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 6, 2]
def baseStart_1881807 : Nat := 118140960795 + 1881807 * 2 ^ 59
def prefixEnd_1881807 : Nat := 4983230072969 + 3 ^ 40 * 1881807 * 2
def baseEnd_1881807 : Nat := 966271489995424155158233

theorem tailTrace_1881807 : CollatzResearch.WordTrace tailWord_1881807 prefixEnd_1881807 966271489995424155158233 := by
  unfold tailWord_1881807
  simp only [CollatzResearch.WordTrace]
  refine ⟨68635139893542100893779675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45756759929028067262519783 68635139893542100893779675)
  ·
    refine ⟨102952709840313151340669513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68635139893542100893779675 102952709840313151340669513)
    ·
      refine ⟨77214532380234863505502135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102952709840313151340669513 77214532380234863505502135)
      ·
        refine ⟨115821798570352295258253203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77214532380234863505502135 115821798570352295258253203)
        ·
          refine ⟨173732697855528442887379805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115821798570352295258253203 173732697855528442887379805)
          ·
            refine ⟨65149761695823166082767427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173732697855528442887379805 65149761695823166082767427)
            ·
              refine ⟨97724642543734749124151141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65149761695823166082767427 97724642543734749124151141)
              ·
                refine ⟨18323370476950265460778339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97724642543734749124151141 18323370476950265460778339)
                ·
                  refine ⟨27485055715425398191167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18323370476950265460778339 27485055715425398191167509)
                  ·
                    refine ⟨1288361986660565540210977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27485055715425398191167509 1288361986660565540210977)
                    ·
                      refine ⟨966271489995424155158233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288361986660565540210977 966271489995424155158233)
                      ·
                        rfl

theorem cell23_1881807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6, 2].length) (baseStart_1881807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881807 prefixEnd_1881807 := by exact prefixLift 1881807
  have htrace : WordTrace (prefixWord ++ tailWord_1881807) baseStart_1881807 baseEnd_1881807 := by
    simpa [prefixWord, tailWord_1881807, baseEnd_1881807] using wordTrace_append hprefix tailTrace_1881807
  have hstable : (prefixWord ++ tailWord_1881807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881807).length < 2 ^ (prefixWord ++ tailWord_1881807).sum := by decide
  have hdescent : baseEnd_1881807 < baseStart_1881807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881821 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1881821 : Nat := 118140960795 + 1881821 * 2 ^ 59
def prefixEnd_1881821 : Nat := 4983230072969 + 3 ^ 40 * 1881821 * 2
def baseEnd_1881821 : Nat := 322092892908195700127723

theorem tailTrace_1881821 : CollatzResearch.WordTrace tailWord_1881821 prefixEnd_1881821 322092892908195700127723 := by
  unfold tailWord_1881821
  simp only [CollatzResearch.WordTrace]
  refine ⟨68635650515491381284789317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45757100343660920856526211 68635650515491381284789317)
  ·
    refine ⟨12869184471654633990897997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68635650515491381284789317 12869184471654633990897997)
    ·
      refine ⟨4825944176870487746586749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12869184471654633990897997 4825944176870487746586749)
      ·
        refine ⟨1809729066326432904970031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4825944176870487746586749 1809729066326432904970031)
        ·
          refine ⟨2714593599489649357455047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809729066326432904970031 2714593599489649357455047)
          ·
            refine ⟨4071890399234474036182571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714593599489649357455047 4071890399234474036182571)
            ·
              refine ⟨6107835598851711054273857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071890399234474036182571 6107835598851711054273857)
              ·
                refine ⟨4580876699138783290705393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6107835598851711054273857 4580876699138783290705393)
                ·
                  refine ⟨3435657524354087468029045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580876699138783290705393 3435657524354087468029045)
                  ·
                    refine ⟨322092892908195700127723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3435657524354087468029045 322092892908195700127723)
                    ·
                      rfl

theorem cell23_1881821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1881821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881821 prefixEnd_1881821 := by exact prefixLift 1881821
  have htrace : WordTrace (prefixWord ++ tailWord_1881821) baseStart_1881821 baseEnd_1881821 := by
    simpa [prefixWord, tailWord_1881821, baseEnd_1881821] using wordTrace_append hprefix tailTrace_1881821
  have hstable : (prefixWord ++ tailWord_1881821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881821).length < 2 ^ (prefixWord ++ tailWord_1881821).sum := by decide
  have hdescent : baseEnd_1881821 < baseStart_1881821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881834 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1881834 : Nat := 118140960795 + 1881834 * 2 ^ 59
def prefixEnd_1881834 : Nat := 4983230072969 + 3 ^ 40 * 1881834 * 2
def baseEnd_1881834 : Nat := 322095117991031849840203

theorem tailTrace_1881834 : CollatzResearch.WordTrace tailWord_1881834 prefixEnd_1881834 322095117991031849840203 := by
  unfold tailWord_1881834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159031166111071126253139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45757416442962856336675037 17159031166111071126253139)
  ·
    refine ⟨25738546749166606689379709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17159031166111071126253139 25738546749166606689379709)
    ·
      refine ⟨9651955030937477508517391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25738546749166606689379709 9651955030937477508517391)
      ·
        refine ⟨14477932546406216262776087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651955030937477508517391 14477932546406216262776087)
        ·
          refine ⟨21716898819609324394164131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14477932546406216262776087 21716898819609324394164131)
          ·
            refine ⟨32575348229413986591246197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21716898819609324394164131 32575348229413986591246197)
            ·
              refine ⟨3053938896507561242929331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32575348229413986591246197 3053938896507561242929331)
              ·
                refine ⟨4580908344761341864393997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053938896507561242929331 4580908344761341864393997)
                ·
                  refine ⟨1717840629285503199147749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4580908344761341864393997 1717840629285503199147749)
                  ·
                    refine ⟨322095117991031849840203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717840629285503199147749 322095117991031849840203)
                    ·
                      rfl

theorem cell23_1881834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1881834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881834 prefixEnd_1881834 := by exact prefixLift 1881834
  have htrace : WordTrace (prefixWord ++ tailWord_1881834) baseStart_1881834 baseEnd_1881834 := by
    simpa [prefixWord, tailWord_1881834, baseEnd_1881834] using wordTrace_append hprefix tailTrace_1881834
  have hstable : (prefixWord ++ tailWord_1881834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881834).length < 2 ^ (prefixWord ++ tailWord_1881834).sum := by decide
  have hdescent : baseEnd_1881834 < baseStart_1881834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881857 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1881857 : Nat := 118140960795 + 1881857 * 2 ^ 59
def prefixEnd_1881857 : Nat := 4983230072969 + 3 ^ 40 * 1881857 * 2
def baseEnd_1881857 : Nat := 966297164028148959533003

theorem tailTrace_1881857 : CollatzResearch.WordTrace tailWord_1881857 prefixEnd_1881857 966297164028148959533003 := by
  unfold tailWord_1881857
  simp only [CollatzResearch.WordTrace]
  refine ⟨68636963543360959433099825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45757975695573972955399883 68636963543360959433099825)
  ·
    refine ⟨51477722657520719574824869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68636963543360959433099825 51477722657520719574824869)
    ·
      refine ⟨9652072998285134920279663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51477722657520719574824869 9652072998285134920279663)
      ·
        refine ⟨14478109497427702380419495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652072998285134920279663 14478109497427702380419495)
        ·
          refine ⟨21717164246141553570629243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478109497427702380419495 21717164246141553570629243)
          ·
            refine ⟨32575746369212330355943865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717164246141553570629243 32575746369212330355943865)
            ·
              refine ⟨24431809776909247766957899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32575746369212330355943865 24431809776909247766957899)
              ·
                refine ⟨36647714665363871650436849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24431809776909247766957899 36647714665363871650436849)
                ·
                  refine ⟨27485785999022903737827637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36647714665363871650436849 27485785999022903737827637)
                  ·
                    refine ⟨2576792437408397225421341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27485785999022903737827637 2576792437408397225421341)
                    ·
                      refine ⟨966297164028148959533003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2576792437408397225421341 966297164028148959533003)
                      ·
                        rfl

theorem cell23_1881857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1881857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881857 prefixEnd_1881857 := by exact prefixLift 1881857
  have htrace : WordTrace (prefixWord ++ tailWord_1881857) baseStart_1881857 baseEnd_1881857 := by
    simpa [prefixWord, tailWord_1881857, baseEnd_1881857] using wordTrace_append hprefix tailTrace_1881857
  have hstable : (prefixWord ++ tailWord_1881857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881857).length < 2 ^ (prefixWord ++ tailWord_1881857).sum := by decide
  have hdescent : baseEnd_1881857 < baseStart_1881857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881908 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1881908 : Nat := 118140960795 + 1881908 * 2 ^ 59
def prefixEnd_1881908 : Nat := 4983230072969 + 3 ^ 40 * 1881908 * 2
def baseEnd_1881908 : Nat := 966323351541528259995269

theorem tailTrace_1881908 : CollatzResearch.WordTrace tailWord_1881908 prefixEnd_1881908 966323351541528259995269 := by
  unfold tailWord_1881908
  simp only [CollatzResearch.WordTrace]
  refine ⟨34319411833088097571603189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45759215777450796762137585 34319411833088097571603189)
  ·
    refine ⟨3217444859352009147337799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34319411833088097571603189 3217444859352009147337799)
    ·
      refine ⟨4826167289028013721006699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217444859352009147337799 4826167289028013721006699)
      ·
        refine ⟨7239250933542020581510049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826167289028013721006699 7239250933542020581510049)
        ·
          refine ⟨5429438200156515436132537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7239250933542020581510049 5429438200156515436132537)
          ·
            refine ⟨4072078650117386577099403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5429438200156515436132537 4072078650117386577099403)
            ·
              refine ⟨6108117975176079865649105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072078650117386577099403 6108117975176079865649105)
              ·
                refine ⟨4581088481382059899236829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108117975176079865649105 4581088481382059899236829)
                ·
                  refine ⟨1717908180518272462213811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4581088481382059899236829 1717908180518272462213811)
                  ·
                    refine ⟨2576862270777408693320717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1717908180518272462213811 2576862270777408693320717)
                    ·
                      refine ⟨966323351541528259995269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2576862270777408693320717 966323351541528259995269)
                      ·
                        rfl

theorem cell23_1881908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1881908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881908 prefixEnd_1881908 := by exact prefixLift 1881908
  have htrace : WordTrace (prefixWord ++ tailWord_1881908) baseStart_1881908 baseEnd_1881908 := by
    simpa [prefixWord, tailWord_1881908, baseEnd_1881908] using wordTrace_append hprefix tailTrace_1881908
  have hstable : (prefixWord ++ tailWord_1881908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881908).length < 2 ^ (prefixWord ++ tailWord_1881908).sum := by decide
  have hdescent : baseEnd_1881908 < baseStart_1881908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881914 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1881914 : Nat := 118140960795 + 1881914 * 2 ^ 59
def prefixEnd_1881914 : Nat := 4983230072969 + 3 ^ 40 * 1881914 * 2
def baseEnd_1881914 : Nat := 966326432425455236520241

theorem tailTrace_1881914 : CollatzResearch.WordTrace tailWord_1881914 prefixEnd_1881914 966326432425455236520241 := by
  unfold tailWord_1881914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159760626038614541981199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45759361669436305445283197 17159760626038614541981199)
  ·
    refine ⟨25739640939057921812971799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17159760626038614541981199 25739640939057921812971799)
    ·
      refine ⟨38609461408586882719457699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25739640939057921812971799 38609461408586882719457699)
      ·
        refine ⟨57914192112880324079186549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38609461408586882719457699 57914192112880324079186549)
        ·
          refine ⟨5429455510582530382423739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57914192112880324079186549 5429455510582530382423739)
          ·
            refine ⟨8144183265873795573635609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429455510582530382423739 8144183265873795573635609)
            ·
              refine ⟨6108137449405346680226707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8144183265873795573635609 6108137449405346680226707)
              ·
                refine ⟨9162206174108020020340061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108137449405346680226707 9162206174108020020340061)
                ·
                  refine ⟨3435827315290507507627523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9162206174108020020340061 3435827315290507507627523)
                  ·
                    refine ⟨5153740972935761261441285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3435827315290507507627523 5153740972935761261441285)
                    ·
                      refine ⟨966326432425455236520241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5153740972935761261441285 966326432425455236520241)
                      ·
                        rfl

theorem cell23_1881914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1881914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881914 prefixEnd_1881914 := by exact prefixLift 1881914
  have htrace : WordTrace (prefixWord ++ tailWord_1881914) baseStart_1881914 baseEnd_1881914 := by
    simpa [prefixWord, tailWord_1881914, baseEnd_1881914] using wordTrace_append hprefix tailTrace_1881914
  have hstable : (prefixWord ++ tailWord_1881914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881914).length < 2 ^ (prefixWord ++ tailWord_1881914).sum := by decide
  have hdescent : baseEnd_1881914 < baseStart_1881914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881918 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_1881918 : Nat := 118140960795 + 1881918 * 2 ^ 59
def prefixEnd_1881918 : Nat := 4983230072969 + 3 ^ 40 * 1881918 * 2
def baseEnd_1881918 : Nat := 966328486348073220870223

theorem tailTrace_1881918 : CollatzResearch.WordTrace tailWord_1881918 prefixEnd_1881918 966328486348073220870223 := by
  unfold tailWord_1881918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579898549517495856383801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45759458930759977900713605 8579898549517495856383801)
  ·
    refine ⟨6434923912138121892287851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8579898549517495856383801 6434923912138121892287851)
    ·
      refine ⟨9652385868207182838431777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434923912138121892287851 9652385868207182838431777)
      ·
        refine ⟨7239289401155387128823833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9652385868207182838431777 7239289401155387128823833)
        ·
          refine ⟨5429467050866540346617875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7239289401155387128823833 5429467050866540346617875)
          ·
            refine ⟨8144200576299810519926813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429467050866540346617875 8144200576299810519926813)
            ·
              refine ⟨3054075216112428944972555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8144200576299810519926813 3054075216112428944972555)
              ·
                refine ⟨4581112824168643417458833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054075216112428944972555 4581112824168643417458833)
                ·
                  refine ⟨3435834618126482563094125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581112824168643417458833 3435834618126482563094125)
                  ·
                    refine ⟨1288437981797430961160297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435834618126482563094125 1288437981797430961160297)
                    ·
                      refine ⟨966328486348073220870223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288437981797430961160297 966328486348073220870223)
                      ·
                        rfl

theorem cell23_1881918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_1881918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881918 prefixEnd_1881918 := by exact prefixLift 1881918
  have htrace : WordTrace (prefixWord ++ tailWord_1881918) baseStart_1881918 baseEnd_1881918 := by
    simpa [prefixWord, tailWord_1881918, baseEnd_1881918] using wordTrace_append hprefix tailTrace_1881918
  have hstable : (prefixWord ++ tailWord_1881918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881918).length < 2 ^ (prefixWord ++ tailWord_1881918).sum := by decide
  have hdescent : baseEnd_1881918 < baseStart_1881918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881937 : List Nat := [1, 2, 2, 1, 5, 2, 10]
def baseStart_1881937 : Nat := 118140960795 + 1881937 * 2 ^ 59
def prefixEnd_1881937 : Nat := 4983230072969 + 3 ^ 40 * 1881937 * 2
def baseEnd_1881937 : Nat := 11930101759018625265835

theorem tailTrace_1881937 : CollatzResearch.WordTrace tailWord_1881937 prefixEnd_1881937 11930101759018625265835 := by
  unfold tailWord_1881937
  simp only [CollatzResearch.WordTrace]
  refine ⟨68639881383071133096012065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45759920922047422064008043 68639881383071133096012065)
  ·
    refine ⟨51479911037303349822009049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68639881383071133096012065 51479911037303349822009049)
    ·
      refine ⟨38609933277977512366506787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51479911037303349822009049 38609933277977512366506787)
      ·
        refine ⟨57914899916966268549760181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38609933277977512366506787 57914899916966268549760181)
        ·
          refine ⟨5429521867215587676540017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57914899916966268549760181 5429521867215587676540017)
          ·
            refine ⟨4072141400411690757405013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5429521867215587676540017 4072141400411690757405013)
            ·
              refine ⟨11930101759018625265835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4072141400411690757405013 11930101759018625265835)
              ·
                rfl

theorem cell23_1881937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 10].length) (baseStart_1881937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881937 prefixEnd_1881937 := by exact prefixLift 1881937
  have htrace : WordTrace (prefixWord ++ tailWord_1881937) baseStart_1881937 baseEnd_1881937 := by
    simpa [prefixWord, tailWord_1881937, baseEnd_1881937] using wordTrace_append hprefix tailTrace_1881937
  have hstable : (prefixWord ++ tailWord_1881937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881937).length < 2 ^ (prefixWord ++ tailWord_1881937).sum := by decide
  have hdescent : baseEnd_1881937 < baseStart_1881937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881941 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1881941 : Nat := 118140960795 + 1881941 * 2 ^ 59
def prefixEnd_1881941 : Nat := 4983230072969 + 3 ^ 40 * 1881941 * 2
def baseEnd_1881941 : Nat := 322113432134375543627539

theorem tailTrace_1881941 : CollatzResearch.WordTrace tailWord_1881941 prefixEnd_1881941 322113432134375543627539 := by
  unfold tailWord_1881941
  simp only [CollatzResearch.WordTrace]
  refine ⟨68640027275056641779157677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45760018183371094519438451 68640027275056641779157677)
  ·
    refine ⟨25740010228146240667184129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68640027275056641779157677 25740010228146240667184129)
    ·
      refine ⟨19305007671109680500388097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25740010228146240667184129 19305007671109680500388097)
      ·
        refine ⟨14478755753332260375291073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19305007671109680500388097 14478755753332260375291073)
        ·
          refine ⟨10859066814999195281468305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14478755753332260375291073 10859066814999195281468305)
          ·
            refine ⟨8144300111249396461101229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10859066814999195281468305 8144300111249396461101229)
            ·
              refine ⟨3054112541718523672912961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8144300111249396461101229 3054112541718523672912961)
              ·
                refine ⟨2290584406288892754684721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054112541718523672912961 2290584406288892754684721)
                ·
                  refine ⟨1717938304716669566013541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2290584406288892754684721 1717938304716669566013541)
                  ·
                    refine ⟨322113432134375543627539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717938304716669566013541 322113432134375543627539)
                    ·
                      rfl

theorem cell23_1881941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1881941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881941 prefixEnd_1881941 := by exact prefixLift 1881941
  have htrace : WordTrace (prefixWord ++ tailWord_1881941) baseStart_1881941 baseEnd_1881941 := by
    simpa [prefixWord, tailWord_1881941, baseEnd_1881941] using wordTrace_append hprefix tailTrace_1881941
  have hstable : (prefixWord ++ tailWord_1881941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881941).length < 2 ^ (prefixWord ++ tailWord_1881941).sum := by decide
  have hdescent : baseEnd_1881941 < baseStart_1881941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881977 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1881977 : Nat := 118140960795 + 1881977 * 2 ^ 59
def prefixEnd_1881977 : Nat := 4983230072969 + 3 ^ 40 * 1881977 * 2
def baseEnd_1881977 : Nat := 966358781706688490032451

theorem tailTrace_1881977 : CollatzResearch.WordTrace tailWord_1881977 prefixEnd_1881977 966358781706688490032451 := by
  unfold tailWord_1881977
  simp only [CollatzResearch.WordTrace]
  refine ⟨68641340302926219927468185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45760893535284146618312123 68641340302926219927468185)
  ·
    refine ⟨51481005227194664945601139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68641340302926219927468185 51481005227194664945601139)
    ·
      refine ⟨77221507840791997418401709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51481005227194664945601139 77221507840791997418401709)
      ·
        refine ⟨28958065440296999031900641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77221507840791997418401709 28958065440296999031900641)
        ·
          refine ⟨21718549080222749273925481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28958065440296999031900641 21718549080222749273925481)
          ·
            refine ⟨16288911810167061955444111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21718549080222749273925481 16288911810167061955444111)
            ·
              refine ⟨24433367715250592933166167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16288911810167061955444111 24433367715250592933166167)
              ·
                refine ⟨36650051572875889399749251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24433367715250592933166167 36650051572875889399749251)
                ·
                  refine ⟨54975077359313834099623877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36650051572875889399749251 54975077359313834099623877)
                  ·
                    refine ⟨10307827004871343893679477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54975077359313834099623877 10307827004871343893679477)
                    ·
                      refine ⟨966358781706688490032451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10307827004871343893679477 966358781706688490032451)
                      ·
                        rfl

theorem cell23_1881977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1881977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1881977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1881977 prefixEnd_1881977 := by exact prefixLift 1881977
  have htrace : WordTrace (prefixWord ++ tailWord_1881977) baseStart_1881977 baseEnd_1881977 := by
    simpa [prefixWord, tailWord_1881977, baseEnd_1881977] using wordTrace_append hprefix tailTrace_1881977
  have hstable : (prefixWord ++ tailWord_1881977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881977).length < 2 ^ (prefixWord ++ tailWord_1881977).sum := by decide
  have hdescent : baseEnd_1881977 < baseStart_1881977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882124 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1882124 : Nat := 118140960795 + 1882124 * 2 ^ 59
def prefixEnd_1882124 : Nat := 4983230072969 + 3 ^ 40 * 1882124 * 2
def baseEnd_1882124 : Nat := 966434263362899414894275

theorem tailTrace_1882124 : CollatzResearch.WordTrace tailWord_1882124 prefixEnd_1882124 966434263362899414894275 := by
  unfold tailWord_1882124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323350916696832016534713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45764467888929109355379617 34323350916696832016534713)
  ·
    refine ⟨25742513187522624012401035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34323350916696832016534713 25742513187522624012401035)
    ·
      refine ⟨38613769781283936018601553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25742513187522624012401035 38613769781283936018601553)
      ·
        refine ⟨28960327335962952013951165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38613769781283936018601553 28960327335962952013951165)
        ·
          refine ⟨10860122750986107005231687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28960327335962952013951165 10860122750986107005231687)
          ·
            refine ⟨16290184126479160507847531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860122750986107005231687 16290184126479160507847531)
            ·
              refine ⟨24435276189718740761771297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16290184126479160507847531 24435276189718740761771297)
              ·
                refine ⟨18326457142289055571328473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24435276189718740761771297 18326457142289055571328473)
                ·
                  refine ⟨13744842856716791678496355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18326457142289055571328473 13744842856716791678496355)
                  ·
                    refine ⟨20617264285075187517744533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13744842856716791678496355 20617264285075187517744533)
                    ·
                      refine ⟨966434263362899414894275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20617264285075187517744533 966434263362899414894275)
                      ·
                        rfl

theorem cell23_1882124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1882124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882124 prefixEnd_1882124 := by exact prefixLift 1882124
  have htrace : WordTrace (prefixWord ++ tailWord_1882124) baseStart_1882124 baseEnd_1882124 := by
    simpa [prefixWord, tailWord_1882124, baseEnd_1882124] using wordTrace_append hprefix tailTrace_1882124
  have hstable : (prefixWord ++ tailWord_1882124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882124).length < 2 ^ (prefixWord ++ tailWord_1882124).sum := by decide
  have hdescent : baseEnd_1882124 < baseStart_1882124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882201 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1882201 : Nat := 118140960795 + 1882201 * 2 ^ 59
def prefixEnd_1882201 : Nat := 4983230072969 + 3 ^ 40 * 1882201 * 2
def baseEnd_1882201 : Nat := 966473801373295613631421

theorem tailTrace_1882201 : CollatzResearch.WordTrace tailWord_1882201 prefixEnd_1882201 966473801373295613631421 := by
  unfold tailWord_1882201
  simp only [CollatzResearch.WordTrace]
  refine ⟨68649510254114706183622457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45766340169409804122414971 68649510254114706183622457)
  ·
    refine ⟨51487132690586029637716843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68649510254114706183622457 51487132690586029637716843)
    ·
      refine ⟨77230699035879044456575265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51487132690586029637716843 77230699035879044456575265)
      ·
        refine ⟨57923024276909283342431449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77230699035879044456575265 57923024276909283342431449)
        ·
          refine ⟨43442268207681962506823587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57923024276909283342431449 43442268207681962506823587)
          ·
            refine ⟨65163402311522943760235381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43442268207681962506823587 65163402311522943760235381)
            ·
              refine ⟨6109068966705275977522067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65163402311522943760235381 6109068966705275977522067)
              ·
                refine ⟨9163603450057913966283101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109068966705275977522067 9163603450057913966283101)
                ·
                  refine ⟨3436351293771717737356163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9163603450057913966283101 3436351293771717737356163)
                  ·
                    refine ⟨5154526940657576606034245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3436351293771717737356163 5154526940657576606034245)
                    ·
                      refine ⟨966473801373295613631421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5154526940657576606034245 966473801373295613631421)
                      ·
                        rfl

theorem cell23_1882201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1882201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882201 prefixEnd_1882201 := by exact prefixLift 1882201
  have htrace : WordTrace (prefixWord ++ tailWord_1882201) baseStart_1882201 baseEnd_1882201 := by
    simpa [prefixWord, tailWord_1882201, baseEnd_1882201] using wordTrace_append hprefix tailTrace_1882201
  have hstable : (prefixWord ++ tailWord_1882201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882201).length < 2 ^ (prefixWord ++ tailWord_1882201).sum := by decide
  have hdescent : baseEnd_1882201 < baseStart_1882201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882211 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 6, 4]
def baseStart_1882211 : Nat := 118140960795 + 1882211 * 2 ^ 59
def prefixEnd_1882211 : Nat := 4983230072969 + 3 ^ 40 * 1882211 * 2
def baseEnd_1882211 : Nat := 322159645393280191502125

theorem tailTrace_1882211 : CollatzResearch.WordTrace tailWord_1882211 prefixEnd_1882211 322159645393280191502125 := by
  unfold tailWord_1882211
  simp only [CollatzResearch.WordTrace]
  refine ⟨68649874984078477891486487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45766583322718985260990991 68649874984078477891486487)
  ·
    refine ⟨102974812476117716837229731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68649874984078477891486487 102974812476117716837229731)
    ·
      refine ⟨154462218714176575255844597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102974812476117716837229731 154462218714176575255844597)
      ·
        refine ⟨14480833004454053930235431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154462218714176575255844597 14480833004454053930235431)
        ·
          refine ⟨21721249506681080895353147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14480833004454053930235431 21721249506681080895353147)
          ·
            refine ⟨32581874260021621343029721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21721249506681080895353147 32581874260021621343029721)
            ·
              refine ⟨24436405695016216007272291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32581874260021621343029721 24436405695016216007272291)
              ·
                refine ⟨36654608542524324010908437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24436405695016216007272291 36654608542524324010908437)
                ·
                  refine ⟨1718184775430827688011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36654608542524324010908437 1718184775430827688011333)
                  ·
                    refine ⟨322159645393280191502125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718184775430827688011333 322159645393280191502125)
                    ·
                      rfl

theorem cell23_1882211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 4].length) (baseStart_1882211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882211 prefixEnd_1882211 := by exact prefixLift 1882211
  have htrace : WordTrace (prefixWord ++ tailWord_1882211) baseStart_1882211 baseEnd_1882211 := by
    simpa [prefixWord, tailWord_1882211, baseEnd_1882211] using wordTrace_append hprefix tailTrace_1882211
  have hstable : (prefixWord ++ tailWord_1882211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882211).length < 2 ^ (prefixWord ++ tailWord_1882211).sum := by decide
  have hdescent : baseEnd_1882211 < baseStart_1882211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882224 : List Nat := [2, 1, 1, 1, 5, 13]
def baseStart_1882224 : Nat := 118140960795 + 1882224 * 2 ^ 59
def prefixEnd_1882224 : Nat := 4983230072969 + 3 ^ 40 * 1882224 * 2
def baseEnd_1882224 : Nat := 3977307042915016558205

theorem tailTrace_1882224 : CollatzResearch.WordTrace tailWord_1882224 prefixEnd_1882224 3977307042915016558205 := by
  unfold tailWord_1882224
  simp only [CollatzResearch.WordTrace]
  refine ⟨34325174566515690555854863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45766899422020920741139817 34325174566515690555854863)
  ·
    refine ⟨51487761849773535833782295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34325174566515690555854863 51487761849773535833782295)
    ·
      refine ⟨77231642774660303750673443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51487761849773535833782295 77231642774660303750673443)
      ·
        refine ⟨115847464161990455626010165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77231642774660303750673443 115847464161990455626010165)
        ·
          refine ⟨10860699765186605214938453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115847464161990455626010165 10860699765186605214938453)
          ·
            refine ⟨3977307042915016558205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 10860699765186605214938453 3977307042915016558205)
            ·
              rfl

theorem cell23_1882224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 13].length) (baseStart_1882224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882224 prefixEnd_1882224 := by exact prefixLift 1882224
  have htrace : WordTrace (prefixWord ++ tailWord_1882224) baseStart_1882224 baseEnd_1882224 := by
    simpa [prefixWord, tailWord_1882224, baseEnd_1882224] using wordTrace_append hprefix tailTrace_1882224
  have hstable : (prefixWord ++ tailWord_1882224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882224).length < 2 ^ (prefixWord ++ tailWord_1882224).sum := by decide
  have hdescent : baseEnd_1882224 < baseStart_1882224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882248 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1882248 : Nat := 118140960795 + 1882248 * 2 ^ 59
def prefixEnd_1882248 : Nat := 4983230072969 + 3 ^ 40 * 1882248 * 2
def baseEnd_1882248 : Nat := 966497934964056929743705

theorem tailTrace_1882248 : CollatzResearch.WordTrace tailWord_1882248 prefixEnd_1882248 966497934964056929743705 := by
  unfold tailWord_1882248
  simp only [CollatzResearch.WordTrace]
  refine ⟨34325612242472216605291699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45767482989962955473722265 34325612242472216605291699)
  ·
    refine ⟨51488418363708324907937549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34325612242472216605291699 51488418363708324907937549)
    ·
      refine ⟨19308156886390621840476581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51488418363708324907937549 19308156886390621840476581)
      ·
        refine ⟨3620279416198241595089359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19308156886390621840476581 3620279416198241595089359)
        ·
          refine ⟨5430419124297362392634039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620279416198241595089359 5430419124297362392634039)
          ·
            refine ⟨8145628686446043588951059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430419124297362392634039 8145628686446043588951059)
            ·
              refine ⟨12218443029669065383426589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145628686446043588951059 12218443029669065383426589)
              ·
                refine ⟨4581916136125899518784971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218443029669065383426589 4581916136125899518784971)
                ·
                  refine ⟨6872874204188849278177457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581916136125899518784971 6872874204188849278177457)
                  ·
                    refine ⟨5154655653141636958633093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872874204188849278177457 5154655653141636958633093)
                    ·
                      refine ⟨966497934964056929743705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5154655653141636958633093 966497934964056929743705)
                      ·
                        rfl

theorem cell23_1882248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1882248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882248 prefixEnd_1882248 := by exact prefixLift 1882248
  have htrace : WordTrace (prefixWord ++ tailWord_1882248) baseStart_1882248 baseEnd_1882248 := by
    simpa [prefixWord, tailWord_1882248, baseEnd_1882248] using wordTrace_append hprefix tailTrace_1882248
  have hstable : (prefixWord ++ tailWord_1882248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882248).length < 2 ^ (prefixWord ++ tailWord_1882248).sum := by decide
  have hdescent : baseEnd_1882248 < baseStart_1882248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882258 : List Nat := [3, 2, 3, 1, 1, 1, 5, 7]
def baseStart_1882258 : Nat := 118140960795 + 1882258 * 2 ^ 59
def prefixEnd_1882258 : Nat := 4983230072969 + 3 ^ 40 * 1882258 * 2
def baseEnd_1882258 : Nat := 35796409991503773726617

theorem tailTrace_1882258 : CollatzResearch.WordTrace tailWord_1882258 prefixEnd_1882258 35796409991503773726617 := by
  unfold tailWord_1882258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162897303727051229611857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45767726143272136612298285 17162897303727051229611857)
  ·
    refine ⟨12872172977795288422208893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17162897303727051229611857 12872172977795288422208893)
    ·
      refine ⟨4827064866673233158328335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12872172977795288422208893 4827064866673233158328335)
      ·
        refine ⟨7240597300009849737492503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827064866673233158328335 7240597300009849737492503)
        ·
          refine ⟨10860895950014774606238755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7240597300009849737492503 10860895950014774606238755)
          ·
            refine ⟨16291343925022161909358133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860895950014774606238755 16291343925022161909358133)
            ·
              refine ⟨1527313492970827679002325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16291343925022161909358133 1527313492970827679002325)
              ·
                refine ⟨35796409991503773726617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1527313492970827679002325 35796409991503773726617)
                ·
                  rfl

theorem cell23_1882258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_1882258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882258 prefixEnd_1882258 := by exact prefixLift 1882258
  have htrace : WordTrace (prefixWord ++ tailWord_1882258) baseStart_1882258 baseEnd_1882258 := by
    simpa [prefixWord, tailWord_1882258, baseEnd_1882258] using wordTrace_append hprefix tailTrace_1882258
  have hstable : (prefixWord ++ tailWord_1882258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882258).length < 2 ^ (prefixWord ++ tailWord_1882258).sum := by decide
  have hdescent : baseEnd_1882258 < baseStart_1882258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882268 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1882268 : Nat := 118140960795 + 1882268 * 2 ^ 59
def prefixEnd_1882268 : Nat := 4983230072969 + 3 ^ 40 * 1882268 * 2
def baseEnd_1882268 : Nat := 966508204577146851493613

theorem tailTrace_1882268 : CollatzResearch.WordTrace tailWord_1882268 prefixEnd_1882268 966508204577146851493613 := by
  unfold tailWord_1882268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34325976972435988313155729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45767969296581317750874305 34325976972435988313155729)
  ·
    refine ⟨25744482729326991234866797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34325976972435988313155729 25744482729326991234866797)
    ·
      refine ⟨9654181023497621713075049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25744482729326991234866797 9654181023497621713075049)
      ·
        refine ⟨7240635767623216284806287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9654181023497621713075049 7240635767623216284806287)
        ·
          refine ⟨10860953651434824427209431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7240635767623216284806287 10860953651434824427209431)
          ·
            refine ⟨16291430477152236640814147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860953651434824427209431 16291430477152236640814147)
            ·
              refine ⟨24437145715728354961221221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16291430477152236640814147 24437145715728354961221221)
              ·
                refine ⟨4581964821699066555228979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24437145715728354961221221 4581964821699066555228979)
                ·
                  refine ⟨6872947232548599832843469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581964821699066555228979 6872947232548599832843469)
                  ·
                    refine ⟨2577355212205724937316301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6872947232548599832843469 2577355212205724937316301)
                    ·
                      refine ⟨966508204577146851493613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577355212205724937316301 966508204577146851493613)
                      ·
                        rfl

theorem cell23_1882268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1882268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882268 prefixEnd_1882268 := by exact prefixLift 1882268
  have htrace : WordTrace (prefixWord ++ tailWord_1882268) baseStart_1882268 baseEnd_1882268 := by
    simpa [prefixWord, tailWord_1882268, baseEnd_1882268] using wordTrace_append hprefix tailTrace_1882268
  have hstable : (prefixWord ++ tailWord_1882268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882268).length < 2 ^ (prefixWord ++ tailWord_1882268).sum := by decide
  have hdescent : baseEnd_1882268 < baseStart_1882268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882269 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_1882269 : Nat := 118140960795 + 1882269 * 2 ^ 59
def prefixEnd_1882269 : Nat := 4983230072969 + 3 ^ 40 * 1882269 * 2
def baseEnd_1882269 : Nat := 966508718057801347581109

theorem tailTrace_1882269 : CollatzResearch.WordTrace tailWord_1882269 prefixEnd_1882269 966508718057801347581109 := by
  unfold tailWord_1882269
  simp only [CollatzResearch.WordTrace]
  refine ⟨68651990417868353797097861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45767993611912235864731907 68651990417868353797097861)
  ·
    refine ⟨12872248203350316336955849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68651990417868353797097861 12872248203350316336955849)
    ·
      refine ⟨9654186152512737252716887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12872248203350316336955849 9654186152512737252716887)
      ·
        refine ⟨14481279228769105879075331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654186152512737252716887 14481279228769105879075331)
        ·
          refine ⟨21721918843153658818612997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481279228769105879075331 21721918843153658818612997)
          ·
            refine ⟨4072859783091311028489937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21721918843153658818612997 4072859783091311028489937)
            ·
              refine ⟨3054644837318483271367453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072859783091311028489937 3054644837318483271367453)
              ·
                refine ⟨1145491813994431226762795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3054644837318483271367453 1145491813994431226762795)
                ·
                  refine ⟨1718237720991646840144193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145491813994431226762795 1718237720991646840144193)
                  ·
                    refine ⟨1288678290743735130108145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1718237720991646840144193 1288678290743735130108145)
                    ·
                      refine ⟨966508718057801347581109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288678290743735130108145 966508718057801347581109)
                      ·
                        rfl

theorem cell23_1882269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_1882269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882269 prefixEnd_1882269 := by exact prefixLift 1882269
  have htrace : WordTrace (prefixWord ++ tailWord_1882269) baseStart_1882269 baseEnd_1882269 := by
    simpa [prefixWord, tailWord_1882269, baseEnd_1882269] using wordTrace_append hprefix tailTrace_1882269
  have hstable : (prefixWord ++ tailWord_1882269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882269).length < 2 ^ (prefixWord ++ tailWord_1882269).sum := by decide
  have hdescent : baseEnd_1882269 < baseStart_1882269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882272 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3]
def baseStart_1882272 : Nat := 118140960795 + 1882272 * 2 ^ 59
def prefixEnd_1882272 : Nat := 4983230072969 + 3 ^ 40 * 1882272 * 2
def baseEnd_1882272 : Nat := 966510258499764835843595

theorem tailTrace_1882272 : CollatzResearch.WordTrace tailWord_1882272 prefixEnd_1882272 966510258499764835843595 := by
  unfold tailWord_1882272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326049918428742654728535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45768066557904990206304713 34326049918428742654728535)
  ·
    refine ⟨51489074877643113982092803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34326049918428742654728535 51489074877643113982092803)
    ·
      refine ⟨77233612316464670973139205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51489074877643113982092803 77233612316464670973139205)
      ·
        refine ⟨14481302309337125807463601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77233612316464670973139205 14481302309337125807463601)
        ·
          refine ⟨10860976732002844355597701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14481302309337125807463601 10860976732002844355597701)
          ·
            refine ⟨2036433137250533316674569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10860976732002844355597701 2036433137250533316674569)
            ·
              refine ⟨1527324852937899987505927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036433137250533316674569 1527324852937899987505927)
              ·
                refine ⟨2290987279406849981258891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527324852937899987505927 2290987279406849981258891)
                ·
                  refine ⟨3436480919110274971888337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290987279406849981258891 3436480919110274971888337)
                  ·
                    refine ⟨2577360689332706228916253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436480919110274971888337 2577360689332706228916253)
                    ·
                      refine ⟨966510258499764835843595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577360689332706228916253 966510258499764835843595)
                      ·
                        rfl

theorem cell23_1882272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_1882272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882272 prefixEnd_1882272 := by exact prefixLift 1882272
  have htrace : WordTrace (prefixWord ++ tailWord_1882272) baseStart_1882272 baseEnd_1882272 := by
    simpa [prefixWord, tailWord_1882272, baseEnd_1882272] using wordTrace_append hprefix tailTrace_1882272
  have hstable : (prefixWord ++ tailWord_1882272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882272).length < 2 ^ (prefixWord ++ tailWord_1882272).sum := by decide
  have hdescent : baseEnd_1882272 < baseStart_1882272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882279 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1882279 : Nat := 118140960795 + 1882279 * 2 ^ 59
def prefixEnd_1882279 : Nat := 4983230072969 + 3 ^ 40 * 1882279 * 2
def baseEnd_1882279 : Nat := 322171284288115436152021

theorem tailTrace_1882279 : CollatzResearch.WordTrace tailWord_1882279 prefixEnd_1882279 322171284288115436152021 := by
  unfold tailWord_1882279
  simp only [CollatzResearch.WordTrace]
  refine ⟨68652355147832125504961891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45768236765221417003307927 68652355147832125504961891)
  ·
    refine ⟨102978532721748188257442837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68652355147832125504961891 102978532721748188257442837)
    ·
      refine ⟨4827118721331946324567633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102978532721748188257442837 4827118721331946324567633)
      ·
        refine ⟨3620339040998959743425725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827118721331946324567633 3620339040998959743425725)
        ·
          refine ⟨1357627140374609903784647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3620339040998959743425725 1357627140374609903784647)
          ·
            refine ⟨2036440710561914855676971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357627140374609903784647 2036440710561914855676971)
            ·
              refine ⟨3054661065842872283515457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036440710561914855676971 3054661065842872283515457)
              ·
                refine ⟨2290995799382154212636593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054661065842872283515457 2290995799382154212636593)
                ·
                  refine ⟨1718246849536615659477445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2290995799382154212636593 1718246849536615659477445)
                  ·
                    refine ⟨322171284288115436152021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718246849536615659477445 322171284288115436152021)
                    ·
                      rfl

theorem cell23_1882279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1882279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882279 prefixEnd_1882279 := by exact prefixLift 1882279
  have htrace : WordTrace (prefixWord ++ tailWord_1882279) baseStart_1882279 baseEnd_1882279 := by
    simpa [prefixWord, tailWord_1882279, baseEnd_1882279] using wordTrace_append hprefix tailTrace_1882279
  have hstable : (prefixWord ++ tailWord_1882279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882279).length < 2 ^ (prefixWord ++ tailWord_1882279).sum := by decide
  have hdescent : baseEnd_1882279 < baseStart_1882279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882286 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1882286 : Nat := 118140960795 + 1882286 * 2 ^ 59
def prefixEnd_1882286 : Nat := 4983230072969 + 3 ^ 40 * 1882286 * 2
def baseEnd_1882286 : Nat := 966517447228927781068531

theorem tailTrace_1882286 : CollatzResearch.WordTrace tailWord_1882286 prefixEnd_1882286 966517447228927781068531 := by
  unfold tailWord_1882286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581576307350845712558339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45768406972537843800311141 8581576307350845712558339)
  ·
    refine ⟨12872364461026268568837509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8581576307350845712558339 12872364461026268568837509)
    ·
      refine ⟨2413568336442425356657033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12872364461026268568837509 2413568336442425356657033)
      ·
        refine ⟨1810176252331819017492775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2413568336442425356657033 1810176252331819017492775)
        ·
          refine ⟨2715264378497728526239163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810176252331819017492775 2715264378497728526239163)
          ·
            refine ⟨4072896567746592789358745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715264378497728526239163 4072896567746592789358745)
            ·
              refine ⟨3054672425809944592019059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072896567746592789358745 3054672425809944592019059)
              ·
                refine ⟨4582008638714916888028589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054672425809944592019059 4582008638714916888028589)
                ·
                  refine ⟨1718253239518093833010721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4582008638714916888028589 1718253239518093833010721)
                  ·
                    refine ⟨1288689929638570374758041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1718253239518093833010721 1288689929638570374758041)
                    ·
                      refine ⟨966517447228927781068531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288689929638570374758041 966517447228927781068531)
                      ·
                        rfl

theorem cell23_1882286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1882286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882286 prefixEnd_1882286 := by exact prefixLift 1882286
  have htrace : WordTrace (prefixWord ++ tailWord_1882286) baseStart_1882286 baseEnd_1882286 := by
    simpa [prefixWord, tailWord_1882286, baseEnd_1882286] using wordTrace_append hprefix tailTrace_1882286
  have hstable : (prefixWord ++ tailWord_1882286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882286).length < 2 ^ (prefixWord ++ tailWord_1882286).sum := by decide
  have hdescent : baseEnd_1882286 < baseStart_1882286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882302 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1882302 : Nat := 118140960795 + 1882302 * 2 ^ 59
def prefixEnd_1882302 : Nat := 4983230072969 + 3 ^ 40 * 1882302 * 2
def baseEnd_1882302 : Nat := 966525662919399718468457

theorem tailTrace_1882302 : CollatzResearch.WordTrace tailWord_1882302 prefixEnd_1882302 966525662919399718468457 := by
  unfold tailWord_1882302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581649253343600054131145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45768796017832533622032773 8581649253343600054131145)
  ·
    refine ⟨6436236940007700040598359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8581649253343600054131145 6436236940007700040598359)
    ·
      refine ⟨9654355410011550060897539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436236940007700040598359 9654355410011550060897539)
      ·
        refine ⟨14481533115017325091346309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654355410011550060897539 14481533115017325091346309)
        ·
          refine ⟨2715287459065748454627433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14481533115017325091346309 2715287459065748454627433)
          ·
            refine ⟨2036465594299311340970575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715287459065748454627433 2036465594299311340970575)
            ·
              refine ⟨3054698391448967011455863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036465594299311340970575 3054698391448967011455863)
              ·
                refine ⟨4582047587173450517183795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054698391448967011455863 4582047587173450517183795)
                ·
                  refine ⟨6873071380760175775775693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582047587173450517183795 6873071380760175775775693)
                  ·
                    refine ⟨2577401767785065915915885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6873071380760175775775693 2577401767785065915915885)
                    ·
                      refine ⟨966525662919399718468457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577401767785065915915885 966525662919399718468457)
                      ·
                        rfl

theorem cell23_1882302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1882302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882302 prefixEnd_1882302 := by exact prefixLift 1882302
  have htrace : WordTrace (prefixWord ++ tailWord_1882302) baseStart_1882302 baseEnd_1882302 := by
    simpa [prefixWord, tailWord_1882302, baseEnd_1882302] using wordTrace_append hprefix tailTrace_1882302
  have hstable : (prefixWord ++ tailWord_1882302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882302).length < 2 ^ (prefixWord ++ tailWord_1882302).sum := by decide
  have hdescent : baseEnd_1882302 < baseStart_1882302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882321 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1882321 : Nat := 118140960795 + 1882321 * 2 ^ 59
def prefixEnd_1882321 : Nat := 4983230072969 + 3 ^ 40 * 1882321 * 2
def baseEnd_1882321 : Nat := 966535419051835144130869

theorem tailTrace_1882321 : CollatzResearch.WordTrace tailWord_1882321 prefixEnd_1882321 966535419051835144130869 := by
  unfold tailWord_1882321
  simp only [CollatzResearch.WordTrace]
  refine ⟨68653887013679966677990817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45769258009119977785327211 68653887013679966677990817)
  ·
    refine ⟨51490415260259975008493113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68653887013679966677990817 51490415260259975008493113)
    ·
      refine ⟨38617811445194981256369835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51490415260259975008493113 38617811445194981256369835)
      ·
        refine ⟨57926717167792471884554753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38617811445194981256369835 57926717167792471884554753)
        ·
          refine ⟨43445037875844353913416065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57926717167792471884554753 43445037875844353913416065)
          ·
            refine ⟨32583778406883265435062049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43445037875844353913416065 32583778406883265435062049)
            ·
              refine ⟨24437833805162449076296537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32583778406883265435062049 24437833805162449076296537)
              ·
                refine ⟨18328375353871836807222403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24437833805162449076296537 18328375353871836807222403)
                ·
                  refine ⟨27492563030807755210833605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18328375353871836807222403 27492563030807755210833605)
                  ·
                    refine ⟨5154855568276454102031301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27492563030807755210833605 5154855568276454102031301)
                    ·
                      refine ⟨966535419051835144130869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5154855568276454102031301 966535419051835144130869)
                      ·
                        rfl

theorem cell23_1882321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1882321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882321 prefixEnd_1882321 := by exact prefixLift 1882321
  have htrace : WordTrace (prefixWord ++ tailWord_1882321) baseStart_1882321 baseEnd_1882321 := by
    simpa [prefixWord, tailWord_1882321, baseEnd_1882321] using wordTrace_append hprefix tailTrace_1882321
  have hstable : (prefixWord ++ tailWord_1882321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882321).length < 2 ^ (prefixWord ++ tailWord_1882321).sum := by decide
  have hdescent : baseEnd_1882321 < baseStart_1882321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882328 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1882328 : Nat := 118140960795 + 1882328 * 2 ^ 59
def prefixEnd_1882328 : Nat := 4983230072969 + 3 ^ 40 * 1882328 * 2
def baseEnd_1882328 : Nat := 966539013416416616743337

theorem tailTrace_1882328 : CollatzResearch.WordTrace tailWord_1882328 prefixEnd_1882328 966539013416416616743337 := by
  unfold tailWord_1882328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34327071162327303436747819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45769428216436404582330425 34327071162327303436747819)
  ·
    refine ⟨51490606743490955155121729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34327071162327303436747819 51490606743490955155121729)
    ·
      refine ⟨38617955057618216366341297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51490606743490955155121729 38617955057618216366341297)
      ·
        refine ⟨28963466293213662274755973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38617955057618216366341297 28963466293213662274755973)
        ·
          refine ⟨5430649929977561676516745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28963466293213662274755973 5430649929977561676516745)
          ·
            refine ⟨4072987447483171257387559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430649929977561676516745 4072987447483171257387559)
            ·
              refine ⟨6109481171224756886081339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072987447483171257387559 6109481171224756886081339)
              ·
                refine ⟨9164221756837135329122009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109481171224756886081339 9164221756837135329122009)
                ·
                  refine ⟨6873166317627851496841507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164221756837135329122009 6873166317627851496841507)
                  ·
                    refine ⟨10309749476441777245262261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873166317627851496841507 10309749476441777245262261)
                    ·
                      refine ⟨966539013416416616743337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10309749476441777245262261 966539013416416616743337)
                      ·
                        rfl

theorem cell23_1882328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1882328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882328 prefixEnd_1882328 := by exact prefixLift 1882328
  have htrace : WordTrace (prefixWord ++ tailWord_1882328) baseStart_1882328 baseEnd_1882328 := by
    simpa [prefixWord, tailWord_1882328, baseEnd_1882328] using wordTrace_append hprefix tailTrace_1882328
  have hstable : (prefixWord ++ tailWord_1882328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882328).length < 2 ^ (prefixWord ++ tailWord_1882328).sum := by decide
  have hdescent : baseEnd_1882328 < baseStart_1882328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882361 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_1882361 : Nat := 118140960795 + 1882361 * 2 ^ 59
def prefixEnd_1882361 : Nat := 4983230072969 + 3 ^ 40 * 1882361 * 2
def baseEnd_1882361 : Nat := 322185319426004995876895

theorem tailTrace_1882361 : CollatzResearch.WordTrace tailWord_1882361 prefixEnd_1882361 322185319426004995876895 := by
  unfold tailWord_1882361
  simp only [CollatzResearch.WordTrace]
  refine ⟨68655345933535053509446937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45770230622356702339631291 68655345933535053509446937)
  ·
    refine ⟨51491509450151290132085203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68655345933535053509446937 51491509450151290132085203)
    ·
      refine ⟨77237264175226935198127805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51491509450151290132085203 77237264175226935198127805)
      ·
        refine ⟨28963974065710100699297927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77237264175226935198127805 28963974065710100699297927)
        ·
          refine ⟨43445961098565151048946891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28963974065710100699297927 43445961098565151048946891)
          ·
            refine ⟨65168941647847726573420337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43445961098565151048946891 65168941647847726573420337)
            ·
              refine ⟨48876706235885794930065253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65168941647847726573420337 48876706235885794930065253)
              ·
                refine ⟨9164382419228586549387235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48876706235885794930065253 9164382419228586549387235)
                ·
                  refine ⟨13746573628842879824080853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164382419228586549387235 13746573628842879824080853)
                  ·
                    refine ⟨322185319426004995876895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13746573628842879824080853 322185319426004995876895)
                    ·
                      rfl

theorem cell23_1882361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_1882361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882361 prefixEnd_1882361 := by exact prefixLift 1882361
  have htrace : WordTrace (prefixWord ++ tailWord_1882361) baseStart_1882361 baseEnd_1882361 := by
    simpa [prefixWord, tailWord_1882361, baseEnd_1882361] using wordTrace_append hprefix tailTrace_1882361
  have hstable : (prefixWord ++ tailWord_1882361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882361).length < 2 ^ (prefixWord ++ tailWord_1882361).sum := by decide
  have hdescent : baseEnd_1882361 < baseStart_1882361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882371 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_1882371 : Nat := 118140960795 + 1882371 * 2 ^ 59
def prefixEnd_1882371 : Nat := 4983230072969 + 3 ^ 40 * 1882371 * 2
def baseEnd_1882371 : Nat := 966561093084559948505639

theorem tailTrace_1882371 : CollatzResearch.WordTrace tailWord_1882371 prefixEnd_1882371 966561093084559948505639 := by
  unfold tailWord_1882371
  simp only [CollatzResearch.WordTrace]
  refine ⟨68655710663498825217310967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45770473775665883478207311 68655710663498825217310967)
  ·
    refine ⟨102983565995248237825966451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68655710663498825217310967 102983565995248237825966451)
    ·
      refine ⟨154475348992872356738949677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102983565995248237825966451 154475348992872356738949677)
      ·
        refine ⟨57928255872327133777106129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154475348992872356738949677 57928255872327133777106129)
        ·
          refine ⟨43446191904245350332829597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57928255872327133777106129 43446191904245350332829597)
          ·
            refine ⟨16292321964092006374811099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43446191904245350332829597 16292321964092006374811099)
            ·
              refine ⟨24438482946138009562216649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292321964092006374811099 24438482946138009562216649)
              ·
                refine ⟨18328862209603507171662487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24438482946138009562216649 18328862209603507171662487)
                ·
                  refine ⟨27493293314405260757493731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18328862209603507171662487 27493293314405260757493731)
                  ·
                    refine ⟨41239939971607891136240597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27493293314405260757493731 41239939971607891136240597)
                    ·
                      refine ⟨966561093084559948505639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41239939971607891136240597 966561093084559948505639)
                      ·
                        rfl

theorem cell23_1882371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_1882371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882371 prefixEnd_1882371 := by exact prefixLift 1882371
  have htrace : WordTrace (prefixWord ++ tailWord_1882371) baseStart_1882371 baseEnd_1882371 := by
    simpa [prefixWord, tailWord_1882371, baseEnd_1882371] using wordTrace_append hprefix tailTrace_1882371
  have hstable : (prefixWord ++ tailWord_1882371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882371).length < 2 ^ (prefixWord ++ tailWord_1882371).sum := by decide
  have hdescent : baseEnd_1882371 < baseStart_1882371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882378 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1882378 : Nat := 118140960795 + 1882378 * 2 ^ 59
def prefixEnd_1882378 : Nat := 4983230072969 + 3 ^ 40 * 1882378 * 2
def baseEnd_1882378 : Nat := 322188229149713807039369

theorem tailTrace_1882378 : CollatzResearch.WordTrace tailWord_1882378 prefixEnd_1882378 322188229149713807039369 := by
  unfold tailWord_1882378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163991493618366353203947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45770643982982310275210525 17163991493618366353203947)
  ·
    refine ⟨25745987240427549529805921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17163991493618366353203947 25745987240427549529805921)
    ·
      refine ⟨19309490430320662147354441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25745987240427549529805921 19309490430320662147354441)
      ·
        refine ⟨14482117822740496610515831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19309490430320662147354441 14482117822740496610515831)
        ·
          refine ⟨21723176734110744915773747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482117822740496610515831 21723176734110744915773747)
          ·
            refine ⟨32584765101166117373660621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21723176734110744915773747 32584765101166117373660621)
            ·
              refine ⟨12219286912937294015122733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32584765101166117373660621 12219286912937294015122733)
              ·
                refine ⟨4582232592351485255671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12219286912937294015122733 4582232592351485255671025)
                ·
                  refine ⟨3436674444263613941753269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4582232592351485255671025 3436674444263613941753269)
                  ·
                    refine ⟨322188229149713807039369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3436674444263613941753269 322188229149713807039369)
                    ·
                      rfl

theorem cell23_1882378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1882378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882378 prefixEnd_1882378 := by exact prefixLift 1882378
  have htrace : WordTrace (prefixWord ++ tailWord_1882378) baseStart_1882378 baseEnd_1882378 := by
    simpa [prefixWord, tailWord_1882378, baseEnd_1882378] using wordTrace_append hprefix tailTrace_1882378
  have hstable : (prefixWord ++ tailWord_1882378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882378).length < 2 ^ (prefixWord ++ tailWord_1882378).sum := by decide
  have hdescent : baseEnd_1882378 < baseStart_1882378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882425 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_1882425 : Nat := 118140960795 + 1882425 * 2 ^ 59
def prefixEnd_1882425 : Nat := 4983230072969 + 3 ^ 40 * 1882425 * 2
def baseEnd_1882425 : Nat := 322196273679967579076797

theorem tailTrace_1882425 : CollatzResearch.WordTrace tailWord_1882425 prefixEnd_1882425 322196273679967579076797 := by
  unfold tailWord_1882425
  simp only [CollatzResearch.WordTrace]
  refine ⟨68657680205303192439776729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45771786803535461626517819 68657680205303192439776729)
  ·
    refine ⟨51493260153977394329832547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68657680205303192439776729 51493260153977394329832547)
    ·
      refine ⟨77239890230966091494748821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51493260153977394329832547 77239890230966091494748821)
      ·
        refine ⟨3620619854576535538816351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77239890230966091494748821 3620619854576535538816351)
        ·
          refine ⟨5430929781864803308224527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620619854576535538816351 5430929781864803308224527)
          ·
            refine ⟨8146394672797204962336791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430929781864803308224527 8146394672797204962336791)
            ·
              refine ⟨12219592009195807443505187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146394672797204962336791 12219592009195807443505187)
              ·
                refine ⟨18329388013793711165257781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12219592009195807443505187 18329388013793711165257781)
                ·
                  refine ⟨1718380126293160421742917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18329388013793711165257781 1718380126293160421742917)
                  ·
                    refine ⟨322196273679967579076797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718380126293160421742917 322196273679967579076797)
                    ·
                      rfl

theorem cell23_1882425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_1882425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882425 prefixEnd_1882425 := by exact prefixLift 1882425
  have htrace : WordTrace (prefixWord ++ tailWord_1882425) baseStart_1882425 baseEnd_1882425 := by
    simpa [prefixWord, tailWord_1882425, baseEnd_1882425] using wordTrace_append hprefix tailTrace_1882425
  have hstable : (prefixWord ++ tailWord_1882425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882425).length < 2 ^ (prefixWord ++ tailWord_1882425).sum := by decide
  have hdescent : baseEnd_1882425 < baseStart_1882425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882435 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3]
def baseStart_1882435 : Nat := 118140960795 + 1882435 * 2 ^ 59
def prefixEnd_1882435 : Nat := 4983230072969 + 3 ^ 40 * 1882435 * 2
def baseEnd_1882435 : Nat := 966593955846447698105345

theorem tailTrace_1882435 : CollatzResearch.WordTrace tailWord_1882435 prefixEnd_1882435 966593955846447698105345 := by
  unfold tailWord_1882435
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658044935266964147640759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45772029956844642765093839 68658044935266964147640759)
  ·
    refine ⟨102987067402900446221461139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658044935266964147640759 102987067402900446221461139)
    ·
      refine ⟨154480601104350669332191709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102987067402900446221461139 154480601104350669332191709)
      ·
        refine ⟨57930225414131500999571891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154480601104350669332191709 57930225414131500999571891)
        ·
          refine ⟨86895338121197251499357837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57930225414131500999571891 86895338121197251499357837)
          ·
            refine ⟨32585751795448969312259189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86895338121197251499357837 32585751795448969312259189)
            ·
              refine ⟨3054914230823340873024299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32585751795448969312259189 3054914230823340873024299)
              ·
                refine ⟨4582371346235011309536449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054914230823340873024299 4582371346235011309536449)
                ·
                  refine ⟨3436778509676258482152337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4582371346235011309536449 3436778509676258482152337)
                  ·
                    refine ⟨2577583882257193861614253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436778509676258482152337 2577583882257193861614253)
                    ·
                      refine ⟨966593955846447698105345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577583882257193861614253 966593955846447698105345)
                      ·
                        rfl

theorem cell23_1882435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_1882435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882435 prefixEnd_1882435 := by exact prefixLift 1882435
  have htrace : WordTrace (prefixWord ++ tailWord_1882435) baseStart_1882435 baseEnd_1882435 := by
    simpa [prefixWord, tailWord_1882435, baseEnd_1882435] using wordTrace_append hprefix tailTrace_1882435
  have hstable : (prefixWord ++ tailWord_1882435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882435).length < 2 ^ (prefixWord ++ tailWord_1882435).sum := by decide
  have hdescent : baseEnd_1882435 < baseStart_1882435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882472 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 6]
def baseStart_1882472 : Nat := 118140960795 + 1882472 * 2 ^ 59
def prefixEnd_1882472 : Nat := 4983230072969 + 3 ^ 40 * 1882472 * 2
def baseEnd_1882472 : Nat := 107401439403407117038075

theorem tailTrace_1882472 : CollatzResearch.WordTrace tailWord_1882472 prefixEnd_1882472 107401439403407117038075 := by
  unfold tailWord_1882472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34329697218066459733368835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45772929624088612977825113 34329697218066459733368835)
  ·
    refine ⟨51494545827099689600053253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34329697218066459733368835 51494545827099689600053253)
    ·
      refine ⟨9655227342581191800009985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51494545827099689600053253 9655227342581191800009985)
      ·
        refine ⟨7241420506935893850007489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655227342581191800009985 7241420506935893850007489)
        ·
          refine ⟨5431065380201920387505617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7241420506935893850007489 5431065380201920387505617)
          ·
            refine ⟨4073299035151440290629213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5431065380201920387505617 4073299035151440290629213)
            ·
              refine ⟨1527487138181790108985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4073299035151440290629213 1527487138181790108985955)
              ·
                refine ⟨2291230707272685163478933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527487138181790108985955 2291230707272685163478933)
                ·
                  refine ⟨107401439403407117038075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2291230707272685163478933 107401439403407117038075)
                  ·
                    rfl

theorem cell23_1882472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 6].length) (baseStart_1882472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882472 prefixEnd_1882472 := by exact prefixLift 1882472
  have htrace : WordTrace (prefixWord ++ tailWord_1882472) baseStart_1882472 baseEnd_1882472 := by
    simpa [prefixWord, tailWord_1882472, baseEnd_1882472] using wordTrace_append hprefix tailTrace_1882472
  have hstable : (prefixWord ++ tailWord_1882472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882472).length < 2 ^ (prefixWord ++ tailWord_1882472).sum := by decide
  have hdescent : baseEnd_1882472 < baseStart_1882472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882475 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 3, 2]
def baseStart_1882475 : Nat := 118140960795 + 1882475 * 2 ^ 59
def prefixEnd_1882475 : Nat := 4983230072969 + 3 ^ 40 * 1882475 * 2
def baseEnd_1882475 : Nat := 966614495072627541605161

theorem tailTrace_1882475 : CollatzResearch.WordTrace tailWord_1882475 prefixEnd_1882475 966614495072627541605161 := by
  unfold tailWord_1882475
  simp only [CollatzResearch.WordTrace]
  refine ⟨68659503855122050979096879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45773002570081367319397919 68659503855122050979096879)
  ·
    refine ⟨102989255782683076468645319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68659503855122050979096879 102989255782683076468645319)
    ·
      refine ⟨154483883674024614702967979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102989255782683076468645319 154483883674024614702967979)
      ·
        refine ⟨231725825511036922054451969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154483883674024614702967979 231725825511036922054451969)
        ·
          refine ⟨173794369133277691540838977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231725825511036922054451969 173794369133277691540838977)
          ·
            refine ⟨130345776849958268655629233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173794369133277691540838977 130345776849958268655629233)
            ·
              refine ⟨97759332637468701491721925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130345776849958268655629233 97759332637468701491721925)
              ·
                refine ⟨18329874869525381529697861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97759332637468701491721925 18329874869525381529697861)
                ·
                  refine ⟨3436851538036009036818349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18329874869525381529697861 3436851538036009036818349)
                  ·
                    refine ⟨1288819326763503388806881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436851538036009036818349 1288819326763503388806881)
                    ·
                      refine ⟨966614495072627541605161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288819326763503388806881 966614495072627541605161)
                      ·
                        rfl

theorem cell23_1882475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3, 2].length) (baseStart_1882475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882475 prefixEnd_1882475 := by exact prefixLift 1882475
  have htrace : WordTrace (prefixWord ++ tailWord_1882475) baseStart_1882475 baseEnd_1882475 := by
    simpa [prefixWord, tailWord_1882475, baseEnd_1882475] using wordTrace_append hprefix tailTrace_1882475
  have hstable : (prefixWord ++ tailWord_1882475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882475).length < 2 ^ (prefixWord ++ tailWord_1882475).sum := by decide
  have hdescent : baseEnd_1882475 < baseStart_1882475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882482 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1882482 : Nat := 118140960795 + 1882482 * 2 ^ 59
def prefixEnd_1882482 : Nat := 4983230072969 + 3 ^ 40 * 1882482 * 2
def baseEnd_1882482 : Nat := 966618089437209014217629

theorem tailTrace_1882482 : CollatzResearch.WordTrace tailWord_1882482 prefixEnd_1882482 966618089437209014217629 := by
  unfold tailWord_1882482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164939791524172793650425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45773172777397794116401133 17164939791524172793650425)
  ·
    refine ⟨12873704843643129595237819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17164939791524172793650425 12873704843643129595237819)
    ·
      refine ⟨19310557265464694392856729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12873704843643129595237819 19310557265464694392856729)
      ·
        refine ⟨14482917949098520794642547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19310557265464694392856729 14482917949098520794642547)
        ·
          refine ⟨21724376923647781191963821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482917949098520794642547 21724376923647781191963821)
          ·
            refine ⟨8146641346367917946986433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21724376923647781191963821 8146641346367917946986433)
            ·
              refine ⟨6109981009775938460239825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8146641346367917946986433 6109981009775938460239825)
              ·
                refine ⟨4582485757331953845179869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109981009775938460239825 4582485757331953845179869)
                ·
                  refine ⟨1718432158999482691942451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4582485757331953845179869 1718432158999482691942451)
                  ·
                    refine ⟨2577648238499224037913677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1718432158999482691942451 2577648238499224037913677)
                    ·
                      refine ⟨966618089437209014217629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577648238499224037913677 966618089437209014217629)
                      ·
                        rfl

theorem cell23_1882482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1882482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882482 prefixEnd_1882482 := by exact prefixLift 1882482
  have htrace : WordTrace (prefixWord ++ tailWord_1882482) baseStart_1882482 baseEnd_1882482 := by
    simpa [prefixWord, tailWord_1882482, baseEnd_1882482] using wordTrace_append hprefix tailTrace_1882482
  have hstable : (prefixWord ++ tailWord_1882482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882482).length < 2 ^ (prefixWord ++ tailWord_1882482).sum := by decide
  have hdescent : baseEnd_1882482 < baseStart_1882482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882516 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1882516 : Nat := 118140960795 + 1882516 * 2 ^ 59
def prefixEnd_1882516 : Nat := 4983230072969 + 3 ^ 40 * 1882516 * 2
def baseEnd_1882516 : Nat := 966635547779461881192473

theorem tailTrace_1882516 : CollatzResearch.WordTrace tailWord_1882516 prefixEnd_1882516 966635547779461881192473 := by
  unfold tailWord_1882516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330499623986757490669701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45773999498649009987559601 34330499623986757490669701)
  ·
    refine ⟨6436968679497517029500569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34330499623986757490669701 6436968679497517029500569)
    ·
      refine ⟨4827726509623137772125427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6436968679497517029500569 4827726509623137772125427)
      ·
        refine ⟨7241589764434706658188141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827726509623137772125427 7241589764434706658188141)
        ·
          refine ⟨2715596161663014996820553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7241589764434706658188141 2715596161663014996820553)
          ·
            refine ⟨2036697121247261247615415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715596161663014996820553 2036697121247261247615415)
            ·
              refine ⟨3055045681870891871423123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036697121247261247615415 3055045681870891871423123)
              ·
                refine ⟨4582568522806337807134685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055045681870891871423123 4582568522806337807134685)
                ·
                  refine ⟨1718463196052376677675507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4582568522806337807134685 1718463196052376677675507)
                  ·
                    refine ⟨2577694794078565016513261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1718463196052376677675507 2577694794078565016513261)
                    ·
                      refine ⟨966635547779461881192473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577694794078565016513261 966635547779461881192473)
                      ·
                        rfl

theorem cell23_1882516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1882516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882516 prefixEnd_1882516 := by exact prefixLift 1882516
  have htrace : WordTrace (prefixWord ++ tailWord_1882516) baseStart_1882516 baseEnd_1882516 := by
    simpa [prefixWord, tailWord_1882516, baseEnd_1882516] using wordTrace_append hprefix tailTrace_1882516
  have hstable : (prefixWord ++ tailWord_1882516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882516).length < 2 ^ (prefixWord ++ tailWord_1882516).sum := by decide
  have hdescent : baseEnd_1882516 < baseStart_1882516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882528 : List Nat := [2, 1, 1, 4, 1, 3, 1, 10]
def baseStart_1882528 : Nat := 118140960795 + 1882528 * 2 ^ 59
def prefixEnd_1882528 : Nat := 4983230072969 + 3 ^ 40 * 1882528 * 2
def baseEnd_1882528 : Nat := 35801544798048734601571

theorem tailTrace_1882528 : CollatzResearch.WordTrace tailWord_1882528 prefixEnd_1882528 35801544798048734601571 := by
  unfold tailWord_1882528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330718461965020515388119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45774291282620027353850825 34330718461965020515388119)
  ·
    refine ⟨51496077692947530773082179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34330718461965020515388119 51496077692947530773082179)
    ·
      refine ⟨77244116539421296159623269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51496077692947530773082179 77244116539421296159623269)
      ·
        refine ⟨14483271851141493029929363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77244116539421296159623269 14483271851141493029929363)
        ·
          refine ⟨21724907776712239544894045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14483271851141493029929363 21724907776712239544894045)
          ·
            refine ⟨8146840416267089829335267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21724907776712239544894045 8146840416267089829335267)
            ·
              refine ⟨12220260624400634744002901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146840416267089829335267 12220260624400634744002901)
              ·
                refine ⟨35801544798048734601571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12220260624400634744002901 35801544798048734601571)
                ·
                  rfl

theorem cell23_1882528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 10].length) (baseStart_1882528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882528 prefixEnd_1882528 := by exact prefixLift 1882528
  have htrace : WordTrace (prefixWord ++ tailWord_1882528) baseStart_1882528 baseEnd_1882528 := by
    simpa [prefixWord, tailWord_1882528, baseEnd_1882528] using wordTrace_append hprefix tailTrace_1882528
  have hstable : (prefixWord ++ tailWord_1882528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882528).length < 2 ^ (prefixWord ++ tailWord_1882528).sum := by decide
  have hdescent : baseEnd_1882528 < baseStart_1882528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882535 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1882535 : Nat := 118140960795 + 1882535 * 2 ^ 59
def prefixEnd_1882535 : Nat := 4983230072969 + 3 ^ 40 * 1882535 * 2
def baseEnd_1882535 : Nat := 966645303911897306854885

theorem tailTrace_1882535 : CollatzResearch.WordTrace tailWord_1882535 prefixEnd_1882535 966645303911897306854885 := by
  unfold tailWord_1882535
  simp only [CollatzResearch.WordTrace]
  refine ⟨68661692234904681226281059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45774461489936454150854039 68661692234904681226281059)
  ·
    refine ⟨102992538352357021839421589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68661692234904681226281059 102992538352357021839421589)
    ·
      refine ⟨4827775235266735398722887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102992538352357021839421589 4827775235266735398722887)
      ·
        refine ⟨7241662852900103098084331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827775235266735398722887 7241662852900103098084331)
        ·
          refine ⟨10862494279350154647126497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241662852900103098084331 10862494279350154647126497)
          ·
            refine ⟨8146870709512615985344873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10862494279350154647126497 8146870709512615985344873)
            ·
              refine ⟨6110153032134461989008655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8146870709512615985344873 6110153032134461989008655)
              ·
                refine ⟨9165229548201692983512983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110153032134461989008655 9165229548201692983512983)
                ·
                  refine ⟨13747844322302539475269475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165229548201692983512983 13747844322302539475269475)
                  ·
                    refine ⟨20621766483453809212904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13747844322302539475269475 20621766483453809212904213)
                    ·
                      refine ⟨966645303911897306854885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20621766483453809212904213 966645303911897306854885)
                      ·
                        rfl

theorem cell23_1882535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1882535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882535 prefixEnd_1882535 := by exact prefixLift 1882535
  have htrace : WordTrace (prefixWord ++ tailWord_1882535) baseStart_1882535 baseEnd_1882535 := by
    simpa [prefixWord, tailWord_1882535, baseEnd_1882535] using wordTrace_append hprefix tailTrace_1882535
  have hstable : (prefixWord ++ tailWord_1882535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882535).length < 2 ^ (prefixWord ++ tailWord_1882535).sum := by decide
  have hdescent : baseEnd_1882535 < baseStart_1882535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882562 : List Nat := [3, 5, 2, 13]
def baseStart_1882562 : Nat := 118140960795 + 1882562 * 2 ^ 59
def prefixEnd_1882562 : Nat := 4983230072969 + 3 ^ 40 * 1882562 * 2
def baseEnd_1882562 : Nat := 442002363003918016103

theorem tailTrace_1882562 : CollatzResearch.WordTrace tailWord_1882562 prefixEnd_1882562 442002363003918016103 := by
  unfold tailWord_1882562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17165669251451716209378485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45775118003871243225009293 17165669251451716209378485)
  ·
    refine ⟨1609281492323598394629233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17165669251451716209378485 1609281492323598394629233)
    ·
      refine ⟨1206961119242698795971925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1609281492323598394629233 1206961119242698795971925)
      ·
        refine ⟨442002363003918016103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1206961119242698795971925 442002363003918016103)
        ·
          rfl

theorem cell23_1882562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 13].length) (baseStart_1882562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882562 prefixEnd_1882562 := by exact prefixLift 1882562
  have htrace : WordTrace (prefixWord ++ tailWord_1882562) baseStart_1882562 baseEnd_1882562 := by
    simpa [prefixWord, tailWord_1882562, baseEnd_1882562] using wordTrace_append hprefix tailTrace_1882562
  have hstable : (prefixWord ++ tailWord_1882562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882562).length < 2 ^ (prefixWord ++ tailWord_1882562).sum := by decide
  have hdescent : baseEnd_1882562 < baseStart_1882562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882589 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1882589 : Nat := 118140960795 + 1882589 * 2 ^ 59
def prefixEnd_1882589 : Nat := 4983230072969 + 3 ^ 40 * 1882589 * 2
def baseEnd_1882589 : Nat := 966673031867240095579637

theorem tailTrace_1882589 : CollatzResearch.WordTrace tailWord_1882589 prefixEnd_1882589 966673031867240095579637 := by
  unfold tailWord_1882589
  simp only [CollatzResearch.WordTrace]
  refine ⟨68663661776709048448746821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45775774517806032299164547 68663661776709048448746821)
  ·
    refine ⟨12874436583132946584140029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68663661776709048448746821 12874436583132946584140029)
    ·
      refine ⟨4827913718674854969052511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12874436583132946584140029 4827913718674854969052511)
      ·
        refine ⟨7241870578012282453578767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827913718674854969052511 7241870578012282453578767)
        ·
          refine ⟨10862805867018423680368151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241870578012282453578767 10862805867018423680368151)
          ·
            refine ⟨16294208800527635520552227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862805867018423680368151 16294208800527635520552227)
            ·
              refine ⟨24441313200791453280828341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16294208800527635520552227 24441313200791453280828341)
              ·
                refine ⟨2291373112574198745077657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24441313200791453280828341 2291373112574198745077657)
                ·
                  refine ⟨1718529834430649058808243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2291373112574198745077657 1718529834430649058808243)
                  ·
                    refine ⟨2577794751645973588212365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1718529834430649058808243 2577794751645973588212365)
                    ·
                      refine ⟨966673031867240095579637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2577794751645973588212365 966673031867240095579637)
                      ·
                        rfl

theorem cell23_1882589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1882589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882589 prefixEnd_1882589 := by exact prefixLift 1882589
  have htrace : WordTrace (prefixWord ++ tailWord_1882589) baseStart_1882589 baseEnd_1882589 := by
    simpa [prefixWord, tailWord_1882589, baseEnd_1882589] using wordTrace_append hprefix tailTrace_1882589
  have hstable : (prefixWord ++ tailWord_1882589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882589).length < 2 ^ (prefixWord ++ tailWord_1882589).sum := by decide
  have hdescent : baseEnd_1882589 < baseStart_1882589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882599 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1882599 : Nat := 118140960795 + 1882599 * 2 ^ 59
def prefixEnd_1882599 : Nat := 4983230072969 + 3 ^ 40 * 1882599 * 2
def baseEnd_1882599 : Nat := 966678166673785056454591

theorem tailTrace_1882599 : CollatzResearch.WordTrace tailWord_1882599 prefixEnd_1882599 966678166673785056454591 := by
  unfold tailWord_1882599
  simp only [CollatzResearch.WordTrace]
  refine ⟨68664026506672820156610851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45776017671115213437740567 68664026506672820156610851)
  ·
    refine ⟨102996039760009230234916277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68664026506672820156610851 102996039760009230234916277)
    ·
      refine ⟨9655878727500865334523401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102996039760009230234916277 9655878727500865334523401)
      ·
        refine ⟨7241909045625649000892551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655878727500865334523401 7241909045625649000892551)
        ·
          refine ⟨10862863568438473501338827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241909045625649000892551 10862863568438473501338827)
          ·
            refine ⟨16294295352657710252008241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862863568438473501338827 16294295352657710252008241)
            ·
              refine ⟨12220721514493282689006181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16294295352657710252008241 12220721514493282689006181)
              ·
                refine ⟨2291385283967490504188659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12220721514493282689006181 2291385283967490504188659)
                ·
                  refine ⟨3437077925951235756282989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291385283967490504188659 3437077925951235756282989)
                  ·
                    refine ⟨1288904222231713408606121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437077925951235756282989 1288904222231713408606121)
                    ·
                      refine ⟨966678166673785056454591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1288904222231713408606121 966678166673785056454591)
                      ·
                        rfl

theorem cell23_1882599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1882599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882599 prefixEnd_1882599 := by exact prefixLift 1882599
  have htrace : WordTrace (prefixWord ++ tailWord_1882599) baseStart_1882599 baseEnd_1882599 := by
    simpa [prefixWord, tailWord_1882599, baseEnd_1882599] using wordTrace_append hprefix tailTrace_1882599
  have hstable : (prefixWord ++ tailWord_1882599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882599).length < 2 ^ (prefixWord ++ tailWord_1882599).sum := by decide
  have hdescent : baseEnd_1882599 < baseStart_1882599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882635 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 7]
def baseStart_1882635 : Nat := 118140960795 + 1882635 * 2 ^ 59
def prefixEnd_1882635 : Nat := 4983230072969 + 3 ^ 40 * 1882635 * 2
def baseEnd_1882635 : Nat := 107410739108594101733825

theorem tailTrace_1882635 : CollatzResearch.WordTrace tailWord_1882635 prefixEnd_1882635 107410739108594101733825 := by
  unfold tailWord_1882635
  simp only [CollatzResearch.WordTrace]
  refine ⟨68665339534542398304921359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45776893023028265536614239 68665339534542398304921359)
  ·
    refine ⟨102998009301813597457382039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68665339534542398304921359 102998009301813597457382039)
    ·
      refine ⟨154497013952720396186073059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102998009301813597457382039 154497013952720396186073059)
      ·
        refine ⟨231745520929080594279109589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154497013952720396186073059 231745520929080594279109589)
        ·
          refine ⟨5431535646775326428416631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 231745520929080594279109589 5431535646775326428416631)
          ·
            refine ⟨8147303470162989642624947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431535646775326428416631 8147303470162989642624947)
            ·
              refine ⟨12220955205244484463937421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8147303470162989642624947 12220955205244484463937421)
              ·
                refine ⟨4582858201966681673976533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12220955205244484463937421 4582858201966681673976533)
                ·
                  refine ⟨107410739108594101733825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4582858201966681673976533 107410739108594101733825)
                  ·
                    rfl

theorem cell23_1882635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 7].length) (baseStart_1882635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882635 prefixEnd_1882635 := by exact prefixLift 1882635
  have htrace : WordTrace (prefixWord ++ tailWord_1882635) baseStart_1882635 baseEnd_1882635 := by
    simpa [prefixWord, tailWord_1882635, baseEnd_1882635] using wordTrace_append hprefix tailTrace_1882635
  have hstable : (prefixWord ++ tailWord_1882635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882635).length < 2 ^ (prefixWord ++ tailWord_1882635).sum := by decide
  have hdescent : baseEnd_1882635 < baseStart_1882635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882675 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_1882675 : Nat := 118140960795 + 1882675 * 2 ^ 59
def prefixEnd_1882675 : Nat := 4983230072969 + 3 ^ 40 * 1882675 * 2
def baseEnd_1882675 : Nat := 966717191203526759104241

theorem tailTrace_1882675 : CollatzResearch.WordTrace tailWord_1882675 prefixEnd_1882675 966717191203526759104241 := by
  unfold tailWord_1882675
  simp only [CollatzResearch.WordTrace]
  refine ⟨68666798454397485136377479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45777865636264990090918319 68666798454397485136377479)
  ·
    refine ⟨103000197681596227704566219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68666798454397485136377479 103000197681596227704566219)
    ·
      refine ⟨154500296522394341556849329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103000197681596227704566219 154500296522394341556849329)
      ·
        refine ⟨115875222391795756167636997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154500296522394341556849329 115875222391795756167636997)
        ·
          refine ⟨21726604198461704281431937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115875222391795756167636997 21726604198461704281431937)
          ·
            refine ⟨16294953148846278211073953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21726604198461704281431937 16294953148846278211073953)
            ·
              refine ⟨12221214861634708658305465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16294953148846278211073953 12221214861634708658305465)
              ·
                refine ⟨9165911146226031493729099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12221214861634708658305465 9165911146226031493729099)
                ·
                  refine ⟨13748866719339047240593649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165911146226031493729099 13748866719339047240593649)
                  ·
                    refine ⟨10311650039504285430445237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13748866719339047240593649 10311650039504285430445237)
                    ·
                      refine ⟨966717191203526759104241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10311650039504285430445237 966717191203526759104241)
                      ·
                        rfl

theorem cell23_1882675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_1882675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882675 prefixEnd_1882675 := by exact prefixLift 1882675
  have htrace : WordTrace (prefixWord ++ tailWord_1882675) baseStart_1882675 baseEnd_1882675 := by
    simpa [prefixWord, tailWord_1882675, baseEnd_1882675] using wordTrace_append hprefix tailTrace_1882675
  have hstable : (prefixWord ++ tailWord_1882675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882675).length < 2 ^ (prefixWord ++ tailWord_1882675).sum := by decide
  have hdescent : baseEnd_1882675 < baseStart_1882675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882682 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1882682 : Nat := 118140960795 + 1882682 * 2 ^ 59
def prefixEnd_1882682 : Nat := 4983230072969 + 3 ^ 40 * 1882682 * 2
def baseEnd_1882682 : Nat := 322240261856036077238903

theorem tailTrace_1882682 : CollatzResearch.WordTrace tailWord_1882682 prefixEnd_1882682 322240261856036077238903 := by
  unfold tailWord_1882682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166763441343031332970575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45778035843581416887921533 17166763441343031332970575)
  ·
    refine ⟨25750145162014546999455863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17166763441343031332970575 25750145162014546999455863)
    ·
      refine ⟨38625217743021820499183795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25750145162014546999455863 38625217743021820499183795)
      ·
        refine ⟨57937826614532730748775693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38625217743021820499183795 57937826614532730748775693)
        ·
          refine ⟨21726684980449774030790885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57937826614532730748775693 21726684980449774030790885)
          ·
            refine ⟨4073753433834332630773291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21726684980449774030790885 4073753433834332630773291)
            ·
              refine ⟨6110630150751498946159937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073753433834332630773291 6110630150751498946159937)
              ·
                refine ⟨4582972613063624209619953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110630150751498946159937 4582972613063624209619953)
                ·
                  refine ⟨3437229459797718157214965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4582972613063624209619953 3437229459797718157214965)
                  ·
                    refine ⟨322240261856036077238903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3437229459797718157214965 322240261856036077238903)
                    ·
                      rfl

theorem cell23_1882682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1882682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882682 prefixEnd_1882682 := by exact prefixLift 1882682
  have htrace : WordTrace (prefixWord ++ tailWord_1882682) baseStart_1882682 baseEnd_1882682 := by
    simpa [prefixWord, tailWord_1882682, baseEnd_1882682] using wordTrace_append hprefix tailTrace_1882682
  have hstable : (prefixWord ++ tailWord_1882682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882682).length < 2 ^ (prefixWord ++ tailWord_1882682).sum := by decide
  have hdescent : baseEnd_1882682 < baseStart_1882682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882686 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1882686 : Nat := 118140960795 + 1882686 * 2 ^ 59
def prefixEnd_1882686 : Nat := 4983230072969 + 3 ^ 40 * 1882686 * 2
def baseEnd_1882686 : Nat := 107413648832302912896299

theorem tailTrace_1882686 : CollatzResearch.WordTrace tailWord_1882686 prefixEnd_1882686 107413648832302912896299 := by
  unfold tailWord_1882686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583399957169704251878489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45778133104905089343351941 8583399957169704251878489)
  ·
    refine ⟨6437549967877278188908867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8583399957169704251878489 6437549967877278188908867)
    ·
      refine ⟨9656324951815917283363301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6437549967877278188908867 9656324951815917283363301)
      ·
        refine ⟨1810560928465484490630619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9656324951815917283363301 1810560928465484490630619)
        ·
          refine ⟨2715841392698226735945929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810560928465484490630619 2715841392698226735945929)
          ·
            refine ⟨2036881044523670051959447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715841392698226735945929 2036881044523670051959447)
            ·
              refine ⟨3055321566785505077939171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036881044523670051959447 3055321566785505077939171)
              ·
                refine ⟨4582982350178257616908757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055321566785505077939171 4582982350178257616908757)
                ·
                  refine ⟨107413648832302912896299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4582982350178257616908757 107413648832302912896299)
                  ·
                    rfl

theorem cell23_1882686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1882686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882686 prefixEnd_1882686 := by exact prefixLift 1882686
  have htrace : WordTrace (prefixWord ++ tailWord_1882686) baseStart_1882686 baseEnd_1882686 := by
    simpa [prefixWord, tailWord_1882686, baseEnd_1882686] using wordTrace_append hprefix tailTrace_1882686
  have hstable : (prefixWord ++ tailWord_1882686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882686).length < 2 ^ (prefixWord ++ tailWord_1882686).sum := by decide
  have hdescent : baseEnd_1882686 < baseStart_1882686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882712 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_1882712 : Nat := 118140960795 + 1882712 * 2 ^ 59
def prefixEnd_1882712 : Nat := 4983230072969 + 3 ^ 40 * 1882712 * 2
def baseEnd_1882712 : Nat := 322245396662581038113857

theorem tailTrace_1882712 : CollatzResearch.WordTrace tailWord_1882712 prefixEnd_1882712 322245396662581038113857 := by
  unfold tailWord_1882712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34334073977631720227737195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45778765303508960303649593 34334073977631720227737195)
  ·
    refine ⟨51501110966447580341605793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34334073977631720227737195 51501110966447580341605793)
    ·
      refine ⟨38625833224835685256204345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51501110966447580341605793 38625833224835685256204345)
      ·
        refine ⟨28969374918626763942153259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38625833224835685256204345 28969374918626763942153259)
        ·
          refine ⟨43454062377940145913229889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28969374918626763942153259 43454062377940145913229889)
          ·
            refine ⟨32590546783455109434922417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43454062377940145913229889 32590546783455109434922417)
            ·
              refine ⟨24442910087591332076191813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32590546783455109434922417 24442910087591332076191813)
              ·
                refine ⟨4583045641423374764285965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24442910087591332076191813 4583045641423374764285965)
                ·
                  refine ⟨1718642115533765536607237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4583045641423374764285965 1718642115533765536607237)
                  ·
                    refine ⟨322245396662581038113857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718642115533765536607237 322245396662581038113857)
                    ·
                      rfl

theorem cell23_1882712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_1882712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882712 prefixEnd_1882712 := by exact prefixLift 1882712
  have htrace : WordTrace (prefixWord ++ tailWord_1882712) baseStart_1882712 baseEnd_1882712 := by
    simpa [prefixWord, tailWord_1882712, baseEnd_1882712] using wordTrace_append hprefix tailTrace_1882712
  have hstable : (prefixWord ++ tailWord_1882712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882712).length < 2 ^ (prefixWord ++ tailWord_1882712).sum := by decide
  have hdescent : baseEnd_1882712 < baseStart_1882712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882729 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 1, 4]
def baseStart_1882729 : Nat := 118140960795 + 1882729 * 2 ^ 59
def prefixEnd_1882729 : Nat := 4983230072969 + 3 ^ 40 * 1882729 * 2
def baseEnd_1882729 : Nat := 322248306386289849276331

theorem tailTrace_1882729 : CollatzResearch.WordTrace tailWord_1882729 prefixEnd_1882729 322248306386289849276331 := by
  unfold tailWord_1882729
  simp only [CollatzResearch.WordTrace]
  refine ⟨68668767996201852358843241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45779178664134568239228827 68668767996201852358843241)
  ·
    refine ⟨51501575997151389269132431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68668767996201852358843241 51501575997151389269132431)
    ·
      refine ⟨77252363995727083903698647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51501575997151389269132431 77252363995727083903698647)
      ·
        refine ⟨115878545993590625855547971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77252363995727083903698647 115878545993590625855547971)
        ·
          refine ⟨173817818990385938783321957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115878545993590625855547971 173817818990385938783321957)
          ·
            refine ⟨32590841060697363521872867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173817818990385938783321957 32590841060697363521872867)
            ·
              refine ⟨48886261591046045282809301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32590841060697363521872867 48886261591046045282809301)
              ·
                refine ⟨1145771756040141686315843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48886261591046045282809301 1145771756040141686315843)
                ·
                  refine ⟨1718657634060212529473765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145771756040141686315843 1718657634060212529473765)
                  ·
                    refine ⟨322248306386289849276331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718657634060212529473765 322248306386289849276331)
                    ·
                      rfl

theorem cell23_1882729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 4].length) (baseStart_1882729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882729 prefixEnd_1882729 := by exact prefixLift 1882729
  have htrace : WordTrace (prefixWord ++ tailWord_1882729) baseStart_1882729 baseEnd_1882729 := by
    simpa [prefixWord, tailWord_1882729, baseEnd_1882729] using wordTrace_append hprefix tailTrace_1882729
  have hstable : (prefixWord ++ tailWord_1882729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882729).length < 2 ^ (prefixWord ++ tailWord_1882729).sum := by decide
  have hdescent : baseEnd_1882729 < baseStart_1882729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882826 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_1882826 : Nat := 118140960795 + 1882826 * 2 ^ 59
def prefixEnd_1882826 : Nat := 4983230072969 + 3 ^ 40 * 1882826 * 2
def baseEnd_1882826 : Nat := 966794726782355668316047

theorem tailTrace_1882826 : CollatzResearch.WordTrace tailWord_1882826 prefixEnd_1882826 966794726782355668316047 := by
  unfold tailWord_1882826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168076469212609481281083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45781537251233625283416221 17168076469212609481281083)
  ·
    refine ⟨25752114703818914221921625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17168076469212609481281083 25752114703818914221921625)
    ·
      refine ⟨19314086027864185666441219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25752114703818914221921625 19314086027864185666441219)
      ·
        refine ⟨28971129041796278499661829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19314086027864185666441219 28971129041796278499661829)
        ·
          refine ⟨5432086695336802218686593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28971129041796278499661829 5432086695336802218686593)
          ·
            refine ⟨4074065021502601664014945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5432086695336802218686593 4074065021502601664014945)
            ·
              refine ⟨3055548766126951248011209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074065021502601664014945 3055548766126951248011209)
              ·
                refine ⟨2291661574595213436008407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055548766126951248011209 2291661574595213436008407)
                ·
                  refine ⟨3437492361892820154012611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291661574595213436008407 3437492361892820154012611)
                  ·
                    refine ⟨5156238542839230231018917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3437492361892820154012611 5156238542839230231018917)
                    ·
                      refine ⟨966794726782355668316047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5156238542839230231018917 966794726782355668316047)
                      ·
                        rfl

theorem cell23_1882826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_1882826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882826 prefixEnd_1882826 := by exact prefixLift 1882826
  have htrace : WordTrace (prefixWord ++ tailWord_1882826) baseStart_1882826 baseEnd_1882826 := by
    simpa [prefixWord, tailWord_1882826, baseEnd_1882826] using wordTrace_append hprefix tailTrace_1882826
  have hstable : (prefixWord ++ tailWord_1882826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882826).length < 2 ^ (prefixWord ++ tailWord_1882826).sum := by decide
  have hdescent : baseEnd_1882826 < baseStart_1882826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882837 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1882837 : Nat := 118140960795 + 1882837 * 2 ^ 59
def prefixEnd_1882837 : Nat := 4983230072969 + 3 ^ 40 * 1882837 * 2
def baseEnd_1882837 : Nat := 966800375069555125278497

theorem tailTrace_1882837 : CollatzResearch.WordTrace tailWord_1882837 prefixEnd_1882837 966800375069555125278497 := by
  unfold tailWord_1882837
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672707079810586803774765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45781804719873724535849843 68672707079810586803774765)
  ·
    refine ⟨25752265154928970051415537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68672707079810586803774765 25752265154928970051415537)
    ·
      refine ⟨19314198866196727538561653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25752265154928970051415537 19314198866196727538561653)
      ·
        refine ⟨1810706143705943206740155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19314198866196727538561653 1810706143705943206740155)
        ·
          refine ⟨2716059215558914810110233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810706143705943206740155 2716059215558914810110233)
          ·
            refine ⟨2037044411669186107582675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2716059215558914810110233 2037044411669186107582675)
            ·
              refine ⟨3055566617503779161374013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037044411669186107582675 3055566617503779161374013)
              ·
                refine ⟨1145837481563917185515255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3055566617503779161374013 1145837481563917185515255)
                ·
                  refine ⟨1718756222345875778272883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145837481563917185515255 1718756222345875778272883)
                  ·
                    refine ⟨2578134333518813667409325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1718756222345875778272883 2578134333518813667409325)
                    ·
                      refine ⟨966800375069555125278497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2578134333518813667409325 966800375069555125278497)
                      ·
                        rfl

theorem cell23_1882837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1882837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882837 prefixEnd_1882837 := by exact prefixLift 1882837
  have htrace : WordTrace (prefixWord ++ tailWord_1882837) baseStart_1882837 baseEnd_1882837 := by
    simpa [prefixWord, tailWord_1882837, baseEnd_1882837] using wordTrace_append hprefix tailTrace_1882837
  have hstable : (prefixWord ++ tailWord_1882837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882837).length < 2 ^ (prefixWord ++ tailWord_1882837).sum := by decide
  have hdescent : baseEnd_1882837 < baseStart_1882837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882892 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1882892 : Nat := 118140960795 + 1882892 * 2 ^ 59
def prefixEnd_1882892 : Nat := 4983230072969 + 3 ^ 40 * 1882892 * 2
def baseEnd_1882892 : Nat := 322276205501850803363581

theorem tailTrace_1882892 : CollatzResearch.WordTrace tailWord_1882892 prefixEnd_1882892 322276205501850803363581 := by
  unfold tailWord_1882892
  simp only [CollatzResearch.WordTrace]
  refine ⟨34337356547305665598513465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45783142063074220798017953 34337356547305665598513465)
  ·
    refine ⟨25753017410479249198885099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34337356547305665598513465 25753017410479249198885099)
    ·
      refine ⟨38629526115718873798327649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25753017410479249198885099 38629526115718873798327649)
      ·
        refine ⟨28972144586789155348745737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38629526115718873798327649 28972144586789155348745737)
        ·
          refine ⟨21729108440091866511559303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28972144586789155348745737 21729108440091866511559303)
          ·
            refine ⟨32593662660137799767338955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21729108440091866511559303 32593662660137799767338955)
            ·
              refine ⟨48890493990206699651008433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32593662660137799767338955 48890493990206699651008433)
              ·
                refine ⟨36667870492655024738256325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48890493990206699651008433 36667870492655024738256325)
                ·
                  refine ⟨6875225717372817138423061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36667870492655024738256325 6875225717372817138423061)
                  ·
                    refine ⟨322276205501850803363581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6875225717372817138423061 322276205501850803363581)
                    ·
                      rfl

theorem cell23_1882892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1882892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882892 prefixEnd_1882892 := by exact prefixLift 1882892
  have htrace : WordTrace (prefixWord ++ tailWord_1882892) baseStart_1882892 baseEnd_1882892 := by
    simpa [prefixWord, tailWord_1882892, baseEnd_1882892] using wordTrace_append hprefix tailTrace_1882892
  have hstable : (prefixWord ++ tailWord_1882892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882892).length < 2 ^ (prefixWord ++ tailWord_1882892).sum := by decide
  have hdescent : baseEnd_1882892 < baseStart_1882892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882926 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1882926 : Nat := 118140960795 + 1882926 * 2 ^ 59
def prefixEnd_1882926 : Nat := 4983230072969 + 3 ^ 40 * 1882926 * 2
def baseEnd_1882926 : Nat := 322282024949268425688529

theorem tailTrace_1882926 : CollatzResearch.WordTrace tailWord_1882926 prefixEnd_1882926 322282024949268425688529 := by
  unfold tailWord_1882926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584494147061019375470579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45783968784325436669176421 8584494147061019375470579)
  ·
    refine ⟨12876741220591529063205869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8584494147061019375470579 12876741220591529063205869)
    ·
      refine ⟨4828777957721823398702201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12876741220591529063205869 4828777957721823398702201)
      ·
        refine ⟨3621583468291367549026651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828777957721823398702201 3621583468291367549026651)
        ·
          refine ⟨5432375202437051323539977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621583468291367549026651 5432375202437051323539977)
          ·
            refine ⟨4074281401827788492654983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5432375202437051323539977 4074281401827788492654983)
            ·
              refine ⟨6111422102741682738982475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074281401827788492654983 6111422102741682738982475)
              ·
                refine ⟨9167133154112524108473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111422102741682738982475 9167133154112524108473713)
                ·
                  refine ⟨6875349865584393081355285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167133154112524108473713 6875349865584393081355285)
                  ·
                    refine ⟨322282024949268425688529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6875349865584393081355285 322282024949268425688529)
                    ·
                      rfl

theorem cell23_1882926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1882926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882926 prefixEnd_1882926 := by exact prefixLift 1882926
  have htrace : WordTrace (prefixWord ++ tailWord_1882926) baseStart_1882926 baseEnd_1882926 := by
    simpa [prefixWord, tailWord_1882926, baseEnd_1882926] using wordTrace_append hprefix tailTrace_1882926
  have hstable : (prefixWord ++ tailWord_1882926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882926).length < 2 ^ (prefixWord ++ tailWord_1882926).sum := by decide
  have hdescent : baseEnd_1882926 < baseStart_1882926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882929 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1882929 : Nat := 118140960795 + 1882929 * 2 ^ 59
def prefixEnd_1882929 : Nat := 4983230072969 + 3 ^ 40 * 1882929 * 2
def baseEnd_1882929 : Nat := 966847615289768765328073

theorem tailTrace_1882929 : CollatzResearch.WordTrace tailWord_1882929 prefixEnd_1882929 966847615289768765328073 := by
  unfold tailWord_1882929
  simp only [CollatzResearch.WordTrace]
  refine ⟨68676062595477286516123841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45784041730318191010749227 68676062595477286516123841)
  ·
    refine ⟨51507046946607964887092881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68676062595477286516123841 51507046946607964887092881)
    ·
      refine ⟨38630285209955973665319661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51507046946607964887092881 38630285209955973665319661)
      ·
        refine ⟨14486356953733490124494873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38630285209955973665319661 14486356953733490124494873)
        ·
          refine ⟨10864767715300117593371155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14486356953733490124494873 10864767715300117593371155)
          ·
            refine ⟨16297151572950176390056733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864767715300117593371155 16297151572950176390056733)
            ·
              refine ⟨6111431839856316146271275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16297151572950176390056733 6111431839856316146271275)
              ·
                refine ⟨9167147759784474219406913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111431839856316146271275 9167147759784474219406913)
                ·
                  refine ⟨6875360819838355664555185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167147759784474219406913 6875360819838355664555185)
                  ·
                    refine ⟨5156520614878766748416389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6875360819838355664555185 5156520614878766748416389)
                    ·
                      refine ⟨966847615289768765328073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5156520614878766748416389 966847615289768765328073)
                      ·
                        rfl

theorem cell23_1882929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1882929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882929 prefixEnd_1882929 := by exact prefixLift 1882929
  have htrace : WordTrace (prefixWord ++ tailWord_1882929) baseStart_1882929 baseEnd_1882929 := by
    simpa [prefixWord, tailWord_1882929, baseEnd_1882929] using wordTrace_append hprefix tailTrace_1882929
  have hstable : (prefixWord ++ tailWord_1882929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882929).length < 2 ^ (prefixWord ++ tailWord_1882929).sum := by decide
  have hdescent : baseEnd_1882929 < baseStart_1882929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882933 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_1882933 : Nat := 118140960795 + 1882933 * 2 ^ 59
def prefixEnd_1882933 : Nat := 4983230072969 + 3 ^ 40 * 1882933 * 2
def baseEnd_1882933 : Nat := 966849669212386749678055

theorem tailTrace_1882933 : CollatzResearch.WordTrace tailWord_1882933 prefixEnd_1882933 966849669212386749678055 := by
  unfold tailWord_1882933
  simp only [CollatzResearch.WordTrace]
  refine ⟨68676208487462795199269453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45784138991641863466179635 68676208487462795199269453)
  ·
    refine ⟨25753578182798548199726045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68676208487462795199269453 25753578182798548199726045)
    ·
      refine ⟨9657591818549455574897267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25753578182798548199726045 9657591818549455574897267)
      ·
        refine ⟨14486387727824183362345901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9657591818549455574897267 14486387727824183362345901)
        ·
          refine ⟨5432395397934068760879713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14486387727824183362345901 5432395397934068760879713)
          ·
            refine ⟨4074296548450551570659785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5432395397934068760879713 4074296548450551570659785)
            ·
              refine ⟨3055722411337913677994839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074296548450551570659785 3055722411337913677994839)
              ·
                refine ⟨4583583617006870516992259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055722411337913677994839 4583583617006870516992259)
                ·
                  refine ⟨6875375425510305775488389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583583617006870516992259 6875375425510305775488389)
                  ·
                    refine ⟨1289132892283182332904073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875375425510305775488389 1289132892283182332904073)
                    ·
                      refine ⟨966849669212386749678055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289132892283182332904073 966849669212386749678055)
                      ·
                        rfl

theorem cell23_1882933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_1882933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882933 prefixEnd_1882933 := by exact prefixLift 1882933
  have htrace : WordTrace (prefixWord ++ tailWord_1882933) baseStart_1882933 baseEnd_1882933 := by
    simpa [prefixWord, tailWord_1882933, baseEnd_1882933] using wordTrace_append hprefix tailTrace_1882933
  have hstable : (prefixWord ++ tailWord_1882933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882933).length < 2 ^ (prefixWord ++ tailWord_1882933).sum := by decide
  have hdescent : baseEnd_1882933 < baseStart_1882933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882956 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 5]
def baseStart_1882956 : Nat := 118140960795 + 1882956 * 2 ^ 59
def prefixEnd_1882956 : Nat := 4983230072969 + 3 ^ 40 * 1882956 * 2
def baseEnd_1882956 : Nat := 107429053251937795521161

theorem tailTrace_1882956 : CollatzResearch.WordTrace tailWord_1882956 prefixEnd_1882956 107429053251937795521161 := by
  unfold tailWord_1882956
  simp only [CollatzResearch.WordTrace]
  refine ⟨34338523683189735063678361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45784698244252980084904481 34338523683189735063678361)
  ·
    refine ⟨25753892762392301297758771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34338523683189735063678361 25753892762392301297758771)
    ·
      refine ⟨38630839143588451946638157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25753892762392301297758771 38630839143588451946638157)
      ·
        refine ⟨14486564678845669479989309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38630839143588451946638157 14486564678845669479989309)
        ·
          refine ⟨5432461754567126054995991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14486564678845669479989309 5432461754567126054995991)
          ·
            refine ⟨8148692631850689082493987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432461754567126054995991 8148692631850689082493987)
            ·
              refine ⟨12223038947776033623740981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148692631850689082493987 12223038947776033623740981)
              ·
                refine ⟨1145909901354003152225717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12223038947776033623740981 1145909901354003152225717)
                ·
                  refine ⟨107429053251937795521161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1145909901354003152225717 107429053251937795521161)
                  ·
                    rfl

theorem cell23_1882956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_1882956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1882956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1882956 prefixEnd_1882956 := by exact prefixLift 1882956
  have htrace : WordTrace (prefixWord ++ tailWord_1882956) baseStart_1882956 baseEnd_1882956 := by
    simpa [prefixWord, tailWord_1882956, baseEnd_1882956] using wordTrace_append hprefix tailTrace_1882956
  have hstable : (prefixWord ++ tailWord_1882956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882956).length < 2 ^ (prefixWord ++ tailWord_1882956).sum := by decide
  have hdescent : baseEnd_1882956 < baseStart_1882956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883029 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 8]
def baseStart_1883029 : Nat := 118140960795 + 1883029 * 2 ^ 59
def prefixEnd_1883029 : Nat := 4983230072969 + 3 ^ 40 * 1883029 * 2
def baseEnd_1883029 : Nat := 107433218150579819341957

theorem tailTrace_1883029 : CollatzResearch.WordTrace tailWord_1883029 prefixEnd_1883029 107433218150579819341957 := by
  unfold tailWord_1883029
  simp only [CollatzResearch.WordTrace]
  refine ⟨68679709895115003594764141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45786473263410002396509427 68679709895115003594764141)
  ·
    refine ⟨25754891210668126348036553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68679709895115003594764141 25754891210668126348036553)
    ·
      refine ⟨19316168408001094761027415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25754891210668126348036553 19316168408001094761027415)
      ·
        refine ⟨28974252612001642141541123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19316168408001094761027415 28974252612001642141541123)
        ·
          refine ⟨43461378918002463212311685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28974252612001642141541123 43461378918002463212311685)
          ·
            refine ⟨8149008547125461852308441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43461378918002463212311685 8149008547125461852308441)
            ·
              refine ⟨6111756410344096389231331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149008547125461852308441 6111756410344096389231331)
              ·
                refine ⟨9167634615516144583846997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111756410344096389231331 9167634615516144583846997)
                ·
                  refine ⟨107433218150579819341957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9167634615516144583846997 107433218150579819341957)
                  ·
                    rfl

theorem cell23_1883029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_1883029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883029 prefixEnd_1883029 := by exact prefixLift 1883029
  have htrace : WordTrace (prefixWord ++ tailWord_1883029) baseStart_1883029 baseEnd_1883029 := by
    simpa [prefixWord, tailWord_1883029, baseEnd_1883029] using wordTrace_append hprefix tailTrace_1883029
  have hstable : (prefixWord ++ tailWord_1883029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883029).length < 2 ^ (prefixWord ++ tailWord_1883029).sum := by decide
  have hdescent : baseEnd_1883029 < baseStart_1883029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883030 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1883030 : Nat := 118140960795 + 1883030 * 2 ^ 59
def prefixEnd_1883030 : Nat := 4983230072969 + 3 ^ 40 * 1883030 * 2
def baseEnd_1883030 : Nat := 966899476835872870165109

theorem tailTrace_1883030 : CollatzResearch.WordTrace tailWord_1883030 prefixEnd_1883030 966899476835872870165109 := by
  unfold tailWord_1883030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292484148006961297846909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45786497578740920510367029 4292484148006961297846909)
  ·
    refine ⟨1609681555502610486692591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4292484148006961297846909 1609681555502610486692591)
    ·
      refine ⟨2414522333253915730038887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609681555502610486692591 2414522333253915730038887)
      ·
        refine ⟨3621783499880873595058331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414522333253915730038887 3621783499880873595058331)
        ·
          refine ⟨5432675249821310392587497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621783499880873595058331 5432675249821310392587497)
          ·
            refine ⟨4074506437365982794440623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5432675249821310392587497 4074506437365982794440623)
            ·
              refine ⟨6111759656048974191660935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074506437365982794440623 6111759656048974191660935)
              ·
                refine ⟨9167639484073461287491403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111759656048974191660935 9167639484073461287491403)
                ·
                  refine ⟨13751459226110191931237105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9167639484073461287491403 13751459226110191931237105)
                  ·
                    refine ⟨10313594419582643948427829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13751459226110191931237105 10313594419582643948427829)
                    ·
                      refine ⟨966899476835872870165109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10313594419582643948427829 966899476835872870165109)
                      ·
                        rfl

theorem cell23_1883030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1883030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883030 prefixEnd_1883030 := by exact prefixLift 1883030
  have htrace : WordTrace (prefixWord ++ tailWord_1883030) baseStart_1883030 baseEnd_1883030 := by
    simpa [prefixWord, tailWord_1883030, baseEnd_1883030] using wordTrace_append hprefix tailTrace_1883030
  have hstable : (prefixWord ++ tailWord_1883030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883030).length < 2 ^ (prefixWord ++ tailWord_1883030).sum := by decide
  have hdescent : baseEnd_1883030 < baseStart_1883030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883060 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1883060 : Nat := 118140960795 + 1883060 * 2 ^ 59
def prefixEnd_1883060 : Nat := 4983230072969 + 3 ^ 40 * 1883060 * 2
def baseEnd_1883060 : Nat := 966914881255507752789971

theorem tailTrace_1883060 : CollatzResearch.WordTrace tailWord_1883060 prefixEnd_1883060 966914881255507752789971 := by
  unfold tailWord_1883060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340420279001347944571317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45787227038668463926095089 34340420279001347944571317)
  ·
    refine ⟨3219414401156376369803561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34340420279001347944571317 3219414401156376369803561)
    ·
      refine ⟨2414560800867282277352671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3219414401156376369803561 2414560800867282277352671)
      ·
        refine ⟨3621841201300923416029007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414560800867282277352671 3621841201300923416029007)
        ·
          refine ⟨5432761801951385124043511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621841201300923416029007 5432761801951385124043511)
          ·
            refine ⟨8149142702927077686065267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432761801951385124043511 8149142702927077686065267)
            ·
              refine ⟨12223714054390616529097901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149142702927077686065267 12223714054390616529097901)
              ·
                refine ⟨4583892770396481198411713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12223714054390616529097901 4583892770396481198411713)
                ·
                  refine ⟨3437919577797360898808785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583892770396481198411713 3437919577797360898808785)
                  ·
                    refine ⟨2578439683348020674106589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3437919577797360898808785 2578439683348020674106589)
                    ·
                      refine ⟨966914881255507752789971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2578439683348020674106589 966914881255507752789971)
                      ·
                        rfl

theorem cell23_1883060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1883060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883060 prefixEnd_1883060 := by exact prefixLift 1883060
  have htrace : WordTrace (prefixWord ++ tailWord_1883060) baseStart_1883060 baseEnd_1883060 := by
    simpa [prefixWord, tailWord_1883060, baseEnd_1883060] using wordTrace_append hprefix tailTrace_1883060
  have hstable : (prefixWord ++ tailWord_1883060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883060).length < 2 ^ (prefixWord ++ tailWord_1883060).sum := by decide
  have hdescent : baseEnd_1883060 < baseStart_1883060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883083 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 2, 3, 2]
def baseStart_1883083 : Nat := 118140960795 + 1883083 * 2 ^ 59
def prefixEnd_1883083 : Nat := 4983230072969 + 3 ^ 40 * 1883083 * 2
def baseEnd_1883083 : Nat := 966926691310561162802365

theorem tailTrace_1883083 : CollatzResearch.WordTrace tailWord_1883083 prefixEnd_1883083 966926691310561162802365 := by
  unfold tailWord_1883083
  simp only [CollatzResearch.WordTrace]
  refine ⟨68681679436919370817229903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45787786291279580544819935 68681679436919370817229903)
  ·
    refine ⟨103022519155379056225844855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68681679436919370817229903 103022519155379056225844855)
    ·
      refine ⟨154533778733068584338767283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103022519155379056225844855 154533778733068584338767283)
      ·
        refine ⟨231800668099602876508150925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154533778733068584338767283 231800668099602876508150925)
        ·
          refine ⟨86925250537351078690556597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231800668099602876508150925 86925250537351078690556597)
          ·
            refine ⟨8149242237876663627239681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86925250537351078690556597 8149242237876663627239681)
            ·
              refine ⟨6111931678407497720429761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149242237876663627239681 6111931678407497720429761)
              ·
                refine ⟨4583948758805623290322321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6111931678407497720429761 4583948758805623290322321)
                ·
                  refine ⟨3437961569104217467741741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583948758805623290322321 3437961569104217467741741)
                  ·
                    refine ⟨1289235588414081550403153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437961569104217467741741 1289235588414081550403153)
                    ·
                      refine ⟨966926691310561162802365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289235588414081550403153 966926691310561162802365)
                      ·
                        rfl

theorem cell23_1883083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3, 2].length) (baseStart_1883083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883083 prefixEnd_1883083 := by exact prefixLift 1883083
  have htrace : WordTrace (prefixWord ++ tailWord_1883083) baseStart_1883083 baseEnd_1883083 := by
    simpa [prefixWord, tailWord_1883083, baseEnd_1883083] using wordTrace_append hprefix tailTrace_1883083
  have hstable : (prefixWord ++ tailWord_1883083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883083).length < 2 ^ (prefixWord ++ tailWord_1883083).sum := by decide
  have hdescent : baseEnd_1883083 < baseStart_1883083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883089 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_1883089 : Nat := 118140960795 + 1883089 * 2 ^ 59
def prefixEnd_1883089 : Nat := 4983230072969 + 3 ^ 40 * 1883089 * 2
def baseEnd_1883089 : Nat := 322309924064829379775779

theorem tailTrace_1883089 : CollatzResearch.WordTrace tailWord_1883089 prefixEnd_1883089 322309924064829379775779 := by
  unfold tailWord_1883089
  simp only [CollatzResearch.WordTrace]
  refine ⟨68681898274897633841948321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45787932183265089227965547 68681898274897633841948321)
  ·
    refine ⟨51511423706173225381461241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68681898274897633841948321 51511423706173225381461241)
    ·
      refine ⟨38633567779629919036095931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51511423706173225381461241 38633567779629919036095931)
      ·
        refine ⟨57950351669444878554143897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38633567779629919036095931 57950351669444878554143897)
        ·
          refine ⟨43462763752083658915607923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57950351669444878554143897 43462763752083658915607923)
          ·
            refine ⟨65194145628125488373411885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43462763752083658915607923 65194145628125488373411885)
            ·
              refine ⟨24447804610547058140029457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65194145628125488373411885 24447804610547058140029457)
              ·
                refine ⟨18335853457910293605022093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24447804610547058140029457 18335853457910293605022093)
                ·
                  refine ⟨6875945046716360101883285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18335853457910293605022093 6875945046716360101883285)
                  ·
                    refine ⟨322309924064829379775779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6875945046716360101883285 322309924064829379775779)
                    ·
                      rfl

theorem cell23_1883089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_1883089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883089 prefixEnd_1883089 := by exact prefixLift 1883089
  have htrace : WordTrace (prefixWord ++ tailWord_1883089) baseStart_1883089 baseEnd_1883089 := by
    simpa [prefixWord, tailWord_1883089, baseEnd_1883089] using wordTrace_append hprefix tailTrace_1883089
  have hstable : (prefixWord ++ tailWord_1883089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883089).length < 2 ^ (prefixWord ++ tailWord_1883089).sum := by decide
  have hdescent : baseEnd_1883089 < baseStart_1883089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883096 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1883096 : Nat := 118140960795 + 1883096 * 2 ^ 59
def prefixEnd_1883096 : Nat := 4983230072969 + 3 ^ 40 * 1883096 * 2
def baseEnd_1883096 : Nat := 966933366559069611939805

theorem tailTrace_1883096 : CollatzResearch.WordTrace tailWord_1883096 prefixEnd_1883096 966933366559069611939805 := by
  unfold tailWord_1883096
  simp only [CollatzResearch.WordTrace]
  refine ⟨34341076792936137018726571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45788102390581516024968761 34341076792936137018726571)
  ·
    refine ⟨51511615189404205528089857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34341076792936137018726571 51511615189404205528089857)
    ·
      refine ⟨38633711392053154146067393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51511615189404205528089857 38633711392053154146067393)
      ·
        refine ⟨28975283544039865609550545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38633711392053154146067393 28975283544039865609550545)
        ·
          refine ⟨21731462658029899207162909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28975283544039865609550545 21731462658029899207162909)
          ·
            refine ⟨8149298496761212202686091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21731462658029899207162909 8149298496761212202686091)
            ·
              refine ⟨12223947745141818304029137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149298496761212202686091 12223947745141818304029137)
              ·
                refine ⟨9167960808856363728021853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12223947745141818304029137 9167960808856363728021853)
                ·
                  refine ⟨3437985303321136398008195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9167960808856363728021853 3437985303321136398008195)
                  ·
                    refine ⟨5156977954981704597012293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3437985303321136398008195 5156977954981704597012293)
                    ·
                      refine ⟨966933366559069611939805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5156977954981704597012293 966933366559069611939805)
                      ·
                        rfl

theorem cell23_1883096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1883096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883096 prefixEnd_1883096 := by exact prefixLift 1883096
  have htrace : WordTrace (prefixWord ++ tailWord_1883096) baseStart_1883096 baseEnd_1883096 := by
    simpa [prefixWord, tailWord_1883096, baseEnd_1883096] using wordTrace_append hprefix tailTrace_1883096
  have hstable : (prefixWord ++ tailWord_1883096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883096).length < 2 ^ (prefixWord ++ tailWord_1883096).sum := by decide
  have hdescent : baseEnd_1883096 < baseStart_1883096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883139 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_1883139 : Nat := 118140960795 + 1883139 * 2 ^ 59
def prefixEnd_1883139 : Nat := 4983230072969 + 3 ^ 40 * 1883139 * 2
def baseEnd_1883139 : Nat := 966955446227212943702107

theorem tailTrace_1883139 : CollatzResearch.WordTrace tailWord_1883139 prefixEnd_1883139 966955446227212943702107 := by
  unfold tailWord_1883139
  simp only [CollatzResearch.WordTrace]
  refine ⟨68683721924716492381268471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45789147949810994920845647 68683721924716492381268471)
  ·
    refine ⟨103025582887074738571902707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68683721924716492381268471 103025582887074738571902707)
    ·
      refine ⟨154538374330612107857854061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103025582887074738571902707 154538374330612107857854061)
      ·
        refine ⟨57951890373979540446695273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154538374330612107857854061 57951890373979540446695273)
        ·
          refine ⟨43463917780484655335021455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57951890373979540446695273 43463917780484655335021455)
          ·
            refine ⟨65195876670726983002532183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43463917780484655335021455 65195876670726983002532183)
            ·
              refine ⟨97793815006090474503798275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65195876670726983002532183 97793815006090474503798275)
              ·
                refine ⟨146690722509135711755697413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97793815006090474503798275 146690722509135711755697413)
                ·
                  refine ⟨27504510470462945954193265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146690722509135711755697413 27504510470462945954193265)
                  ·
                    refine ⟨20628382852847209465644949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27504510470462945954193265 20628382852847209465644949)
                    ·
                      refine ⟨966955446227212943702107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20628382852847209465644949 966955446227212943702107)
                      ·
                        rfl

theorem cell23_1883139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_1883139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883139 prefixEnd_1883139 := by exact prefixLift 1883139
  have htrace : WordTrace (prefixWord ++ tailWord_1883139) baseStart_1883139 baseEnd_1883139 := by
    simpa [prefixWord, tailWord_1883139, baseEnd_1883139] using wordTrace_append hprefix tailTrace_1883139
  have hstable : (prefixWord ++ tailWord_1883139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883139).length < 2 ^ (prefixWord ++ tailWord_1883139).sum := by decide
  have hdescent : baseEnd_1883139 < baseStart_1883139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883147 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 1, 2, 2]
def baseStart_1883147 : Nat := 118140960795 + 1883147 * 2 ^ 59
def prefixEnd_1883147 : Nat := 4983230072969 + 3 ^ 40 * 1883147 * 2
def baseEnd_1883147 : Nat := 966959554072448912402071

theorem tailTrace_1883147 : CollatzResearch.WordTrace tailWord_1883147 prefixEnd_1883147 966959554072448912402071 := by
  unfold tailWord_1883147
  simp only [CollatzResearch.WordTrace]
  refine ⟨68684013708687509747559695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45789342472458339831706463 68684013708687509747559695)
  ·
    refine ⟨103026020563031264621339543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68684013708687509747559695 103026020563031264621339543)
    ·
      refine ⟨154539030844546896932009315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103026020563031264621339543 154539030844546896932009315)
      ·
        refine ⟨231808546266820345398013973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154539030844546896932009315 231808546266820345398013973)
        ·
          refine ⟨10866025606257203690531905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231808546266820345398013973 10866025606257203690531905)
          ·
            refine ⟨8149519204692902767898929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10866025606257203690531905 8149519204692902767898929)
            ·
              refine ⟨6112139403519677075924197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149519204692902767898929 6112139403519677075924197)
              ·
                refine ⟨1146026138159939451735787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6112139403519677075924197 1146026138159939451735787)
                ·
                  refine ⟨1719039207239909177603681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146026138159939451735787 1719039207239909177603681)
                  ·
                    refine ⟨1289279405429931883202761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719039207239909177603681 1289279405429931883202761)
                    ·
                      refine ⟨966959554072448912402071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289279405429931883202761 966959554072448912402071)
                      ·
                        rfl

theorem cell23_1883147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 2, 2].length) (baseStart_1883147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883147 prefixEnd_1883147 := by exact prefixLift 1883147
  have htrace : WordTrace (prefixWord ++ tailWord_1883147) baseStart_1883147 baseEnd_1883147 := by
    simpa [prefixWord, tailWord_1883147, baseEnd_1883147] using wordTrace_append hprefix tailTrace_1883147
  have hstable : (prefixWord ++ tailWord_1883147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883147).length < 2 ^ (prefixWord ++ tailWord_1883147).sum := by decide
  have hdescent : baseEnd_1883147 < baseStart_1883147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883216 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1883216 : Nat := 118140960795 + 1883216 * 2 ^ 59
def prefixEnd_1883216 : Nat := 4983230072969 + 3 ^ 40 * 1883216 * 2
def baseEnd_1883216 : Nat := 966994984237609142439253

theorem tailTrace_1883216 : CollatzResearch.WordTrace tailWord_1883216 prefixEnd_1883216 966994984237609142439253 := by
  unfold tailWord_1883216
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343265172718767265910751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45791020230291689687881001 34343265172718767265910751)
  ·
    refine ⟨51514897759078150898866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34343265172718767265910751 51514897759078150898866127)
    ·
      refine ⟨77272346638617226348299191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51514897759078150898866127 77272346638617226348299191)
      ·
        refine ⟨115908519957925839522448787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77272346638617226348299191 115908519957925839522448787)
        ·
          refine ⟨173862779936888759283673181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115908519957925839522448787 173862779936888759283673181)
          ·
            refine ⟨65198542476333284731377443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173862779936888759283673181 65198542476333284731377443)
            ·
              refine ⟨97797813714499927097066165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65198542476333284731377443 97797813714499927097066165)
              ·
                refine ⟨9168545035734368165349953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97797813714499927097066165 9168545035734368165349953)
                ·
                  refine ⟨6876408776800776124012465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9168545035734368165349953 6876408776800776124012465)
                  ·
                    refine ⟨5157306582600582093009349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6876408776800776124012465 5157306582600582093009349)
                    ·
                      refine ⟨966994984237609142439253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5157306582600582093009349 966994984237609142439253)
                      ·
                        rfl

theorem cell23_1883216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1883216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883216 prefixEnd_1883216 := by exact prefixLift 1883216
  have htrace : WordTrace (prefixWord ++ tailWord_1883216) baseStart_1883216 baseEnd_1883216 := by
    simpa [prefixWord, tailWord_1883216, baseEnd_1883216] using wordTrace_append hprefix tailTrace_1883216
  have hstable : (prefixWord ++ tailWord_1883216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883216).length < 2 ^ (prefixWord ++ tailWord_1883216).sum := by decide
  have hdescent : baseEnd_1883216 < baseStart_1883216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883254 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1883254 : Nat := 118140960795 + 1883254 * 2 ^ 59
def prefixEnd_1883254 : Nat := 4983230072969 + 3 ^ 40 * 1883254 * 2
def baseEnd_1883254 : Nat := 967014496502479993764079

theorem tailTrace_1883254 : CollatzResearch.WordTrace tailWord_1883254 prefixEnd_1883254 967014496502479993764079 := by
  unfold tailWord_1883254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292994769956241688856551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45791944212866578014469877 4292994769956241688856551)
  ·
    refine ⟨6439492154934362533284827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4292994769956241688856551 6439492154934362533284827)
    ·
      refine ⟨9659238232401543799927241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439492154934362533284827 9659238232401543799927241)
      ·
        refine ⟨7244428674301157849945431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9659238232401543799927241 7244428674301157849945431)
        ·
          refine ⟨10866643011451736774918147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244428674301157849945431 10866643011451736774918147)
          ·
            refine ⟨16299964517177605162377221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866643011451736774918147 16299964517177605162377221)
            ·
              refine ⟨3056243346970800967945729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16299964517177605162377221 3056243346970800967945729)
              ·
                refine ⟨2292182510228100725959297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056243346970800967945729 2292182510228100725959297)
                ·
                  refine ⟨1719136882671075544469473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292182510228100725959297 1719136882671075544469473)
                  ·
                    refine ⟨1289352662003306658352105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719136882671075544469473 1289352662003306658352105)
                    ·
                      refine ⟨967014496502479993764079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289352662003306658352105 967014496502479993764079)
                      ·
                        rfl

theorem cell23_1883254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1883254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883254 prefixEnd_1883254 := by exact prefixLift 1883254
  have htrace : WordTrace (prefixWord ++ tailWord_1883254) baseStart_1883254 baseEnd_1883254 := by
    simpa [prefixWord, tailWord_1883254, baseEnd_1883254] using wordTrace_append hprefix tailTrace_1883254
  have hstable : (prefixWord ++ tailWord_1883254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883254).length < 2 ^ (prefixWord ++ tailWord_1883254).sum := by decide
  have hdescent : baseEnd_1883254 < baseStart_1883254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883290 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_1883290 : Nat := 118140960795 + 1883290 * 2 ^ 59
def prefixEnd_1883290 : Nat := 4983230072969 + 3 ^ 40 * 1883290 * 2
def baseEnd_1883290 : Nat := 322344327268680617637971

theorem tailTrace_1883290 : CollatzResearch.WordTrace tailWord_1883290 prefixEnd_1883290 322344327268680617637971 := by
  unfold tailWord_1883290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172307336792361292503831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45792819564779630113343549 17172307336792361292503831)
  ·
    refine ⟨25758461005188541938755747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17172307336792361292503831 25758461005188541938755747)
    ·
      refine ⟨38637691507782812908133621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25758461005188541938755747 38637691507782812908133621)
      ·
        refine ⟨3622283578854638710137527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38637691507782812908133621 3622283578854638710137527)
        ·
          refine ⟨5433425368281958065206291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622283578854638710137527 5433425368281958065206291)
          ·
            refine ⟨8150138052422937097809437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433425368281958065206291 8150138052422937097809437)
            ·
              refine ⟨3056301769658601411678539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8150138052422937097809437 3056301769658601411678539)
              ·
                refine ⟨4584452654487902117517809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056301769658601411678539 4584452654487902117517809)
                ·
                  refine ⟨3438339490865926588138357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4584452654487902117517809 3438339490865926588138357)
                  ·
                    refine ⟨322344327268680617637971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3438339490865926588138357 322344327268680617637971)
                    ·
                      rfl

theorem cell23_1883290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_1883290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883290 prefixEnd_1883290 := by exact prefixLift 1883290
  have htrace : WordTrace (prefixWord ++ tailWord_1883290) baseStart_1883290 baseEnd_1883290 := by
    simpa [prefixWord, tailWord_1883290, baseEnd_1883290] using wordTrace_append hprefix tailTrace_1883290
  have hstable : (prefixWord ++ tailWord_1883290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883290).length < 2 ^ (prefixWord ++ tailWord_1883290).sum := by decide
  have hdescent : baseEnd_1883290 < baseStart_1883290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883293 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1883293 : Nat := 118140960795 + 1883293 * 2 ^ 59
def prefixEnd_1883293 : Nat := 4983230072969 + 3 ^ 40 * 1883293 * 2
def baseEnd_1883293 : Nat := 967034522248005341176399

theorem tailTrace_1883293 : CollatzResearch.WordTrace tailWord_1883293 prefixEnd_1883293 967034522248005341176399 := by
  unfold tailWord_1883293
  simp only [CollatzResearch.WordTrace]
  refine ⟨68689338766158576682374533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45792892510772384454916355 68689338766158576682374533)
  ·
    refine ⟨12879251018654733127945225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68689338766158576682374533 12879251018654733127945225)
    ·
      refine ⟨9659438263991049845958919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12879251018654733127945225 9659438263991049845958919)
      ·
        refine ⟨14489157395986574768938379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659438263991049845958919 14489157395986574768938379)
        ·
          refine ⟨21733736093979862153407569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14489157395986574768938379 21733736093979862153407569)
          ·
            refine ⟨16300302070484896615055677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21733736093979862153407569 16300302070484896615055677)
            ·
              refine ⟨6112613276431836230645879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16300302070484896615055677 6112613276431836230645879)
              ·
                refine ⟨9168919914647754345968819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112613276431836230645879 9168919914647754345968819)
                ·
                  refine ⟨13753379871971631518953229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9168919914647754345968819 13753379871971631518953229)
                  ·
                    refine ⟨5157517451989361819607461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13753379871971631518953229 5157517451989361819607461)
                    ·
                      refine ⟨967034522248005341176399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5157517451989361819607461 967034522248005341176399)
                      ·
                        rfl

theorem cell23_1883293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1883293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883293 prefixEnd_1883293 := by exact prefixLift 1883293
  have htrace : WordTrace (prefixWord ++ tailWord_1883293) baseStart_1883293 baseEnd_1883293 := by
    simpa [prefixWord, tailWord_1883293, baseEnd_1883293] using wordTrace_append hprefix tailTrace_1883293
  have hstable : (prefixWord ++ tailWord_1883293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883293).length < 2 ^ (prefixWord ++ tailWord_1883293).sum := by decide
  have hdescent : baseEnd_1883293 < baseStart_1883293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883383 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1883383 : Nat := 118140960795 + 1883383 * 2 ^ 59
def prefixEnd_1883383 : Nat := 4983230072969 + 3 ^ 40 * 1883383 * 2
def baseEnd_1883383 : Nat := 967080735506909989050985

theorem tailTrace_1883383 : CollatzResearch.WordTrace tailWord_1883383 prefixEnd_1883383 967080735506909989050985 := by
  unfold tailWord_1883383
  simp only [CollatzResearch.WordTrace]
  refine ⟨68692621335832522053150803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45795080890555014702100535 68692621335832522053150803)
  ·
    refine ⟨103038932003748783079726205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68692621335832522053150803 103038932003748783079726205)
    ·
      refine ⟨38639599501405793654897327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103038932003748783079726205 38639599501405793654897327)
      ·
        refine ⟨57959399252108690482345991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38639599501405793654897327 57959399252108690482345991)
        ·
          refine ⟨86939098878163035723518987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57959399252108690482345991 86939098878163035723518987)
          ·
            refine ⟨130408648317244553585278481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86939098878163035723518987 130408648317244553585278481)
            ·
              refine ⟨97806486237933415188958861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130408648317244553585278481 97806486237933415188958861)
              ·
                refine ⟨36677432339225030695859573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97806486237933415188958861 36677432339225030695859573)
                ·
                  refine ⟨3438509281802346627736835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36677432339225030695859573 3438509281802346627736835)
                  ·
                    refine ⟨5157763922703519941605253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3438509281802346627736835 5157763922703519941605253)
                    ·
                      refine ⟨967080735506909989050985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5157763922703519941605253 967080735506909989050985)
                      ·
                        rfl

theorem cell23_1883383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1883383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883383 prefixEnd_1883383 := by exact prefixLift 1883383
  have htrace : WordTrace (prefixWord ++ tailWord_1883383) baseStart_1883383 baseEnd_1883383 := by
    simpa [prefixWord, tailWord_1883383, baseEnd_1883383] using wordTrace_append hprefix tailTrace_1883383
  have hstable : (prefixWord ++ tailWord_1883383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883383).length < 2 ^ (prefixWord ++ tailWord_1883383).sum := by decide
  have hdescent : baseEnd_1883383 < baseStart_1883383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883420 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1883420 : Nat := 118140960795 + 1883420 * 2 ^ 59
def prefixEnd_1883420 : Nat := 4983230072969 + 3 ^ 40 * 1883420 * 2
def baseEnd_1883420 : Nat := 967099734291126344288315

theorem tailTrace_1883420 : CollatzResearch.WordTrace tailWord_1883420 prefixEnd_1883420 967099734291126344288315 := by
  unfold tailWord_1883420
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346985418349238686123857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45795980557798984914831809 34346985418349238686123857)
  ·
    refine ⟨25760239063761929014592893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34346985418349238686123857 25760239063761929014592893)
    ·
      refine ⟨9660089648910723380472335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25760239063761929014592893 9660089648910723380472335)
      ·
        refine ⟨14490134473366085070708503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9660089648910723380472335 14490134473366085070708503)
        ·
          refine ⟨21735201710049127606062755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14490134473366085070708503 21735201710049127606062755)
          ·
            refine ⟨32602802565073691409094133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21735201710049127606062755 32602802565073691409094133)
            ·
              refine ⟨3056512740475658569602575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32602802565073691409094133 3056512740475658569602575)
              ·
                refine ⟨4584769110713487854403863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056512740475658569602575 4584769110713487854403863)
                ·
                  refine ⟨6877153666070231781605795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584769110713487854403863 6877153666070231781605795)
                  ·
                    refine ⟨10315730499105347672408693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6877153666070231781605795 10315730499105347672408693)
                    ·
                      refine ⟨967099734291126344288315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10315730499105347672408693 967099734291126344288315)
                      ·
                        rfl

theorem cell23_1883420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1883420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883420 prefixEnd_1883420 := by exact prefixLift 1883420
  have htrace : WordTrace (prefixWord ++ tailWord_1883420) baseStart_1883420 baseEnd_1883420 := by
    simpa [prefixWord, tailWord_1883420, baseEnd_1883420] using wordTrace_append hprefix tailTrace_1883420
  have hstable : (prefixWord ++ tailWord_1883420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883420).length < 2 ^ (prefixWord ++ tailWord_1883420).sum := by decide
  have hdescent : baseEnd_1883420 < baseStart_1883420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883423 : List Nat := [1, 1, 2, 4, 4, 11]
def baseStart_1883423 : Nat := 118140960795 + 1883423 * 2 ^ 59
def prefixEnd_1883423 : Nat := 4983230072969 + 3 ^ 40 * 1883423 * 2
def baseEnd_1883423 : Nat := 3979840636761686553707

theorem tailTrace_1883423 : CollatzResearch.WordTrace tailWord_1883423 prefixEnd_1883423 3979840636761686553707 := by
  unfold tailWord_1883423
  simp only [CollatzResearch.WordTrace]
  refine ⟨68694080255687608884606923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45796053503791739256404615 68694080255687608884606923)
  ·
    refine ⟨103041120383531413326910385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68694080255687608884606923 103041120383531413326910385)
    ·
      refine ⟨77280840287648559995182789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103041120383531413326910385 77280840287648559995182789)
      ·
        refine ⟨14490157553934104999096773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77280840287648559995182789 14490157553934104999096773)
        ·
          refine ⟨2716904541362644687330645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14490157553934104999096773 2716904541362644687330645)
          ·
            refine ⟨3979840636761686553707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2716904541362644687330645 3979840636761686553707)
            ·
              rfl

theorem cell23_1883423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 11].length) (baseStart_1883423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883423 prefixEnd_1883423 := by exact prefixLift 1883423
  have htrace : WordTrace (prefixWord ++ tailWord_1883423) baseStart_1883423 baseEnd_1883423 := by
    simpa [prefixWord, tailWord_1883423, baseEnd_1883423] using wordTrace_append hprefix tailTrace_1883423
  have hstable : (prefixWord ++ tailWord_1883423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883423).length < 2 ^ (prefixWord ++ tailWord_1883423).sum := by decide
  have hdescent : baseEnd_1883423 < baseStart_1883423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883427 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 2, 4]
def baseStart_1883427 : Nat := 118140960795 + 1883427 * 2 ^ 59
def prefixEnd_1883427 : Nat := 4983230072969 + 3 ^ 40 * 1883427 * 2
def baseEnd_1883427 : Nat := 322367776218569272300261

theorem tailTrace_1883427 : CollatzResearch.WordTrace tailWord_1883427 prefixEnd_1883427 322367776218569272300261 := by
  unfold tailWord_1883427
  simp only [CollatzResearch.WordTrace]
  refine ⟨68694226147673117567752535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45796150765115411711835023 68694226147673117567752535)
  ·
    refine ⟨103041339221509676351628803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68694226147673117567752535 103041339221509676351628803)
    ·
      refine ⟨154562008832264514527443205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103041339221509676351628803 154562008832264514527443205)
      ·
        refine ⟨28980376656049596473895601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154562008832264514527443205 28980376656049596473895601)
        ·
          refine ⟨21735282492037197355421701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28980376656049596473895601 21735282492037197355421701)
          ·
            refine ⟨4075365467256974504141569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21735282492037197355421701 4075365467256974504141569)
            ·
              refine ⟨3056524100442730878106177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075365467256974504141569 3056524100442730878106177)
              ·
                refine ⟨2292393075332048158579633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056524100442730878106177 2292393075332048158579633)
                ·
                  refine ⟨1719294806499036118934725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292393075332048158579633 1719294806499036118934725)
                  ·
                    refine ⟨322367776218569272300261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1719294806499036118934725 322367776218569272300261)
                    ·
                      rfl

theorem cell23_1883427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 4].length) (baseStart_1883427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883427 prefixEnd_1883427 := by exact prefixLift 1883427
  have htrace : WordTrace (prefixWord ++ tailWord_1883427) baseStart_1883427 baseEnd_1883427 := by
    simpa [prefixWord, tailWord_1883427, baseEnd_1883427] using wordTrace_append hprefix tailTrace_1883427
  have hstable : (prefixWord ++ tailWord_1883427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883427).length < 2 ^ (prefixWord ++ tailWord_1883427).sum := by decide
  have hdescent : baseEnd_1883427 < baseStart_1883427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883457 : List Nat := [1, 2, 5, 2, 1, 2, 3, 7]
def baseStart_1883457 : Nat := 118140960795 + 1883457 * 2 ^ 59
def prefixEnd_1883457 : Nat := 4983230072969 + 3 ^ 40 * 1883457 * 2
def baseEnd_1883457 : Nat := 35819212336123803686135

theorem tailTrace_1883457 : CollatzResearch.WordTrace tailWord_1883457 prefixEnd_1883457 35819212336123803686135 := by
  unfold tailWord_1883457
  simp only [CollatzResearch.WordTrace]
  refine ⟨68695320337564432691344625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45796880225042955127563083 68695320337564432691344625)
  ·
    refine ⟨51521490253173324518508469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68695320337564432691344625 51521490253173324518508469)
    ·
      refine ⟨4830139711234999173610169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51521490253173324518508469 4830139711234999173610169)
      ·
        refine ⟨3622604783426249380207627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830139711234999173610169 3622604783426249380207627)
        ·
          refine ⟨5433907175139374070311441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622604783426249380207627 5433907175139374070311441)
          ·
            refine ⟨4075430381354530552733581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433907175139374070311441 4075430381354530552733581)
            ·
              refine ⟨1528286393007948957275093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4075430381354530552733581 1528286393007948957275093)
              ·
                refine ⟨35819212336123803686135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1528286393007948957275093 35819212336123803686135)
                ·
                  rfl

theorem cell23_1883457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 7].length) (baseStart_1883457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883457 prefixEnd_1883457 := by exact prefixLift 1883457
  have htrace : WordTrace (prefixWord ++ tailWord_1883457) baseStart_1883457 baseEnd_1883457 := by
    simpa [prefixWord, tailWord_1883457, baseEnd_1883457] using wordTrace_append hprefix tailTrace_1883457
  have hstable : (prefixWord ++ tailWord_1883457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883457).length < 2 ^ (prefixWord ++ tailWord_1883457).sum := by decide
  have hdescent : baseEnd_1883457 < baseStart_1883457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883478 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1883478 : Nat := 118140960795 + 1883478 * 2 ^ 59
def prefixEnd_1883478 : Nat := 4983230072969 + 3 ^ 40 * 1883478 * 2
def baseEnd_1883478 : Nat := 322376505389695705787683

theorem tailTrace_1883478 : CollatzResearch.WordTrace tailWord_1883478 prefixEnd_1883478 322376505389695705787683 := by
  unfold tailWord_1883478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293505391905522079866193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45797390846992235518572725 4293505391905522079866193)
  ·
    refine ⟨3220129043929141559899645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4293505391905522079866193 3220129043929141559899645)
    ·
      refine ⟨1207548391473428084962367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3220129043929141559899645 1207548391473428084962367)
      ·
        refine ⟨1811322587210142127443551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207548391473428084962367 1811322587210142127443551)
        ·
          refine ⟨2716983880815213191165327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811322587210142127443551 2716983880815213191165327)
          ·
            refine ⟨4075475821222819786747991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716983880815213191165327 4075475821222819786747991)
            ·
              refine ⟨6113213731834229680121987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075475821222819786747991 6113213731834229680121987)
              ·
                refine ⟨9169820597751344520182981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113213731834229680121987 9169820597751344520182981)
                ·
                  refine ⟨1719341362078377097534309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9169820597751344520182981 1719341362078377097534309)
                  ·
                    refine ⟨322376505389695705787683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1719341362078377097534309 322376505389695705787683)
                    ·
                      rfl

theorem cell23_1883478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1883478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883478 prefixEnd_1883478 := by exact prefixLift 1883478
  have htrace : WordTrace (prefixWord ++ tailWord_1883478) baseStart_1883478 baseEnd_1883478 := by
    simpa [prefixWord, tailWord_1883478, baseEnd_1883478] using wordTrace_append hprefix tailTrace_1883478
  have hstable : (prefixWord ++ tailWord_1883478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883478).length < 2 ^ (prefixWord ++ tailWord_1883478).sum := by decide
  have hdescent : baseEnd_1883478 < baseStart_1883478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883485 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1883485 : Nat := 118140960795 + 1883485 * 2 ^ 59
def prefixEnd_1883485 : Nat := 4983230072969 + 3 ^ 40 * 1883485 * 2
def baseEnd_1883485 : Nat := 967133110533668589975517

theorem tailTrace_1883485 : CollatzResearch.WordTrace tailWord_1883485 prefixEnd_1883485 967133110533668589975517 := by
  unfold tailWord_1883485
  simp only [CollatzResearch.WordTrace]
  refine ⟨68696341581462993473363909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45797561054308662315575939 68696341581462993473363909)
  ·
    refine ⟨12880564046524311276255733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68696341581462993473363909 12880564046524311276255733)
    ·
      refine ⟨1207552879361654182148975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12880564046524311276255733 1207552879361654182148975)
      ·
        refine ⟨1811329319042481273223463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207552879361654182148975 1811329319042481273223463)
        ·
          refine ⟨2716993978563721909835195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811329319042481273223463 2716993978563721909835195)
          ·
            refine ⟨4075490967845582864752793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716993978563721909835195 4075490967845582864752793)
            ·
              refine ⟨3056618225884187148564595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075490967845582864752793 3056618225884187148564595)
              ·
                refine ⟨4584927338826280722846893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056618225884187148564595 4584927338826280722846893)
                ·
                  refine ⟨1719347752059855271067585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4584927338826280722846893 1719347752059855271067585)
                  ·
                    refine ⟨1289510814044891453300689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719347752059855271067585 1289510814044891453300689)
                    ·
                      refine ⟨967133110533668589975517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289510814044891453300689 967133110533668589975517)
                      ·
                        rfl

theorem cell23_1883485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1883485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883485 prefixEnd_1883485 := by exact prefixLift 1883485
  have htrace : WordTrace (prefixWord ++ tailWord_1883485) baseStart_1883485 baseEnd_1883485 := by
    simpa [prefixWord, tailWord_1883485, baseEnd_1883485] using wordTrace_append hprefix tailTrace_1883485
  have hstable : (prefixWord ++ tailWord_1883485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883485).length < 2 ^ (prefixWord ++ tailWord_1883485).sum := by decide
  have hdescent : baseEnd_1883485 < baseStart_1883485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883500 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1883500 : Nat := 118140960795 + 1883500 * 2 ^ 59
def prefixEnd_1883500 : Nat := 4983230072969 + 3 ^ 40 * 1883500 * 2
def baseEnd_1883500 : Nat := 322380270914495343762649

theorem tailTrace_1883500 : CollatzResearch.WordTrace tailWord_1883500 prefixEnd_1883500 322380270914495343762649 := by
  unfold tailWord_1883500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348444338204325517579977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45797925784272434023439969 34348444338204325517579977)
  ·
    refine ⟨25761333253653244138184983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34348444338204325517579977 25761333253653244138184983)
    ·
      refine ⟨38641999880479866207277475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25761333253653244138184983 38641999880479866207277475)
      ·
        refine ⟨57962999820719799310916213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38641999880479866207277475 57962999820719799310916213)
        ·
          refine ⟨5434031233192481185398395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57962999820719799310916213 5434031233192481185398395)
          ·
            refine ⟨8151046849788721778097593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434031233192481185398395 8151046849788721778097593)
            ·
              refine ⟨6113285137341541333573195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8151046849788721778097593 6113285137341541333573195)
              ·
                refine ⟨9169927706012312000359793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113285137341541333573195 9169927706012312000359793)
                ·
                  refine ⟨6877445779509234000269845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169927706012312000359793 6877445779509234000269845)
                  ·
                    refine ⟨322380270914495343762649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6877445779509234000269845 322380270914495343762649)
                    ·
                      rfl

theorem cell23_1883500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1883500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883500 prefixEnd_1883500 := by exact prefixLift 1883500
  have htrace : WordTrace (prefixWord ++ tailWord_1883500) baseStart_1883500 baseEnd_1883500 := by
    simpa [prefixWord, tailWord_1883500, baseEnd_1883500] using wordTrace_append hprefix tailTrace_1883500
  have hstable : (prefixWord ++ tailWord_1883500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883500).length < 2 ^ (prefixWord ++ tailWord_1883500).sum := by decide
  have hdescent : baseEnd_1883500 < baseStart_1883500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883501 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_1883501 : Nat := 118140960795 + 1883501 * 2 ^ 59
def prefixEnd_1883501 : Nat := 4983230072969 + 3 ^ 40 * 1883501 * 2
def baseEnd_1883501 : Nat := 967141326224140527375443

theorem tailTrace_1883501 : CollatzResearch.WordTrace tailWord_1883501 prefixEnd_1883501 967141326224140527375443 := by
  unfold tailWord_1883501
  simp only [CollatzResearch.WordTrace]
  refine ⟨68696925149405028205946357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45797950099603352137297571 68696925149405028205946357)
  ·
    refine ⟨6440336732756721394307471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68696925149405028205946357 6440336732756721394307471)
    ·
      refine ⟨9660505099135082091461207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6440336732756721394307471 9660505099135082091461207)
      ·
        refine ⟨14490757648702623137191811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9660505099135082091461207 14490757648702623137191811)
        ·
          refine ⟨21736136473053934705787717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14490757648702623137191811 21736136473053934705787717)
          ·
            refine ⟨4075525588697612757335197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21736136473053934705787717 4075525588697612757335197)
            ·
              refine ⟨1528322095761604784000699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4075525588697612757335197 1528322095761604784000699)
              ·
                refine ⟨2292483143642407176001049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528322095761604784000699 2292483143642407176001049)
                ·
                  refine ⟨1719362357731805382000787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292483143642407176001049 1719362357731805382000787)
                  ·
                    refine ⟨2579043536597708073001181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719362357731805382000787 2579043536597708073001181)
                    ·
                      refine ⟨967141326224140527375443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579043536597708073001181 967141326224140527375443)
                      ·
                        rfl

theorem cell23_1883501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_1883501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883501 prefixEnd_1883501 := by exact prefixLift 1883501
  have htrace : WordTrace (prefixWord ++ tailWord_1883501) baseStart_1883501 baseEnd_1883501 := by
    simpa [prefixWord, tailWord_1883501, baseEnd_1883501] using wordTrace_append hprefix tailTrace_1883501
  have hstable : (prefixWord ++ tailWord_1883501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883501).length < 2 ^ (prefixWord ++ tailWord_1883501).sum := by decide
  have hdescent : baseEnd_1883501 < baseStart_1883501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883507 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 8, 2, 2]
def baseStart_1883507 : Nat := 118140960795 + 1883507 * 2 ^ 59
def prefixEnd_1883507 : Nat := 4983230072969 + 3 ^ 40 * 1883507 * 2
def baseEnd_1883507 : Nat := 967144407108067503900415

theorem tailTrace_1883507 : CollatzResearch.WordTrace tailWord_1883507 prefixEnd_1883507 967144407108067503900415 := by
  unfold tailWord_1883507
  simp only [CollatzResearch.WordTrace]
  refine ⟨68697143987383291230664775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45798095991588860820443183 68697143987383291230664775)
  ·
    refine ⟨103045715981074936845997163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68697143987383291230664775 103045715981074936845997163)
    ·
      refine ⟨154568573971612405268995745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103045715981074936845997163 154568573971612405268995745)
      ·
        refine ⟨115926430478709303951746809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154568573971612405268995745 115926430478709303951746809)
        ·
          refine ⟨86944822859031977963810107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115926430478709303951746809 86944822859031977963810107)
          ·
            refine ⟨130417234288547966945715161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86944822859031977963810107 130417234288547966945715161)
            ·
              refine ⟨97812925716410975209286371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130417234288547966945715161 97812925716410975209286371)
              ·
                refine ⟨146719388574616462813929557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97812925716410975209286371 146719388574616462813929557)
                ·
                  refine ⟨1719367834858786673600737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 146719388574616462813929557 1719367834858786673600737)
                  ·
                    refine ⟨1289525876144090005200553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719367834858786673600737 1289525876144090005200553)
                    ·
                      refine ⟨967144407108067503900415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289525876144090005200553 967144407108067503900415)
                      ·
                        rfl

theorem cell23_1883507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2, 2].length) (baseStart_1883507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883507 prefixEnd_1883507 := by exact prefixLift 1883507
  have htrace : WordTrace (prefixWord ++ tailWord_1883507) baseStart_1883507 baseEnd_1883507 := by
    simpa [prefixWord, tailWord_1883507, baseEnd_1883507] using wordTrace_append hprefix tailTrace_1883507
  have hstable : (prefixWord ++ tailWord_1883507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883507).length < 2 ^ (prefixWord ++ tailWord_1883507).sum := by decide
  have hdescent : baseEnd_1883507 < baseStart_1883507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883524 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1883524 : Nat := 118140960795 + 1883524 * 2 ^ 59
def prefixEnd_1883524 : Nat := 4983230072969 + 3 ^ 40 * 1883524 * 2
def baseEnd_1883524 : Nat := 967153136279193937387837

theorem tailTrace_1883524 : CollatzResearch.WordTrace tailWord_1883524 prefixEnd_1883524 967153136279193937387837 := by
  unfold tailWord_1883524
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348882014160851567016813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45798509352214468756022417 34348882014160851567016813)
  ·
    refine ⟨12880830755310319337631305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34348882014160851567016813 12880830755310319337631305)
    ·
      refine ⟨9660623066482739503223479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12880830755310319337631305 9660623066482739503223479)
      ·
        refine ⟨14490934599724109254835219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9660623066482739503223479 14490934599724109254835219)
        ·
          refine ⟨21736401899586163882252829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14490934599724109254835219 21736401899586163882252829)
          ·
            refine ⟨8151150712344811455844811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21736401899586163882252829 8151150712344811455844811)
            ·
              refine ⟨12226726068517217183767217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151150712344811455844811 12226726068517217183767217)
              ·
                refine ⟨9170044551387912887825413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12226726068517217183767217 9170044551387912887825413)
                ·
                  refine ⟨1719383353385233666467265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9170044551387912887825413 1719383353385233666467265)
                  ·
                    refine ⟨1289537515038925249850449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719383353385233666467265 1289537515038925249850449)
                    ·
                      refine ⟨967153136279193937387837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289537515038925249850449 967153136279193937387837)
                      ·
                        rfl

theorem cell23_1883524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1883524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883524 prefixEnd_1883524 := by exact prefixLift 1883524
  have htrace : WordTrace (prefixWord ++ tailWord_1883524) baseStart_1883524 baseEnd_1883524 := by
    simpa [prefixWord, tailWord_1883524, baseEnd_1883524] using wordTrace_append hprefix tailTrace_1883524
  have hstable : (prefixWord ++ tailWord_1883524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883524).length < 2 ^ (prefixWord ++ tailWord_1883524).sum := by decide
  have hdescent : baseEnd_1883524 < baseStart_1883524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883634 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1883634 : Nat := 118140960795 + 1883634 * 2 ^ 59
def prefixEnd_1883634 : Nat := 4983230072969 + 3 ^ 40 * 1883634 * 2
def baseEnd_1883634 : Nat := 967209619151188507012331

theorem tailTrace_1883634 : CollatzResearch.WordTrace tailWord_1883634 prefixEnd_1883634 967209619151188507012331 := by
  unfold tailWord_1883634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17175444014480797980134489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45801184038615461280358637 17175444014480797980134489)
  ·
    refine ⟨12881583010860598485100867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17175444014480797980134489 12881583010860598485100867)
    ·
      refine ⟨19322374516290897727651301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881583010860598485100867 19322374516290897727651301)
      ·
        refine ⟨3622945221804543323934619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19322374516290897727651301 3622945221804543323934619)
        ·
          refine ⟨5434417832706814985901929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622945221804543323934619 5434417832706814985901929)
          ·
            refine ⟨4075813374530111239426447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434417832706814985901929 4075813374530111239426447)
            ·
              refine ⟨6113720061795166859139671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075813374530111239426447 6113720061795166859139671)
              ·
                refine ⟨9170580092692750288709507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113720061795166859139671 9170580092692750288709507)
                ·
                  refine ⟨13755870139039125433064261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9170580092692750288709507 13755870139039125433064261)
                  ·
                    refine ⟨2579225651069836018699549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13755870139039125433064261 2579225651069836018699549)
                    ·
                      refine ⟨967209619151188507012331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579225651069836018699549 967209619151188507012331)
                      ·
                        rfl

theorem cell23_1883634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1883634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883634 prefixEnd_1883634 := by exact prefixLift 1883634
  have htrace : WordTrace (prefixWord ++ tailWord_1883634) baseStart_1883634 baseEnd_1883634 := by
    simpa [prefixWord, tailWord_1883634, baseEnd_1883634] using wordTrace_append hprefix tailTrace_1883634
  have hstable : (prefixWord ++ tailWord_1883634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883634).length < 2 ^ (prefixWord ++ tailWord_1883634).sum := by decide
  have hdescent : baseEnd_1883634 < baseStart_1883634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883704 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_1883704 : Nat := 118140960795 + 1883704 * 2 ^ 59
def prefixEnd_1883704 : Nat := 4983230072969 + 3 ^ 40 * 1883704 * 2
def baseEnd_1883704 : Nat := 967245562797003233137009

theorem tailTrace_1883704 : CollatzResearch.WordTrace tailWord_1883704 prefixEnd_1883704 967245562797003233137009 := by
  unfold tailWord_1883704
  simp only [CollatzResearch.WordTrace]
  refine ⟨34352164583834796937793083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45802886111779729250390777 34352164583834796937793083)
  ·
    refine ⟨51528246875752195406689625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34352164583834796937793083 51528246875752195406689625)
    ·
      refine ⟨38646185156814146555017219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51528246875752195406689625 38646185156814146555017219)
      ·
        refine ⟨57969277735221219832525829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38646185156814146555017219 57969277735221219832525829)
        ·
          refine ⟨10869239575353978718598593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57969277735221219832525829 10869239575353978718598593)
          ·
            refine ⟨8151929681515484038948945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10869239575353978718598593 8151929681515484038948945)
            ·
              refine ⟨6113947261136613029211709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8151929681515484038948945 6113947261136613029211709)
              ·
                refine ⟨2292730222926229885954391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6113947261136613029211709 2292730222926229885954391)
                ·
                  refine ⟨3439095334389344828931587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292730222926229885954391 3439095334389344828931587)
                  ·
                    refine ⟨5158643001584017243397381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439095334389344828931587 5158643001584017243397381)
                    ·
                      refine ⟨967245562797003233137009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5158643001584017243397381 967245562797003233137009)
                      ·
                        rfl

theorem cell23_1883704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_1883704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883704 prefixEnd_1883704 := by exact prefixLift 1883704
  have htrace : WordTrace (prefixWord ++ tailWord_1883704) baseStart_1883704 baseEnd_1883704 := by
    simpa [prefixWord, tailWord_1883704, baseEnd_1883704] using wordTrace_append hprefix tailTrace_1883704
  have hstable : (prefixWord ++ tailWord_1883704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883704).length < 2 ^ (prefixWord ++ tailWord_1883704).sum := by decide
  have hdescent : baseEnd_1883704 < baseStart_1883704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883737 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_1883737 : Nat := 118140960795 + 1883737 * 2 ^ 59
def prefixEnd_1883737 : Nat := 4983230072969 + 3 ^ 40 * 1883737 * 2
def baseEnd_1883737 : Nat := 967262507658601604024357

theorem tailTrace_1883737 : CollatzResearch.WordTrace tailWord_1883737 prefixEnd_1883737 967262507658601604024357 := by
  unfold tailWord_1883737
  simp only [CollatzResearch.WordTrace]
  refine ⟨68705532776550040511537465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45803688517700027007691643 68705532776550040511537465)
  ·
    refine ⟨51529149582412530383653099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68705532776550040511537465 51529149582412530383653099)
    ·
      refine ⟨77293724373618795575479649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51529149582412530383653099 77293724373618795575479649)
      ·
        refine ⟨57970293280214096681609737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77293724373618795575479649 57970293280214096681609737)
        ·
          refine ⟨43477719960160572511207303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57970293280214096681609737 43477719960160572511207303)
          ·
            refine ⟨65216579940240858766810955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43477719960160572511207303 65216579940240858766810955)
            ·
              refine ⟨97824869910361288150216433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65216579940240858766810955 97824869910361288150216433)
              ·
                refine ⟨73368652432770966112662325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97824869910361288150216433 73368652432770966112662325)
                ·
                  refine ⟨6878311165572278073062093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73368652432770966112662325 6878311165572278073062093)
                  ·
                    refine ⟨2579366687089604277398285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6878311165572278073062093 2579366687089604277398285)
                    ·
                      refine ⟨967262507658601604024357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579366687089604277398285 967262507658601604024357)
                      ·
                        rfl

theorem cell23_1883737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_1883737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883737 prefixEnd_1883737 := by exact prefixLift 1883737
  have htrace : WordTrace (prefixWord ++ tailWord_1883737) baseStart_1883737 baseEnd_1883737 := by
    simpa [prefixWord, tailWord_1883737, baseEnd_1883737] using wordTrace_append hprefix tailTrace_1883737
  have hstable : (prefixWord ++ tailWord_1883737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883737).length < 2 ^ (prefixWord ++ tailWord_1883737).sum := by decide
  have hdescent : baseEnd_1883737 < baseStart_1883737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883754 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1883754 : Nat := 118140960795 + 1883754 * 2 ^ 59
def prefixEnd_1883754 : Nat := 4983230072969 + 3 ^ 40 * 1883754 * 2
def baseEnd_1883754 : Nat := 967271236829728037511779

theorem tailTrace_1883754 : CollatzResearch.WordTrace tailWord_1883754 prefixEnd_1883754 967271236829728037511779 := by
  unfold tailWord_1883754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176538204372113103726579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45804101878325634943270877 17176538204372113103726579)
  ·
    refine ⟨25764807306558169655589869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17176538204372113103726579 25764807306558169655589869)
    ·
      refine ⟨9661802739959313620846201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25764807306558169655589869 9661802739959313620846201)
      ·
        refine ⟨7246352054969485215634651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661802739959313620846201 7246352054969485215634651)
        ·
          refine ⟨10869528082454227823451977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246352054969485215634651 10869528082454227823451977)
          ·
            refine ⟨8152146061840670867588983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10869528082454227823451977 8152146061840670867588983)
            ·
              refine ⟨12228219092761006301383475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152146061840670867588983 12228219092761006301383475)
              ·
                refine ⟨18342328639141509452075213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12228219092761006301383475 18342328639141509452075213)
                ·
                  refine ⟨6878373239678066044528205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18342328639141509452075213 6878373239678066044528205)
                  ·
                    refine ⟨2579389964879274766698077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6878373239678066044528205 2579389964879274766698077)
                    ·
                      refine ⟨967271236829728037511779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579389964879274766698077 967271236829728037511779)
                      ·
                        rfl

theorem cell23_1883754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1883754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883754 prefixEnd_1883754 := by exact prefixLift 1883754
  have htrace : WordTrace (prefixWord ++ tailWord_1883754) baseStart_1883754 baseEnd_1883754 := by
    simpa [prefixWord, tailWord_1883754, baseEnd_1883754] using wordTrace_append hprefix tailTrace_1883754
  have hstable : (prefixWord ++ tailWord_1883754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883754).length < 2 ^ (prefixWord ++ tailWord_1883754).sum := by decide
  have hdescent : baseEnd_1883754 < baseStart_1883754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883758 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1883758 : Nat := 118140960795 + 1883758 * 2 ^ 59
def prefixEnd_1883758 : Nat := 4983230072969 + 3 ^ 40 * 1883758 * 2
def baseEnd_1883758 : Nat := 967273290752346021861761

theorem tailTrace_1883758 : CollatzResearch.WordTrace tailWord_1883758 prefixEnd_1883758 967273290752346021861761 := by
  unfold tailWord_1883758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588287338684245137256491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45804199139649307398701285 8588287338684245137256491)
  ·
    refine ⟨12882431008026367705884737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588287338684245137256491 12882431008026367705884737)
    ·
      refine ⟨9661823256019775779413553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12882431008026367705884737 9661823256019775779413553)
      ·
        refine ⟨7246367442014831834560165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661823256019775779413553 7246367442014831834560165)
        ·
          refine ⟨1358693895377780968980031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7246367442014831834560165 1358693895377780968980031)
          ·
            refine ⟨2038040843066671453470047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358693895377780968980031 2038040843066671453470047)
            ·
              refine ⟨3057061264600007180205071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038040843066671453470047 3057061264600007180205071)
              ·
                refine ⟨4585591896900010770307607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057061264600007180205071 4585591896900010770307607)
                ·
                  refine ⟨6878387845350016155461411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585591896900010770307607 6878387845350016155461411)
                  ·
                    refine ⟨10317581768025024233192117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878387845350016155461411 10317581768025024233192117)
                    ·
                      refine ⟨967273290752346021861761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10317581768025024233192117 967273290752346021861761)
                      ·
                        rfl

theorem cell23_1883758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1883758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883758 prefixEnd_1883758 := by exact prefixLift 1883758
  have htrace : WordTrace (prefixWord ++ tailWord_1883758) baseStart_1883758 baseEnd_1883758 := by
    simpa [prefixWord, tailWord_1883758, baseEnd_1883758] using wordTrace_append hprefix tailTrace_1883758
  have hstable : (prefixWord ++ tailWord_1883758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883758).length < 2 ^ (prefixWord ++ tailWord_1883758).sum := by decide
  have hdescent : baseEnd_1883758 < baseStart_1883758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883771 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 3]
def baseStart_1883771 : Nat := 118140960795 + 1883771 * 2 ^ 59
def prefixEnd_1883771 : Nat := 4983230072969 + 3 ^ 40 * 1883771 * 2
def baseEnd_1883771 : Nat := 967279966000854470999201

theorem tailTrace_1883771 : CollatzResearch.WordTrace tailWord_1883771 prefixEnd_1883771 967279966000854470999201 := by
  unfold tailWord_1883771
  simp only [CollatzResearch.WordTrace]
  refine ⟨68706772858426864318275167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45804515238951242878850111 68706772858426864318275167)
  ·
    refine ⟨103060159287640296477412751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68706772858426864318275167 103060159287640296477412751)
    ·
      refine ⟨154590238931460444716119127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103060159287640296477412751 154590238931460444716119127)
      ·
        refine ⟨231885358397190667074178691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154590238931460444716119127 231885358397190667074178691)
        ·
          refine ⟨347828037595786000611268037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231885358397190667074178691 347828037595786000611268037)
          ·
            refine ⟨65217757049209875114612757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347828037595786000611268037 65217757049209875114612757)
            ·
              refine ⟨3057082361681712895997473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65217757049209875114612757 3057082361681712895997473)
              ·
                refine ⟨2292811771261284671998105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057082361681712895997473 2292811771261284671998105)
                ·
                  refine ⟨1719608828445963503998579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292811771261284671998105 1719608828445963503998579)
                  ·
                    refine ⟨2579413242668945255997869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719608828445963503998579 2579413242668945255997869)
                    ·
                      refine ⟨967279966000854470999201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579413242668945255997869 967279966000854470999201)
                      ·
                        rfl

theorem cell23_1883771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 3].length) (baseStart_1883771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883771 prefixEnd_1883771 := by exact prefixLift 1883771
  have htrace : WordTrace (prefixWord ++ tailWord_1883771) baseStart_1883771 baseEnd_1883771 := by
    simpa [prefixWord, tailWord_1883771, baseEnd_1883771] using wordTrace_append hprefix tailTrace_1883771
  have hstable : (prefixWord ++ tailWord_1883771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883771).length < 2 ^ (prefixWord ++ tailWord_1883771).sum := by decide
  have hdescent : baseEnd_1883771 < baseStart_1883771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883787 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 2, 6]
def baseStart_1883787 : Nat := 118140960795 + 1883787 * 2 ^ 59
def prefixEnd_1883787 : Nat := 4983230072969 + 3 ^ 40 * 1883787 * 2
def baseEnd_1883787 : Nat := 322429393897108802799709

theorem tailTrace_1883787 : CollatzResearch.WordTrace tailWord_1883787 prefixEnd_1883787 322429393897108802799709 := by
  unfold tailWord_1883787
  simp only [CollatzResearch.WordTrace]
  refine ⟨68707356426368899050857615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45804904284245932700571743 68707356426368899050857615)
  ·
    refine ⟨103061034639553348576286423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68707356426368899050857615 103061034639553348576286423)
    ·
      refine ⟨154591551959330022864429635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103061034639553348576286423 154591551959330022864429635)
      ·
        refine ⟨231887327938995034296644453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154591551959330022864429635 231887327938995034296644453)
        ·
          refine ⟨43478873988561568930620835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231887327938995034296644453 43478873988561568930620835)
          ·
            refine ⟨65218310982842353395931253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43478873988561568930620835 65218310982842353395931253)
            ·
              refine ⟨6114216654641470630868555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65218310982842353395931253 6114216654641470630868555)
              ·
                refine ⟨9171324981962205946302833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114216654641470630868555 9171324981962205946302833)
                ·
                  refine ⟨6878493736471654459727125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171324981962205946302833 6878493736471654459727125)
                  ·
                    refine ⟨322429393897108802799709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6878493736471654459727125 322429393897108802799709)
                    ·
                      rfl

theorem cell23_1883787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_1883787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883787 prefixEnd_1883787 := by exact prefixLift 1883787
  have htrace : WordTrace (prefixWord ++ tailWord_1883787) baseStart_1883787 baseEnd_1883787 := by
    simpa [prefixWord, tailWord_1883787, baseEnd_1883787] using wordTrace_append hprefix tailTrace_1883787
  have hstable : (prefixWord ++ tailWord_1883787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883787).length < 2 ^ (prefixWord ++ tailWord_1883787).sum := by decide
  have hdescent : baseEnd_1883787 < baseStart_1883787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883797 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1883797 : Nat := 118140960795 + 1883797 * 2 ^ 59
def prefixEnd_1883797 : Nat := 4983230072969 + 3 ^ 40 * 1883797 * 2
def baseEnd_1883797 : Nat := 967293316497871369274081

theorem tailTrace_1883797 : CollatzResearch.WordTrace tailWord_1883797 prefixEnd_1883797 967293316497871369274081 := by
  unfold tailWord_1883797
  simp only [CollatzResearch.WordTrace]
  refine ⟨68707721156332670758721645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45805147437555113839147763 68707721156332670758721645)
  ·
    refine ⟨25765395433624751534520617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68707721156332670758721645 25765395433624751534520617)
    ·
      refine ⟨19324046575218563650890463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25765395433624751534520617 19324046575218563650890463)
      ·
        refine ⟨28986069862827845476335695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19324046575218563650890463 28986069862827845476335695)
        ·
          refine ⟨43479104794241768214503543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28986069862827845476335695 43479104794241768214503543)
          ·
            refine ⟨65218657191362652321755315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43479104794241768214503543 65218657191362652321755315)
            ·
              refine ⟨97827985787043978482632973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65218657191362652321755315 97827985787043978482632973)
              ·
                refine ⟨36685494670141491930987365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97827985787043978482632973 36685494670141491930987365)
                ·
                  refine ⟨6878530250651529737060131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36685494670141491930987365 6878530250651529737060131)
                  ·
                    refine ⟨10317795375977294605590197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878530250651529737060131 10317795375977294605590197)
                    ·
                      refine ⟨967293316497871369274081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10317795375977294605590197 967293316497871369274081)
                      ·
                        rfl

theorem cell23_1883797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1883797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883797 prefixEnd_1883797 := by exact prefixLift 1883797
  have htrace : WordTrace (prefixWord ++ tailWord_1883797) baseStart_1883797 baseEnd_1883797 := by
    simpa [prefixWord, tailWord_1883797, baseEnd_1883797] using wordTrace_append hprefix tailTrace_1883797
  have hstable : (prefixWord ++ tailWord_1883797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883797).length < 2 ^ (prefixWord ++ tailWord_1883797).sum := by decide
  have hdescent : baseEnd_1883797 < baseStart_1883797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883811 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 4, 2, 2]
def baseStart_1883811 : Nat := 118140960795 + 1883811 * 2 ^ 59
def prefixEnd_1883811 : Nat := 4983230072969 + 3 ^ 40 * 1883811 * 2
def baseEnd_1883811 : Nat := 967300505227034314499017

theorem tailTrace_1883811 : CollatzResearch.WordTrace tailWord_1883811 prefixEnd_1883811 967300505227034314499017 := by
  unfold tailWord_1883811
  simp only [CollatzResearch.WordTrace]
  refine ⟨68708231778281951149731287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45805487852187967433154191 68708231778281951149731287)
  ·
    refine ⟨103062347667422926724596931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68708231778281951149731287 103062347667422926724596931)
    ·
      refine ⟨154593521501134390086895397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103062347667422926724596931 154593521501134390086895397)
      ·
        refine ⟨28986285281462698141292887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154593521501134390086895397 28986285281462698141292887)
        ·
          refine ⟨43479427922194047211939331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28986285281462698141292887 43479427922194047211939331)
          ·
            refine ⟨65219141883291070817908997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43479427922194047211939331 65219141883291070817908997)
            ·
              refine ⟨12228589103117075778357937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65219141883291070817908997 12228589103117075778357937)
              ·
                refine ⟨9171441827337806833768453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12228589103117075778357937 9171441827337806833768453)
                ·
                  refine ⟨1719645342625838781331585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9171441827337806833768453 1719645342625838781331585)
                  ·
                    refine ⟨1289734006969379085998689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719645342625838781331585 1289734006969379085998689)
                    ·
                      refine ⟨967300505227034314499017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289734006969379085998689 967300505227034314499017)
                      ·
                        rfl

theorem cell23_1883811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_1883811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883811 prefixEnd_1883811 := by exact prefixLift 1883811
  have htrace : WordTrace (prefixWord ++ tailWord_1883811) baseStart_1883811 baseEnd_1883811 := by
    simpa [prefixWord, tailWord_1883811, baseEnd_1883811] using wordTrace_append hprefix tailTrace_1883811
  have hstable : (prefixWord ++ tailWord_1883811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883811).length < 2 ^ (prefixWord ++ tailWord_1883811).sum := by decide
  have hdescent : baseEnd_1883811 < baseStart_1883811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883822 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1883822 : Nat := 118140960795 + 1883822 * 2 ^ 59
def prefixEnd_1883822 : Nat := 4983230072969 + 3 ^ 40 * 1883822 * 2
def baseEnd_1883822 : Nat := 967306153514233771461467

theorem tailTrace_1883822 : CollatzResearch.WordTrace tailWord_1883822 prefixEnd_1883822 967306153514233771461467 := by
  unfold tailWord_1883822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588579122655262503547715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45805755320828066685587813 8588579122655262503547715)
  ·
    refine ⟨12882868683982893755321573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588579122655262503547715 12882868683982893755321573)
    ·
      refine ⟨2415537878246792579122795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12882868683982893755321573 2415537878246792579122795)
      ·
        refine ⟨3623306817370188868684193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415537878246792579122795 3623306817370188868684193)
        ·
          refine ⟨2717480113027641651513145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623306817370188868684193 2717480113027641651513145)
          ·
            refine ⟨2038110084770731238634859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717480113027641651513145 2038110084770731238634859)
            ·
              refine ⟨3057165127156096857952289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038110084770731238634859 3057165127156096857952289)
              ·
                refine ⟨2292873845367072643464217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057165127156096857952289 2292873845367072643464217)
                ·
                  refine ⟨1719655384025304482598163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292873845367072643464217 1719655384025304482598163)
                  ·
                    refine ⟨2579483076037956723897245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719655384025304482598163 2579483076037956723897245)
                    ·
                      refine ⟨967306153514233771461467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579483076037956723897245 967306153514233771461467)
                      ·
                        rfl

theorem cell23_1883822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1883822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883822 prefixEnd_1883822 := by exact prefixLift 1883822
  have htrace : WordTrace (prefixWord ++ tailWord_1883822) baseStart_1883822 baseEnd_1883822 := by
    simpa [prefixWord, tailWord_1883822, baseEnd_1883822] using wordTrace_append hprefix tailTrace_1883822
  have hstable : (prefixWord ++ tailWord_1883822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883822).length < 2 ^ (prefixWord ++ tailWord_1883822).sum := by decide
  have hdescent : baseEnd_1883822 < baseStart_1883822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883834 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_1883834 : Nat := 118140960795 + 1883834 * 2 ^ 59
def prefixEnd_1883834 : Nat := 4983230072969 + 3 ^ 40 * 1883834 * 2
def baseEnd_1883834 : Nat := 107479146142454191612379

theorem tailTrace_1883834 : CollatzResearch.WordTrace tailWord_1883834 prefixEnd_1883834 107479146142454191612379 := by
  unfold tailWord_1883834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177267664299656519454639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45806047104799084051879037 17177267664299656519454639)
  ·
    refine ⟨25765901496449484779181959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17177267664299656519454639 25765901496449484779181959)
    ·
      refine ⟨38648852244674227168772939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25765901496449484779181959 38648852244674227168772939)
      ·
        refine ⟨57973278367011340753159409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38648852244674227168772939 57973278367011340753159409)
        ·
          refine ⟨43479958775258505564869557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57973278367011340753159409 43479958775258505564869557)
          ·
            refine ⟨4076246135180484896706521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43479958775258505564869557 4076246135180484896706521)
            ·
              refine ⟨3057184601385363672529891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076246135180484896706521 3057184601385363672529891)
              ·
                refine ⟨4585776902078045508794837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057184601385363672529891 4585776902078045508794837)
                ·
                  refine ⟨107479146142454191612379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4585776902078045508794837 107479146142454191612379)
                  ·
                    rfl

theorem cell23_1883834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_1883834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883834 prefixEnd_1883834 := by exact prefixLift 1883834
  have htrace : WordTrace (prefixWord ++ tailWord_1883834) baseStart_1883834 baseEnd_1883834 := by
    simpa [prefixWord, tailWord_1883834, baseEnd_1883834] using wordTrace_append hprefix tailTrace_1883834
  have hstable : (prefixWord ++ tailWord_1883834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883834).length < 2 ^ (prefixWord ++ tailWord_1883834).sum := by decide
  have hdescent : baseEnd_1883834 < baseStart_1883834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883847 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 7]
def baseStart_1883847 : Nat := 118140960795 + 1883847 * 2 ^ 59
def prefixEnd_1883847 : Nat := 4983230072969 + 3 ^ 40 * 1883847 * 2
def baseEnd_1883847 : Nat := 322439663510198724549617

theorem tailTrace_1883847 : CollatzResearch.WordTrace tailWord_1883847 prefixEnd_1883847 322439663510198724549617 := by
  unfold tailWord_1883847
  simp only [CollatzResearch.WordTrace]
  refine ⟨68709544806151529298041795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45806363204101019532027863 68709544806151529298041795)
  ·
    refine ⟨103064317209227293947062693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68709544806151529298041795 103064317209227293947062693)
    ·
      refine ⟨19324559476730117615074255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103064317209227293947062693 19324559476730117615074255)
      ·
        refine ⟨28986839215095176422611383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19324559476730117615074255 28986839215095176422611383)
        ·
          refine ⟨43480258822642764633917075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28986839215095176422611383 43480258822642764633917075)
          ·
            refine ⟨65220388233964146950875613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43480258822642764633917075 65220388233964146950875613)
            ·
              refine ⟨24457645587736555106578355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65220388233964146950875613 24457645587736555106578355)
              ·
                refine ⟨36686468381604832659867533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24457645587736555106578355 36686468381604832659867533)
                ·
                  refine ⟨13757425643101812247450325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36686468381604832659867533 13757425643101812247450325)
                  ·
                    refine ⟨322439663510198724549617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13757425643101812247450325 322439663510198724549617)
                    ·
                      rfl

theorem cell23_1883847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_1883847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883847 prefixEnd_1883847 := by exact prefixLift 1883847
  have htrace : WordTrace (prefixWord ++ tailWord_1883847) baseStart_1883847 baseEnd_1883847 := by
    simpa [prefixWord, tailWord_1883847, baseEnd_1883847] using wordTrace_append hprefix tailTrace_1883847
  have hstable : (prefixWord ++ tailWord_1883847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883847).length < 2 ^ (prefixWord ++ tailWord_1883847).sum := by decide
  have hdescent : baseEnd_1883847 < baseStart_1883847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883864 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_1883864 : Nat := 118140960795 + 1883864 * 2 ^ 59
def prefixEnd_1883864 : Nat := 4983230072969 + 3 ^ 40 * 1883864 * 2
def baseEnd_1883864 : Nat := 322442573233907535712091

theorem tailTrace_1883864 : CollatzResearch.WordTrace tailWord_1883864 prefixEnd_1883864 322442573233907535712091 := by
  unfold tailWord_1883864
  simp only [CollatzResearch.WordTrace]
  refine ⟨34355082423544970600705323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45806776564726627467607097 34355082423544970600705323)
  ·
    refine ⟨51532623635317455901057985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34355082423544970600705323 51532623635317455901057985)
    ·
      refine ⟨38649467726488091925793489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51532623635317455901057985 38649467726488091925793489)
      ·
        refine ⟨28987100794866068944345117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38649467726488091925793489 28987100794866068944345117)
        ·
          refine ⟨10870162798074775854129419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28987100794866068944345117 10870162798074775854129419)
          ·
            refine ⟨16305244197112163781194129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10870162798074775854129419 16305244197112163781194129)
            ·
              refine ⟨12228933147834122835895597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16305244197112163781194129 12228933147834122835895597)
              ·
                refine ⟨4585849930437796063460849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12228933147834122835895597 4585849930437796063460849)
                ·
                  refine ⟨3439387447828347047595637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4585849930437796063460849 3439387447828347047595637)
                  ·
                    refine ⟨322442573233907535712091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3439387447828347047595637 322442573233907535712091)
                    ·
                      rfl

theorem cell23_1883864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_1883864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883864 prefixEnd_1883864 := by exact prefixLift 1883864
  have htrace : WordTrace (prefixWord ++ tailWord_1883864) baseStart_1883864 baseEnd_1883864 := by
    simpa [prefixWord, tailWord_1883864, baseEnd_1883864] using wordTrace_append hprefix tailTrace_1883864
  have hstable : (prefixWord ++ tailWord_1883864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883864).length < 2 ^ (prefixWord ++ tailWord_1883864).sum := by decide
  have hdescent : baseEnd_1883864 < baseStart_1883864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883884 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_1883884 : Nat := 118140960795 + 1883884 * 2 ^ 59
def prefixEnd_1883884 : Nat := 4983230072969 + 3 ^ 40 * 1883884 * 2
def baseEnd_1883884 : Nat := 967337989314812528886181

theorem tailTrace_1883884 : CollatzResearch.WordTrace tailWord_1883884 prefixEnd_1883884 967337989314812528886181 := by
  unfold tailWord_1883884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34355447153508742308569353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45807262871344989744759137 34355447153508742308569353)
  ·
    refine ⟨25766585365131556731427015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34355447153508742308569353 25766585365131556731427015)
    ·
      refine ⟨38649878047697335097140523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25766585365131556731427015 38649878047697335097140523)
      ·
        refine ⟨57974817071546002645710785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38649878047697335097140523 57974817071546002645710785)
        ·
          refine ⟨43481112803659501984283089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57974817071546002645710785 43481112803659501984283089)
          ·
            refine ⟨32610834602744626488212317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43481112803659501984283089 32610834602744626488212317)
            ·
              refine ⟨12229062976029234933079619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32610834602744626488212317 12229062976029234933079619)
              ·
                refine ⟨18343594464043852399619429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229062976029234933079619 18343594464043852399619429)
                ·
                  refine ⟨3439423962008222324928643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18343594464043852399619429 3439423962008222324928643)
                  ·
                    refine ⟨5159135943012333487392965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439423962008222324928643 5159135943012333487392965)
                    ·
                      refine ⟨967337989314812528886181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5159135943012333487392965 967337989314812528886181)
                      ·
                        rfl

theorem cell23_1883884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_1883884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883884 prefixEnd_1883884 := by exact prefixLift 1883884
  have htrace : WordTrace (prefixWord ++ tailWord_1883884) baseStart_1883884 baseEnd_1883884 := by
    simpa [prefixWord, tailWord_1883884, baseEnd_1883884] using wordTrace_append hprefix tailTrace_1883884
  have hstable : (prefixWord ++ tailWord_1883884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883884).length < 2 ^ (prefixWord ++ tailWord_1883884).sum := by decide
  have hdescent : baseEnd_1883884 < baseStart_1883884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883941 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 6]
def baseStart_1883941 : Nat := 118140960795 + 1883941 * 2 ^ 59
def prefixEnd_1883941 : Nat := 4983230072969 + 3 ^ 40 * 1883941 * 2
def baseEnd_1883941 : Nat := 107485250856902089541491

theorem tailTrace_1883941 : CollatzResearch.WordTrace tailWord_1883941 prefixEnd_1883941 107485250856902089541491 := by
  unfold tailWord_1883941
  simp only [CollatzResearch.WordTrace]
  refine ⟨68712973267810983351963677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45808648845207322234642451 68712973267810983351963677)
  ·
    refine ⟨25767364975429118756986379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68712973267810983351963677 25767364975429118756986379)
    ·
      refine ⟨38651047463143678135479569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25767364975429118756986379 38651047463143678135479569)
      ·
        refine ⟨28988285597357758601609677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38651047463143678135479569 28988285597357758601609677)
        ·
          refine ⟨10870607099009159475603629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28988285597357758601609677 10870607099009159475603629)
          ·
            refine ⟨4076477662128434803351361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10870607099009159475603629 4076477662128434803351361)
            ·
              refine ⟨3057358246596326102513521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076477662128434803351361 3057358246596326102513521)
              ·
                refine ⟨2293018684947244576885141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057358246596326102513521 2293018684947244576885141)
                ·
                  refine ⟨107485250856902089541491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293018684947244576885141 107485250856902089541491)
                  ·
                    rfl

theorem cell23_1883941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_1883941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883941 prefixEnd_1883941 := by exact prefixLift 1883941
  have htrace : WordTrace (prefixWord ++ tailWord_1883941) baseStart_1883941 baseEnd_1883941 := by
    simpa [prefixWord, tailWord_1883941, baseEnd_1883941] using wordTrace_append hprefix tailTrace_1883941
  have hstable : (prefixWord ++ tailWord_1883941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883941).length < 2 ^ (prefixWord ++ tailWord_1883941).sum := by decide
  have hdescent : baseEnd_1883941 < baseStart_1883941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883958 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1883958 : Nat := 118140960795 + 1883958 * 2 ^ 59
def prefixEnd_1883958 : Nat := 4983230072969 + 3 ^ 40 * 1883958 * 2
def baseEnd_1883958 : Nat := 107486220764805026595649

theorem tailTrace_1883958 : CollatzResearch.WordTrace tailWord_1883958 prefixEnd_1883958 107486220764805026595649 := by
  unfold tailWord_1883958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294599581796837203458283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45809062205832930170221685 4294599581796837203458283)
  ·
    refine ⟨6441899372695255805187425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294599581796837203458283 6441899372695255805187425)
    ·
      refine ⟨4831424529521441853890569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6441899372695255805187425 4831424529521441853890569)
      ·
        refine ⟨3623568397141081390417927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4831424529521441853890569 3623568397141081390417927)
        ·
          refine ⟨5435352595711622085626891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623568397141081390417927 5435352595711622085626891)
          ·
            refine ⟨8153028893567433128440337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435352595711622085626891 8153028893567433128440337)
            ·
              refine ⟨6114771670175574846330253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153028893567433128440337 6114771670175574846330253)
              ·
                refine ⟨2293039376315840567373845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6114771670175574846330253 2293039376315840567373845)
                ·
                  refine ⟨107486220764805026595649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293039376315840567373845 107486220764805026595649)
                  ·
                    rfl

theorem cell23_1883958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1883958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883958 prefixEnd_1883958 := by exact prefixLift 1883958
  have htrace : WordTrace (prefixWord ++ tailWord_1883958) baseStart_1883958 baseEnd_1883958 := by
    simpa [prefixWord, tailWord_1883958, baseEnd_1883958] using wordTrace_append hprefix tailTrace_1883958
  have hstable : (prefixWord ++ tailWord_1883958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883958).length < 2 ^ (prefixWord ++ tailWord_1883958).sum := by decide
  have hdescent : baseEnd_1883958 < baseStart_1883958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883985 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 1, 1, 3]
def baseStart_1883985 : Nat := 118140960795 + 1883985 * 2 ^ 59
def prefixEnd_1883985 : Nat := 4983230072969 + 3 ^ 40 * 1883985 * 2
def baseEnd_1883985 : Nat := 967389850860916633723217

theorem tailTrace_1883985 : CollatzResearch.WordTrace tailWord_1883985 prefixEnd_1883985 967389850860916633723217 := by
  unfold tailWord_1883985
  simp only [CollatzResearch.WordTrace]
  refine ⟨68714578079651578866565409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45809718719767719244376939 68714578079651578866565409)
  ·
    refine ⟨51535933559738684149924057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68714578079651578866565409 51535933559738684149924057)
    ·
      refine ⟨38651950169804013112443043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51535933559738684149924057 38651950169804013112443043)
      ·
        refine ⟨57977925254706019668664565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38651950169804013112443043 57977925254706019668664565)
        ·
          refine ⟨5435430492628689343937303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57977925254706019668664565 5435430492628689343937303)
          ·
            refine ⟨8153145738943034015905955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435430492628689343937303 8153145738943034015905955)
            ·
              refine ⟨12229718608414551023858933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8153145738943034015905955 12229718608414551023858933)
              ·
                refine ⟨1146536119538864158486775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12229718608414551023858933 1146536119538864158486775)
                ·
                  refine ⟨1719804179308296237730163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146536119538864158486775 1719804179308296237730163)
                  ·
                    refine ⟨2579706268962444356595245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719804179308296237730163 2579706268962444356595245)
                    ·
                      refine ⟨967389850860916633723217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579706268962444356595245 967389850860916633723217)
                      ·
                        rfl

theorem cell23_1883985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_1883985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883985 prefixEnd_1883985 := by exact prefixLift 1883985
  have htrace : WordTrace (prefixWord ++ tailWord_1883985) baseStart_1883985 baseEnd_1883985 := by
    simpa [prefixWord, tailWord_1883985, baseEnd_1883985] using wordTrace_append hprefix tailTrace_1883985
  have hstable : (prefixWord ++ tailWord_1883985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883985).length < 2 ^ (prefixWord ++ tailWord_1883985).sum := by decide
  have hdescent : baseEnd_1883985 < baseStart_1883985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883988 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1883988 : Nat := 118140960795 + 1883988 * 2 ^ 59
def prefixEnd_1883988 : Nat := 4983230072969 + 3 ^ 40 * 1883988 * 2
def baseEnd_1883988 : Nat := 322463797100960040661901

theorem tailTrace_1883988 : CollatzResearch.WordTrace tailWord_1883988 prefixEnd_1883988 322463797100960040661901 := by
  unfold tailWord_1883988
  simp only [CollatzResearch.WordTrace]
  refine ⟨34357343749320355189462309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45809791665760473585949745 34357343749320355189462309)
  ·
    refine ⟨6442001952997566598024183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34357343749320355189462309 6442001952997566598024183)
    ·
      refine ⟨9663002929496349897036275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442001952997566598024183 9663002929496349897036275)
      ·
        refine ⟨14494504394244524845554413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9663002929496349897036275 14494504394244524845554413)
        ·
          refine ⟨5435439147841696817082905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14494504394244524845554413 5435439147841696817082905)
          ·
            refine ⟨4076579360881272612812179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435439147841696817082905 4076579360881272612812179)
            ·
              refine ⟨6114869041321908919218269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076579360881272612812179 6114869041321908919218269)
              ·
                refine ⟨2293075890495715844706851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6114869041321908919218269 2293075890495715844706851)
                ·
                  refine ⟨3439613835743573767060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293075890495715844706851 3439613835743573767060277)
                  ·
                    refine ⟨322463797100960040661901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3439613835743573767060277 322463797100960040661901)
                    ·
                      rfl

theorem cell23_1883988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1883988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1883988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1883988 prefixEnd_1883988 := by exact prefixLift 1883988
  have htrace : WordTrace (prefixWord ++ tailWord_1883988) baseStart_1883988 baseEnd_1883988 := by
    simpa [prefixWord, tailWord_1883988, baseEnd_1883988] using wordTrace_append hprefix tailTrace_1883988
  have hstable : (prefixWord ++ tailWord_1883988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883988).length < 2 ^ (prefixWord ++ tailWord_1883988).sum := by decide
  have hdescent : baseEnd_1883988 < baseStart_1883988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884001 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_1884001 : Nat := 118140960795 + 1884001 * 2 ^ 59
def prefixEnd_1884001 : Nat := 4983230072969 + 3 ^ 40 * 1884001 * 2
def baseEnd_1884001 : Nat := 322466022183796190374381

theorem tailTrace_1884001 : CollatzResearch.WordTrace tailWord_1884001 prefixEnd_1884001 322466022183796190374381 := by
  unfold tailWord_1884001
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715161647593613599147857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45810107765062409066098571 68715161647593613599147857)
  ·
    refine ⟨51536371235695210199360893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68715161647593613599147857 51536371235695210199360893)
    ·
      refine ⟨19326139213385703824760335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51536371235695210199360893 19326139213385703824760335)
      ·
        refine ⟨28989208820078555737140503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19326139213385703824760335 28989208820078555737140503)
        ·
          refine ⟨43483813230117833605710755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28989208820078555737140503 43483813230117833605710755)
          ·
            refine ⟨65225719845176750408566133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43483813230117833605710755 65225719845176750408566133)
            ·
              refine ⟨6114911235485320350803075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65225719845176750408566133 6114911235485320350803075)
              ·
                refine ⟨9172366853227980526204613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114911235485320350803075 9172366853227980526204613)
                ·
                  refine ⟨1719818784980246348663365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9172366853227980526204613 1719818784980246348663365)
                  ·
                    refine ⟨322466022183796190374381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1719818784980246348663365 322466022183796190374381)
                    ·
                      rfl

theorem cell23_1884001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_1884001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884001 prefixEnd_1884001 := by exact prefixLift 1884001
  have htrace : WordTrace (prefixWord ++ tailWord_1884001) baseStart_1884001 baseEnd_1884001 := by
    simpa [prefixWord, tailWord_1884001, baseEnd_1884001] using wordTrace_append hprefix tailTrace_1884001
  have hstable : (prefixWord ++ tailWord_1884001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884001).length < 2 ^ (prefixWord ++ tailWord_1884001).sum := by decide
  have hdescent : baseEnd_1884001 < baseStart_1884001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884002 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1884002 : Nat := 118140960795 + 1884002 * 2 ^ 59
def prefixEnd_1884002 : Nat := 4983230072969 + 3 ^ 40 * 1884002 * 2
def baseEnd_1884002 : Nat := 967398580032043067210639

theorem tailTrace_1884002 : CollatzResearch.WordTrace tailWord_1884002 prefixEnd_1884002 967398580032043067210639 := by
  unfold tailWord_1884002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17178799530147497692483565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45810132080393327179956173 17178799530147497692483565)
  ·
    refine ⟨6442049823805311634681337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17178799530147497692483565 6442049823805311634681337)
    ·
      refine ⟨4831537367853983726011003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6442049823805311634681337 4831537367853983726011003)
      ·
        refine ⟨7247306051780975589016505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831537367853983726011003 7247306051780975589016505)
        ·
          refine ⟨5435479538835731691762379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247306051780975589016505 5435479538835731691762379)
          ·
            refine ⟨8153219308253597537643569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435479538835731691762379 8153219308253597537643569)
            ·
              refine ⟨6114914481190198153232677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153219308253597537643569 6114914481190198153232677)
              ·
                refine ⟨1146546465223162153731127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6114914481190198153232677 1146546465223162153731127)
                ·
                  refine ⟨1719819697834743230596691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146546465223162153731127 1719819697834743230596691)
                  ·
                    refine ⟨2579729546752114845895037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1719819697834743230596691 2579729546752114845895037)
                    ·
                      refine ⟨967398580032043067210639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579729546752114845895037 967398580032043067210639)
                      ·
                        rfl

theorem cell23_1884002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1884002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884002 prefixEnd_1884002 := by exact prefixLift 1884002
  have htrace : WordTrace (prefixWord ++ tailWord_1884002) baseStart_1884002 baseEnd_1884002 := by
    simpa [prefixWord, tailWord_1884002, baseEnd_1884002] using wordTrace_append hprefix tailTrace_1884002
  have hstable : (prefixWord ++ tailWord_1884002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884002).length < 2 ^ (prefixWord ++ tailWord_1884002).sum := by decide
  have hdescent : baseEnd_1884002 < baseStart_1884002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884021 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1884021 : Nat := 118140960795 + 1884021 * 2 ^ 59
def prefixEnd_1884021 : Nat := 4983230072969 + 3 ^ 40 * 1884021 * 2
def baseEnd_1884021 : Nat := 967408336164478492873051

theorem tailTrace_1884021 : CollatzResearch.WordTrace tailWord_1884021 prefixEnd_1884021 967408336164478492873051 := by
  unfold tailWord_1884021
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715891107521157014875917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45810594071680771343250611 68715891107521157014875917)
  ·
    refine ⟨25768459165320433880578469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68715891107521157014875917 25768459165320433880578469)
    ·
      refine ⟨4831586093497581352608463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25768459165320433880578469 4831586093497581352608463)
      ·
        refine ⟨7247379140246372028912695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831586093497581352608463 7247379140246372028912695)
        ·
          refine ⟨10871068710369558043369043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247379140246372028912695 10871068710369558043369043)
          ·
            refine ⟨16306603065554337065053565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871068710369558043369043 16306603065554337065053565)
            ·
              refine ⟨6114976149582876399395087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16306603065554337065053565 6114976149582876399395087)
              ·
                refine ⟨9172464224374314599092631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114976149582876399395087 9172464224374314599092631)
                ·
                  refine ⟨13758696336561471898638947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172464224374314599092631 13758696336561471898638947)
                  ·
                    refine ⟨20638044504842207847958421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13758696336561471898638947 20638044504842207847958421)
                    ·
                      refine ⟨967408336164478492873051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20638044504842207847958421 967408336164478492873051)
                      ·
                        rfl

theorem cell23_1884021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1884021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884021 prefixEnd_1884021 := by exact prefixLift 1884021
  have htrace : WordTrace (prefixWord ++ tailWord_1884021) baseStart_1884021 baseEnd_1884021 := by
    simpa [prefixWord, tailWord_1884021, baseEnd_1884021] using wordTrace_append hprefix tailTrace_1884021
  have hstable : (prefixWord ++ tailWord_1884021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884021).length < 2 ^ (prefixWord ++ tailWord_1884021).sum := by decide
  have hdescent : baseEnd_1884021 < baseStart_1884021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884041 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_1884041 : Nat := 118140960795 + 1884041 * 2 ^ 59
def prefixEnd_1884041 : Nat := 4983230072969 + 3 ^ 40 * 1884041 * 2
def baseEnd_1884041 : Nat := 967418605777568414622959

theorem tailTrace_1884041 : CollatzResearch.WordTrace tailWord_1884041 prefixEnd_1884041 967418605777568414622959 := by
  unfold tailWord_1884041
  simp only [CollatzResearch.WordTrace]
  refine ⟨68716620567448700430603977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45811080378299133620402651 68716620567448700430603977)
  ·
    refine ⟨51537465425586525322952983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68716620567448700430603977 51537465425586525322952983)
    ·
      refine ⟨77306198138379787984429475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51537465425586525322952983 77306198138379787984429475)
      ·
        refine ⟨115959297207569681976644213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77306198138379787984429475 115959297207569681976644213)
        ·
          refine ⟨10871184113209657685310395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115959297207569681976644213 10871184113209657685310395)
          ·
            refine ⟨16306776169814486527965593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871184113209657685310395 16306776169814486527965593)
            ·
              refine ⟨12230082127360864895974195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306776169814486527965593 12230082127360864895974195)
              ·
                refine ⟨18345123191041297343961293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12230082127360864895974195 18345123191041297343961293)
                ·
                  refine ⟨6879421196640486503985485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18345123191041297343961293 6879421196640486503985485)
                  ·
                    refine ⟨2579782948740182438994557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6879421196640486503985485 2579782948740182438994557)
                    ·
                      refine ⟨967418605777568414622959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2579782948740182438994557 967418605777568414622959)
                      ·
                        rfl

theorem cell23_1884041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_1884041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884041 prefixEnd_1884041 := by exact prefixLift 1884041
  have htrace : WordTrace (prefixWord ++ tailWord_1884041) baseStart_1884041 baseEnd_1884041 := by
    simpa [prefixWord, tailWord_1884041, baseEnd_1884041] using wordTrace_append hprefix tailTrace_1884041
  have hstable : (prefixWord ++ tailWord_1884041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884041).length < 2 ^ (prefixWord ++ tailWord_1884041).sum := by decide
  have hdescent : baseEnd_1884041 < baseStart_1884041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884044 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1884044 : Nat := 118140960795 + 1884044 * 2 ^ 59
def prefixEnd_1884044 : Nat := 4983230072969 + 3 ^ 40 * 1884044 * 2
def baseEnd_1884044 : Nat := 322473382073177300961815

theorem tailTrace_1884044 : CollatzResearch.WordTrace tailWord_1884044 prefixEnd_1884044 322473382073177300961815 := by
  unfold tailWord_1884044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34358364993218915971481593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45811153324291887961975457 34358364993218915971481593)
  ·
    refine ⟨25768773744914186978611195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34358364993218915971481593 25768773744914186978611195)
    ·
      refine ⟨38653160617371280467916793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768773744914186978611195 38653160617371280467916793)
      ·
        refine ⟨28989870463028460350937595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38653160617371280467916793 28989870463028460350937595)
        ·
          refine ⟨43484805694542690526406393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28989870463028460350937595 43484805694542690526406393)
          ·
            refine ⟨32613604270907017894804795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43484805694542690526406393 32613604270907017894804795)
            ·
              refine ⟨48920406406360526842207193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32613604270907017894804795 48920406406360526842207193)
              ·
                refine ⟨36690304804770395131655395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48920406406360526842207193 36690304804770395131655395)
                ·
                  refine ⟨55035457207155592697483093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36690304804770395131655395 55035457207155592697483093)
                  ·
                    refine ⟨322473382073177300961815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55035457207155592697483093 322473382073177300961815)
                    ·
                      rfl

theorem cell23_1884044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1884044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884044 prefixEnd_1884044 := by exact prefixLift 1884044
  have htrace : WordTrace (prefixWord ++ tailWord_1884044) baseStart_1884044 baseEnd_1884044 := by
    simpa [prefixWord, tailWord_1884044, baseEnd_1884044] using wordTrace_append hprefix tailTrace_1884044
  have hstable : (prefixWord ++ tailWord_1884044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884044).length < 2 ^ (prefixWord ++ tailWord_1884044).sum := by decide
  have hdescent : baseEnd_1884044 < baseStart_1884044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884051 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 9, 2]
def baseStart_1884051 : Nat := 118140960795 + 1884051 * 2 ^ 59
def prefixEnd_1884051 : Nat := 4983230072969 + 3 ^ 40 * 1884051 * 2
def baseEnd_1884051 : Nat := 967423740584113375497913

theorem tailTrace_1884051 : CollatzResearch.WordTrace tailWord_1884051 prefixEnd_1884051 967423740584113375497913 := by
  unfold tailWord_1884051
  simp only [CollatzResearch.WordTrace]
  refine ⟨68716985297412472138468007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45811323531608314758978671 68716985297412472138468007)
  ·
    refine ⟨103075477946118708207702011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68716985297412472138468007 103075477946118708207702011)
    ·
      refine ⟨154613216919178062311553017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103075477946118708207702011 154613216919178062311553017)
      ·
        refine ⟨115959912689383546733664763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154613216919178062311553017 115959912689383546733664763)
        ·
          refine ⟨173939869034075320100497145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115959912689383546733664763 173939869034075320100497145)
          ·
            refine ⟨130454901775556490075372859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173939869034075320100497145 130454901775556490075372859)
            ·
              refine ⟨195682352663334735113059289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130454901775556490075372859 195682352663334735113059289)
              ·
                refine ⟨146761764497501051334794467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195682352663334735113059289 146761764497501051334794467)
                ·
                  refine ⟨220142646746251577002191701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146761764497501051334794467 220142646746251577002191701)
                  ·
                    refine ⟨1289898320778817833997217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220142646746251577002191701 1289898320778817833997217)
                    ·
                      refine ⟨967423740584113375497913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289898320778817833997217 967423740584113375497913)
                      ·
                        rfl

theorem cell23_1884051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9, 2].length) (baseStart_1884051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884051 prefixEnd_1884051 := by exact prefixLift 1884051
  have htrace : WordTrace (prefixWord ++ tailWord_1884051) baseStart_1884051 baseEnd_1884051 := by
    simpa [prefixWord, tailWord_1884051, baseEnd_1884051] using wordTrace_append hprefix tailTrace_1884051
  have hstable : (prefixWord ++ tailWord_1884051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884051).length < 2 ^ (prefixWord ++ tailWord_1884051).sum := by decide
  have hdescent : baseEnd_1884051 < baseStart_1884051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884085 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1884085 : Nat := 118140960795 + 1884085 * 2 ^ 59
def prefixEnd_1884085 : Nat := 4983230072969 + 3 ^ 40 * 1884085 * 2
def baseEnd_1884085 : Nat := 967441198926366242472757

theorem tailTrace_1884085 : CollatzResearch.WordTrace tailWord_1884085 prefixEnd_1884085 967441198926366242472757 := by
  unfold tailWord_1884085
  simp only [CollatzResearch.WordTrace]
  refine ⟨68718225379289295945205709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45812150252859530630137139 68718225379289295945205709)
  ·
    refine ⟨25769334517233485979452141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68718225379289295945205709 25769334517233485979452141)
    ·
      refine ⟨9663500443962557242294553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25769334517233485979452141 9663500443962557242294553)
      ·
        refine ⟨7247625332971917931720915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9663500443962557242294553 7247625332971917931720915)
        ·
          refine ⟨10871437999457876897581373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247625332971917931720915 10871437999457876897581373)
          ·
            refine ⟨4076789249796703836593015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10871437999457876897581373 4076789249796703836593015)
            ·
              refine ⟨6115183874695055754889523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076789249796703836593015 6115183874695055754889523)
              ·
                refine ⟨9172775812042583632334285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115183874695055754889523 9172775812042583632334285)
                ·
                  refine ⟨3439790929515968862125357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9172775812042583632334285 3439790929515968862125357)
                  ·
                    refine ⟨1289921598568488323297009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439790929515968862125357 1289921598568488323297009)
                    ·
                      refine ⟨967441198926366242472757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1289921598568488323297009 967441198926366242472757)
                      ·
                        rfl

theorem cell23_1884085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1884085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884085 prefixEnd_1884085 := by exact prefixLift 1884085
  have htrace : WordTrace (prefixWord ++ tailWord_1884085) baseStart_1884085 baseEnd_1884085 := by
    simpa [prefixWord, tailWord_1884085, baseEnd_1884085] using wordTrace_append hprefix tailTrace_1884085
  have hstable : (prefixWord ++ tailWord_1884085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884085).length < 2 ^ (prefixWord ++ tailWord_1884085).sum := by decide
  have hdescent : baseEnd_1884085 < baseStart_1884085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884111 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_1884111 : Nat := 118140960795 + 1884111 * 2 ^ 59
def prefixEnd_1884111 : Nat := 4983230072969 + 3 ^ 40 * 1884111 * 2
def baseEnd_1884111 : Nat := 967454549423383140747637

theorem tailTrace_1884111 : CollatzResearch.WordTrace tailWord_1884111 prefixEnd_1884111 967454549423383140747637 := by
  unfold tailWord_1884111
  simp only [CollatzResearch.WordTrace]
  refine ⟨68719173677195102385652187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45812782451463401590434791 68719173677195102385652187)
  ·
    refine ⟨103078760515792653578478281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68719173677195102385652187 103078760515792653578478281)
    ·
      refine ⟨77309070386844490183858711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103078760515792653578478281 77309070386844490183858711)
      ·
        refine ⟨115963605580266735275788067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77309070386844490183858711 115963605580266735275788067)
        ·
          refine ⟨173945408370400102913682101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115963605580266735275788067 173945408370400102913682101)
          ·
            refine ⟨16307382034725009648157697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173945408370400102913682101 16307382034725009648157697)
            ·
              refine ⟨12230536526043757236118273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16307382034725009648157697 12230536526043757236118273)
              ·
                refine ⟨9172902394532817927088705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12230536526043757236118273 9172902394532817927088705)
                ·
                  refine ⟨6879676795899613445316529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9172902394532817927088705 6879676795899613445316529)
                  ·
                    refine ⟨5159757596924710083987397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879676795899613445316529 5159757596924710083987397)
                    ·
                      refine ⟨967454549423383140747637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5159757596924710083987397 967454549423383140747637)
                      ·
                        rfl

theorem cell23_1884111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_1884111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884111 prefixEnd_1884111 := by exact prefixLift 1884111
  have htrace : WordTrace (prefixWord ++ tailWord_1884111) baseStart_1884111 baseEnd_1884111 := by
    simpa [prefixWord, tailWord_1884111, baseEnd_1884111] using wordTrace_append hprefix tailTrace_1884111
  have hstable : (prefixWord ++ tailWord_1884111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884111).length < 2 ^ (prefixWord ++ tailWord_1884111).sum := by decide
  have hdescent : baseEnd_1884111 < baseStart_1884111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884188 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1884188 : Nat := 118140960795 + 1884188 * 2 ^ 59
def prefixEnd_1884188 : Nat := 4983230072969 + 3 ^ 40 * 1884188 * 2
def baseEnd_1884188 : Nat := 967494087433779339484783

theorem tailTrace_1884188 : CollatzResearch.WordTrace tailWord_1884188 prefixEnd_1884188 967494087433779339484783 := by
  unfold tailWord_1884188
  simp only [CollatzResearch.WordTrace]
  refine ⟨34360991048958072268102609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45814654731944096357470145 34360991048958072268102609)
  ·
    refine ⟨25770743286718554201076957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34360991048958072268102609 25770743286718554201076957)
    ·
      refine ⟨9664028732519457825403859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25770743286718554201076957 9664028732519457825403859)
      ·
        refine ⟨14496043098779186738105789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664028732519457825403859 14496043098779186738105789)
        ·
          refine ⟨5436016162042195026789671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14496043098779186738105789 5436016162042195026789671)
          ·
            refine ⟨8154024243063292540184507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436016162042195026789671 8154024243063292540184507)
            ·
              refine ⟨12231036364594938810276761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154024243063292540184507 12231036364594938810276761)
              ·
                refine ⟨9173277273446204107707571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12231036364594938810276761 9173277273446204107707571)
                ·
                  refine ⟨13759915910169306161561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173277273446204107707571 13759915910169306161561357)
                  ·
                    refine ⟨5159968466313489810585509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13759915910169306161561357 5159968466313489810585509)
                    ·
                      refine ⟨967494087433779339484783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5159968466313489810585509 967494087433779339484783)
                      ·
                        rfl

theorem cell23_1884188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1884188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884188 prefixEnd_1884188 := by exact prefixLift 1884188
  have htrace : WordTrace (prefixWord ++ tailWord_1884188) baseStart_1884188 baseEnd_1884188 := by
    simpa [prefixWord, tailWord_1884188, baseEnd_1884188] using wordTrace_append hprefix tailTrace_1884188
  have hstable : (prefixWord ++ tailWord_1884188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884188).length < 2 ^ (prefixWord ++ tailWord_1884188).sum := by decide
  have hdescent : baseEnd_1884188 < baseStart_1884188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884208 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_1884208 : Nat := 118140960795 + 1884208 * 2 ^ 59
def prefixEnd_1884208 : Nat := 4983230072969 + 3 ^ 40 * 1884208 * 2
def baseEnd_1884208 : Nat := 967504357046869261234691

theorem tailTrace_1884208 : CollatzResearch.WordTrace tailWord_1884208 prefixEnd_1884208 967504357046869261234691 := by
  unfold tailWord_1884208
  simp only [CollatzResearch.WordTrace]
  refine ⟨34361355778921843975966639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45815141038562458634622185 34361355778921843975966639)
  ·
    refine ⟨51542033668382765963949959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34361355778921843975966639 51542033668382765963949959)
    ·
      refine ⟨77313050502574148945924939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51542033668382765963949959 77313050502574148945924939)
      ·
        refine ⟨115969575753861223418887409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77313050502574148945924939 115969575753861223418887409)
        ·
          refine ⟨86977181815395917564165557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115969575753861223418887409 86977181815395917564165557)
          ·
            refine ⟨8154110795193367271640521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86977181815395917564165557 8154110795193367271640521)
            ·
              refine ⟨6115583096395025453730391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8154110795193367271640521 6115583096395025453730391)
              ·
                refine ⟨9173374644592538180595587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115583096395025453730391 9173374644592538180595587)
                ·
                  refine ⟨13760061966888807270893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173374644592538180595587 13760061966888807270893381)
                  ·
                    refine ⟨2580011618791651363292509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13760061966888807270893381 2580011618791651363292509)
                    ·
                      refine ⟨967504357046869261234691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580011618791651363292509 967504357046869261234691)
                      ·
                        rfl

theorem cell23_1884208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_1884208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884208 prefixEnd_1884208 := by exact prefixLift 1884208
  have htrace : WordTrace (prefixWord ++ tailWord_1884208) baseStart_1884208 baseEnd_1884208 := by
    simpa [prefixWord, tailWord_1884208, baseEnd_1884208] using wordTrace_append hprefix tailTrace_1884208
  have hstable : (prefixWord ++ tailWord_1884208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884208).length < 2 ^ (prefixWord ++ tailWord_1884208).sum := by decide
  have hdescent : baseEnd_1884208 < baseStart_1884208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884211 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 8]
def baseStart_1884211 : Nat := 118140960795 + 1884211 * 2 ^ 59
def prefixEnd_1884211 : Nat := 4983230072969 + 3 ^ 40 * 1884211 * 2
def baseEnd_1884211 : Nat := 107500655276536972166353

theorem tailTrace_1884211 : CollatzResearch.WordTrace tailWord_1884211 prefixEnd_1884211 107500655276536972166353 := by
  unfold tailWord_1884211
  simp only [CollatzResearch.WordTrace]
  refine ⟨68722820976832819464292487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45815213984555212976194991 68722820976832819464292487)
  ·
    refine ⟨103084231465249229196438731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68722820976832819464292487 103084231465249229196438731)
    ·
      refine ⟨154626347197873843794658097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103084231465249229196438731 154626347197873843794658097)
      ·
        refine ⟨115969760398405382845993573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154626347197873843794658097 115969760398405382845993573)
        ·
          refine ⟨21744330074701009283623795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115969760398405382845993573 21744330074701009283623795)
          ·
            refine ⟨32616495112051513925435693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744330074701009283623795 32616495112051513925435693)
            ·
              refine ⟨12231185667019317722038385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32616495112051513925435693 12231185667019317722038385)
              ·
                refine ⟨9173389250264488291528789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12231185667019317722038385 9173389250264488291528789)
                ·
                  refine ⟨107500655276536972166353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9173389250264488291528789 107500655276536972166353)
                  ·
                    rfl

theorem cell23_1884211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 8].length) (baseStart_1884211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884211 prefixEnd_1884211 := by exact prefixLift 1884211
  have htrace : WordTrace (prefixWord ++ tailWord_1884211) baseStart_1884211 baseEnd_1884211 := by
    simpa [prefixWord, tailWord_1884211, baseEnd_1884211] using wordTrace_append hprefix tailTrace_1884211
  have hstable : (prefixWord ++ tailWord_1884211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884211).length < 2 ^ (prefixWord ++ tailWord_1884211).sum := by decide
  have hdescent : baseEnd_1884211 < baseStart_1884211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884222 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1884222 : Nat := 118140960795 + 1884222 * 2 ^ 59
def prefixEnd_1884222 : Nat := 4983230072969 + 3 ^ 40 * 1884222 * 2
def baseEnd_1884222 : Nat := 967511545776032206459627

theorem tailTrace_1884222 : CollatzResearch.WordTrace tailWord_1884222 prefixEnd_1884222 967511545776032206459627 := by
  unfold tailWord_1884222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590402772474121042867865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45815481453195312228628613 8590402772474121042867865)
  ·
    refine ⟨6442802079355590782150899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8590402772474121042867865 6442802079355590782150899)
    ·
      refine ⟨9664203119033386173226349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442802079355590782150899 9664203119033386173226349)
      ·
        refine ⟨3624076169637519814959881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9664203119033386173226349 3624076169637519814959881)
        ·
          refine ⟨2718057127228139861219911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624076169637519814959881 2718057127228139861219911)
          ·
            refine ⟨4077085690842209791829867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718057127228139861219911 4077085690842209791829867)
            ·
              refine ⟨6115628536263314687744801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077085690842209791829867 6115628536263314687744801)
              ·
                refine ⟨4586721402197486015808601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115628536263314687744801 4586721402197486015808601)
                ·
                  refine ⟨3440041051648114511856451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586721402197486015808601 3440041051648114511856451)
                  ·
                    refine ⟨5160061577472171767784677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440041051648114511856451 5160061577472171767784677)
                    ·
                      refine ⟨967511545776032206459627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5160061577472171767784677 967511545776032206459627)
                      ·
                        rfl

theorem cell23_1884222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1884222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884222 prefixEnd_1884222 := by exact prefixLift 1884222
  have htrace : WordTrace (prefixWord ++ tailWord_1884222) baseStart_1884222 baseEnd_1884222 := by
    simpa [prefixWord, tailWord_1884222, baseEnd_1884222] using wordTrace_append hprefix tailTrace_1884222
  have hstable : (prefixWord ++ tailWord_1884222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884222).length < 2 ^ (prefixWord ++ tailWord_1884222).sum := by decide
  have hdescent : baseEnd_1884222 < baseStart_1884222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884225 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1884225 : Nat := 118140960795 + 1884225 * 2 ^ 59
def prefixEnd_1884225 : Nat := 4983230072969 + 3 ^ 40 * 1884225 * 2
def baseEnd_1884225 : Nat := 967513086217995694722113

theorem tailTrace_1884225 : CollatzResearch.WordTrace tailWord_1884225 prefixEnd_1884225 967513086217995694722113 := by
  unfold tailWord_1884225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723331598782099855302129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45815554399188066570201419 68723331598782099855302129)
  ·
    refine ⟨51542498699086574891476597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68723331598782099855302129 51542498699086574891476597)
    ·
      refine ⟨4832109253039366396075931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51542498699086574891476597 4832109253039366396075931)
      ·
        refine ⟨7248163879559049594113897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832109253039366396075931 7248163879559049594113897)
        ·
          refine ⟨5436122909669287195585423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248163879559049594113897 5436122909669287195585423)
          ·
            refine ⟨8154184364503930793378135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436122909669287195585423 8154184364503930793378135)
            ·
              refine ⟨12231276546755896190067203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154184364503930793378135 12231276546755896190067203)
              ·
                refine ⟨18346914820133844285100805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231276546755896190067203 18346914820133844285100805)
                ·
                  refine ⟨3440046528775095803456401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18346914820133844285100805 3440046528775095803456401)
                  ·
                    refine ⟨2580034896581321852592301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440046528775095803456401 2580034896581321852592301)
                    ·
                      refine ⟨967513086217995694722113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580034896581321852592301 967513086217995694722113)
                      ·
                        rfl

theorem cell23_1884225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1884225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884225 prefixEnd_1884225 := by exact prefixLift 1884225
  have htrace : WordTrace (prefixWord ++ tailWord_1884225) baseStart_1884225 baseEnd_1884225 := by
    simpa [prefixWord, tailWord_1884225, baseEnd_1884225] using wordTrace_append hprefix tailTrace_1884225
  have hstable : (prefixWord ++ tailWord_1884225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884225).length < 2 ^ (prefixWord ++ tailWord_1884225).sum := by decide
  have hdescent : baseEnd_1884225 < baseStart_1884225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884241 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_1884241 : Nat := 118140960795 + 1884241 * 2 ^ 59
def prefixEnd_1884241 : Nat := 4983230072969 + 3 ^ 40 * 1884241 * 2
def baseEnd_1884241 : Nat := 322507100636155877374013

theorem tailTrace_1884241 : CollatzResearch.WordTrace tailWord_1884241 prefixEnd_1884241 322507100636155877374013 := by
  unfold tailWord_1884241
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723915166724134587884577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45815943444482756391923051 68723915166724134587884577)
  ·
    refine ⟨51542936375043100940913433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68723915166724134587884577 51542936375043100940913433)
    ·
      refine ⟨38657202281282325705685075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51542936375043100940913433 38657202281282325705685075)
      ·
        refine ⟨57985803421923488558527613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38657202281282325705685075 57985803421923488558527613)
        ·
          refine ⟨21744676283221308209447855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57985803421923488558527613 21744676283221308209447855)
          ·
            refine ⟨32617014424831962314171783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744676283221308209447855 32617014424831962314171783)
            ·
              refine ⟨48925521637247943471257675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32617014424831962314171783 48925521637247943471257675)
              ·
                refine ⟨73388282455871915206886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48925521637247943471257675 73388282455871915206886513)
                ·
                  refine ⟨55041211841903936405164885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73388282455871915206886513 55041211841903936405164885)
                  ·
                    refine ⟨322507100636155877374013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55041211841903936405164885 322507100636155877374013)
                    ·
                      rfl

theorem cell23_1884241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_1884241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884241 prefixEnd_1884241 := by exact prefixLift 1884241
  have htrace : WordTrace (prefixWord ++ tailWord_1884241) baseStart_1884241 baseEnd_1884241 := by
    simpa [prefixWord, tailWord_1884241, baseEnd_1884241] using wordTrace_append hprefix tailTrace_1884241
  have hstable : (prefixWord ++ tailWord_1884241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884241).length < 2 ^ (prefixWord ++ tailWord_1884241).sum := by decide
  have hdescent : baseEnd_1884241 < baseStart_1884241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884245 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 6]
def baseStart_1884245 : Nat := 118140960795 + 1884245 * 2 ^ 59
def prefixEnd_1884245 : Nat := 4983230072969 + 3 ^ 40 * 1884245 * 2
def baseEnd_1884245 : Nat := 107502595092342846274669

theorem tailTrace_1884245 : CollatzResearch.WordTrace tailWord_1884245 prefixEnd_1884245 107502595092342846274669 := by
  unfold tailWord_1884245
  simp only [CollatzResearch.WordTrace]
  refine ⟨68724061058709643271030189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45816040705806428847353459 68724061058709643271030189)
  ·
    refine ⟨25771522897016116226636321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68724061058709643271030189 25771522897016116226636321)
    ·
      refine ⟨19328642172762087169977241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25771522897016116226636321 19328642172762087169977241)
      ·
        refine ⟨14496481629571565377482931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19328642172762087169977241 14496481629571565377482931)
        ·
          refine ⟨21744722444357348066224397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496481629571565377482931 21744722444357348066224397)
          ·
            refine ⟨8154270916634005524834149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21744722444357348066224397 8154270916634005524834149)
            ·
              refine ⟨1528925796868876035906403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8154270916634005524834149 1528925796868876035906403)
              ·
                refine ⟨2293388695303314053859605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528925796868876035906403 2293388695303314053859605)
                ·
                  refine ⟨107502595092342846274669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293388695303314053859605 107502595092342846274669)
                  ·
                    rfl

theorem cell23_1884245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_1884245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884245 prefixEnd_1884245 := by exact prefixLift 1884245
  have htrace : WordTrace (prefixWord ++ tailWord_1884245) baseStart_1884245 baseEnd_1884245 := by
    simpa [prefixWord, tailWord_1884245, baseEnd_1884245] using wordTrace_append hprefix tailTrace_1884245
  have hstable : (prefixWord ++ tailWord_1884245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884245).length < 2 ^ (prefixWord ++ tailWord_1884245).sum := by decide
  have hdescent : baseEnd_1884245 < baseStart_1884245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884310 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1884310 : Nat := 118140960795 + 1884310 * 2 ^ 59
def prefixEnd_1884310 : Nat := 4983230072969 + 3 ^ 40 * 1884310 * 2
def baseEnd_1884310 : Nat := 967556732073627862159223

theorem tailTrace_1884310 : CollatzResearch.WordTrace tailWord_1884310 prefixEnd_1884310 967556732073627862159223 := by
  unfold tailWord_1884310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295401987717134960759149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45817621202316106248097589 4295401987717134960759149)
  ·
    refine ⟨1610775745393925610284681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4295401987717134960759149 1610775745393925610284681)
    ·
      refine ⟨1208081809045444207713511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1610775745393925610284681 1208081809045444207713511)
      ·
        refine ⟨1812122713568166311570267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208081809045444207713511 1812122713568166311570267)
        ·
          refine ⟨2718184070352249467355401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812122713568166311570267 2718184070352249467355401)
          ·
            refine ⟨2038638052764187100516551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2718184070352249467355401 2038638052764187100516551)
            ·
              refine ⟨3057957079146280650774827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038638052764187100516551 3057957079146280650774827)
              ·
                refine ⟨4586935618719420976162241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057957079146280650774827 4586935618719420976162241)
                ·
                  refine ⟨3440201714039565732121681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586935618719420976162241 3440201714039565732121681)
                  ·
                    refine ⟨2580151285529674299091261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440201714039565732121681 2580151285529674299091261)
                    ·
                      refine ⟨967556732073627862159223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580151285529674299091261 967556732073627862159223)
                      ·
                        rfl

theorem cell23_1884310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1884310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884310 prefixEnd_1884310 := by exact prefixLift 1884310
  have htrace : WordTrace (prefixWord ++ tailWord_1884310) baseStart_1884310 baseEnd_1884310 := by
    simpa [prefixWord, tailWord_1884310, baseEnd_1884310] using wordTrace_append hprefix tailTrace_1884310
  have hstable : (prefixWord ++ tailWord_1884310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884310).length < 2 ^ (prefixWord ++ tailWord_1884310).sum := by decide
  have hdescent : baseEnd_1884310 < baseStart_1884310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884378 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1884378 : Nat := 118140960795 + 1884378 * 2 ^ 59
def prefixEnd_1884378 : Nat := 4983230072969 + 3 ^ 40 * 1884378 * 2
def baseEnd_1884378 : Nat := 322530549586044532036303

theorem tailTrace_1884378 : CollatzResearch.WordTrace tailWord_1884378 prefixEnd_1884378 322530549586044532036303 := by
  unfold tailWord_1884378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182227991806951746405447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45819274644818537990414525 17182227991806951746405447)
  ·
    refine ⟨25773341987710427619608171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182227991806951746405447 25773341987710427619608171)
    ·
      refine ⟨38660012981565641429412257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25773341987710427619608171 38660012981565641429412257)
      ·
        refine ⟨28995009736174231072059193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38660012981565641429412257 28995009736174231072059193)
        ·
          refine ⟨21746257302130673304044395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28995009736174231072059193 21746257302130673304044395)
          ·
            refine ⟨32619385953196009956066593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21746257302130673304044395 32619385953196009956066593)
            ·
              refine ⟨24464539464897007467049945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32619385953196009956066593 24464539464897007467049945)
              ·
                refine ⟨18348404598672755600287459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24464539464897007467049945 18348404598672755600287459)
                ·
                  refine ⟨27522606898009133400431189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18348404598672755600287459 27522606898009133400431189)
                  ·
                    refine ⟨322530549586044532036303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27522606898009133400431189 322530549586044532036303)
                    ·
                      rfl

theorem cell23_1884378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1884378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884378 prefixEnd_1884378 := by exact prefixLift 1884378
  have htrace : WordTrace (prefixWord ++ tailWord_1884378) baseStart_1884378 baseEnd_1884378 := by
    simpa [prefixWord, tailWord_1884378, baseEnd_1884378] using wordTrace_append hprefix tailTrace_1884378
  have hstable : (prefixWord ++ tailWord_1884378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884378).length < 2 ^ (prefixWord ++ tailWord_1884378).sum := by decide
  have hdescent : baseEnd_1884378 < baseStart_1884378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884386 : List Nat := [3, 3, 4, 1, 2, 1, 9]
def baseStart_1884386 : Nat := 118140960795 + 1884386 * 2 ^ 59
def prefixEnd_1884386 : Nat := 4983230072969 + 3 ^ 40 * 1884386 * 2
def baseEnd_1884386 : Nat := 11945626624732957590233

theorem tailTrace_1884386 : CollatzResearch.WordTrace tailWord_1884386 prefixEnd_1884386 11945626624732957590233 := by
  unfold tailWord_1884386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182300937799706087978253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45819469167465882901275341 17182300937799706087978253)
  ·
    refine ⟨6443362851674889782991845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17182300937799706087978253 6443362851674889782991845)
    ·
      refine ⟨1208130534689041834310971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6443362851674889782991845 1208130534689041834310971)
      ·
        refine ⟨1812195802033562751466457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208130534689041834310971 1812195802033562751466457)
        ·
          refine ⟨1359146851525172063599843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812195802033562751466457 1359146851525172063599843)
          ·
            refine ⟨2038720277287758095399765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359146851525172063599843 2038720277287758095399765)
            ·
              refine ⟨11945626624732957590233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2038720277287758095399765 11945626624732957590233)
              ·
                rfl

theorem cell23_1884386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 9].length) (baseStart_1884386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884386 prefixEnd_1884386 := by exact prefixLift 1884386
  have htrace : WordTrace (prefixWord ++ tailWord_1884386) baseStart_1884386 baseEnd_1884386 := by
    simpa [prefixWord, tailWord_1884386, baseEnd_1884386] using wordTrace_append hprefix tailTrace_1884386
  have hstable : (prefixWord ++ tailWord_1884386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884386).length < 2 ^ (prefixWord ++ tailWord_1884386).sum := by decide
  have hdescent : baseEnd_1884386 < baseStart_1884386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884389 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1884389 : Nat := 118140960795 + 1884389 * 2 ^ 59
def prefixEnd_1884389 : Nat := 4983230072969 + 3 ^ 40 * 1884389 * 2
def baseEnd_1884389 : Nat := 967597297045333053071359

theorem tailTrace_1884389 : CollatzResearch.WordTrace tailWord_1884389 prefixEnd_1884389 967597297045333053071359 := by
  unfold tailWord_1884389
  simp only [CollatzResearch.WordTrace]
  refine ⟨68729313170187955864272221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45819542113458637242848147 68729313170187955864272221)
  ·
    refine ⟨25773492438820483449102083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68729313170187955864272221 25773492438820483449102083)
    ·
      refine ⟨38660238658230725173653125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25773492438820483449102083 38660238658230725173653125)
      ·
        refine ⟨7248794748418260970059961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38660238658230725173653125 7248794748418260970059961)
        ·
          refine ⟨5436596061313695727544971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248794748418260970059961 5436596061313695727544971)
          ·
            refine ⟨8154894091970543591317457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436596061313695727544971 8154894091970543591317457)
            ·
              refine ⟨6116170568977907693488093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8154894091970543591317457 6116170568977907693488093)
              ·
                refine ⟨2293563963366715385058035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6116170568977907693488093 2293563963366715385058035)
                ·
                  refine ⟨3440345945050073077587053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293563963366715385058035 3440345945050073077587053)
                  ·
                    refine ⟨1290129729393777404095145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440345945050073077587053 1290129729393777404095145)
                    ·
                      refine ⟨967597297045333053071359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290129729393777404095145 967597297045333053071359)
                      ·
                        rfl

theorem cell23_1884389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1884389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884389 prefixEnd_1884389 := by exact prefixLift 1884389
  have htrace : WordTrace (prefixWord ++ tailWord_1884389) baseStart_1884389 baseEnd_1884389 := by
    simpa [prefixWord, tailWord_1884389, baseEnd_1884389] using wordTrace_append hprefix tailTrace_1884389
  have hstable : (prefixWord ++ tailWord_1884389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884389).length < 2 ^ (prefixWord ++ tailWord_1884389).sum := by decide
  have hdescent : baseEnd_1884389 < baseStart_1884389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884419 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 2, 2, 2]
def baseStart_1884419 : Nat := 118140960795 + 1884419 * 2 ^ 59
def prefixEnd_1884419 : Nat := 4983230072969 + 3 ^ 40 * 1884419 * 2
def baseEnd_1884419 : Nat := 967612701464967935696221

theorem tailTrace_1884419 : CollatzResearch.WordTrace tailWord_1884419 prefixEnd_1884419 967612701464967935696221 := by
  unfold tailWord_1884419
  simp only [CollatzResearch.WordTrace]
  refine ⟨68730407360079270987864311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45820271573386180658576207 68730407360079270987864311)
  ·
    refine ⟨103095611040118906481796467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68730407360079270987864311 103095611040118906481796467)
    ·
      refine ⟨154643416560178359722694701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103095611040118906481796467 154643416560178359722694701)
      ·
        refine ⟨57991281210066884896010513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154643416560178359722694701 57991281210066884896010513)
        ·
          refine ⟨43493460907550163672007885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57991281210066884896010513 43493460907550163672007885)
          ·
            refine ⟨16310047840331311377002957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43493460907550163672007885 16310047840331311377002957)
            ·
              refine ⟨6116267940124241766376109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16310047840331311377002957 6116267940124241766376109)
              ·
                refine ⟨2293600477546590662391041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6116267940124241766376109 2293600477546590662391041)
                ·
                  refine ⟨1720200358159942996793281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2293600477546590662391041 1720200358159942996793281)
                  ·
                    refine ⟨1290150268619957247594961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1720200358159942996793281 1290150268619957247594961)
                    ·
                      refine ⟨967612701464967935696221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290150268619957247594961 967612701464967935696221)
                      ·
                        rfl

theorem cell23_1884419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_1884419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884419 prefixEnd_1884419 := by exact prefixLift 1884419
  have htrace : WordTrace (prefixWord ++ tailWord_1884419) baseStart_1884419 baseEnd_1884419 := by
    simpa [prefixWord, tailWord_1884419, baseEnd_1884419] using wordTrace_append hprefix tailTrace_1884419
  have hstable : (prefixWord ++ tailWord_1884419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884419).length < 2 ^ (prefixWord ++ tailWord_1884419).sum := by decide
  have hdescent : baseEnd_1884419 < baseStart_1884419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884423 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1884423 : Nat := 118140960795 + 1884423 * 2 ^ 59
def prefixEnd_1884423 : Nat := 4983230072969 + 3 ^ 40 * 1884423 * 2
def baseEnd_1884423 : Nat := 967614755387585920046203

theorem tailTrace_1884423 : CollatzResearch.WordTrace tailWord_1884423 prefixEnd_1884423 967614755387585920046203 := by
  unfold tailWord_1884423
  simp only [CollatzResearch.WordTrace]
  refine ⟨68730553252064779671009923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45820368834709853114006615 68730553252064779671009923)
  ·
    refine ⟨103095829878097169506514885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68730553252064779671009923 103095829878097169506514885)
    ·
      refine ⟨19330468102143219282471541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103095829878097169506514885 19330468102143219282471541)
      ·
        refine ⟨1812231384575926807731707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19330468102143219282471541 1812231384575926807731707)
        ·
          refine ⟨2718347076863890211597561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812231384575926807731707 2718347076863890211597561)
          ·
            refine ⟨2038760307647917658698171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2718347076863890211597561 2038760307647917658698171)
            ·
              refine ⟨3058140461471876488047257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038760307647917658698171 3058140461471876488047257)
              ·
                refine ⟨2293605346103907366035443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058140461471876488047257 2293605346103907366035443)
                ·
                  refine ⟨3440408019155861049053165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293605346103907366035443 3440408019155861049053165)
                  ·
                    refine ⟨1290153007183447893394937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440408019155861049053165 1290153007183447893394937)
                    ·
                      refine ⟨967614755387585920046203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290153007183447893394937 967614755387585920046203)
                      ·
                        rfl

theorem cell23_1884423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1884423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884423 prefixEnd_1884423 := by exact prefixLift 1884423
  have htrace : WordTrace (prefixWord ++ tailWord_1884423) baseStart_1884423 baseEnd_1884423 := by
    simpa [prefixWord, tailWord_1884423, baseEnd_1884423] using wordTrace_append hprefix tailTrace_1884423
  have hstable : (prefixWord ++ tailWord_1884423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884423).length < 2 ^ (prefixWord ++ tailWord_1884423).sum := by decide
  have hdescent : baseEnd_1884423 < baseStart_1884423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884492 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_1884492 : Nat := 118140960795 + 1884492 * 2 ^ 59
def prefixEnd_1884492 : Nat := 4983230072969 + 3 ^ 40 * 1884492 * 2
def baseEnd_1884492 : Nat := 967650185552746150083385

theorem tailTrace_1884492 : CollatzResearch.WordTrace tailWord_1884492 prefixEnd_1884492 967650185552746150083385 := by
  unfold tailWord_1884492
  simp only [CollatzResearch.WordTrace]
  refine ⟨34366534944407402227635865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45822046592543202970181153 34366534944407402227635865)
  ·
    refine ⟨25774901208305551670726899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34366534944407402227635865 25774901208305551670726899)
    ·
      refine ⟨38662351812458327506090349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774901208305551670726899 38662351812458327506090349)
      ·
        refine ⟨14498381929671872814783881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38662351812458327506090349 14498381929671872814783881)
        ·
          refine ⟨10873786447253904611087911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498381929671872814783881 10873786447253904611087911)
          ·
            refine ⟨16310679670880856916631867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873786447253904611087911 16310679670880856916631867)
            ·
              refine ⟨24466019506321285374947801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16310679670880856916631867 24466019506321285374947801)
              ·
                refine ⟨18349514629740964031210851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24466019506321285374947801 18349514629740964031210851)
                ·
                  refine ⟨27524271944611446046816277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18349514629740964031210851 27524271944611446046816277)
                  ·
                    refine ⟨1290200247403661533444513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27524271944611446046816277 1290200247403661533444513)
                    ·
                      refine ⟨967650185552746150083385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290200247403661533444513 967650185552746150083385)
                      ·
                        rfl

theorem cell23_1884492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_1884492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884492 prefixEnd_1884492 := by exact prefixLift 1884492
  have htrace : WordTrace (prefixWord ++ tailWord_1884492) baseStart_1884492 baseEnd_1884492 := by
    simpa [prefixWord, tailWord_1884492, baseEnd_1884492] using wordTrace_append hprefix tailTrace_1884492
  have hstable : (prefixWord ++ tailWord_1884492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884492).length < 2 ^ (prefixWord ++ tailWord_1884492).sum := by decide
  have hdescent : baseEnd_1884492 < baseStart_1884492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884515 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 8]
def baseStart_1884515 : Nat := 118140960795 + 1884515 * 2 ^ 59
def prefixEnd_1884515 : Nat := 4983230072969 + 3 ^ 40 * 1884515 * 2
def baseEnd_1884515 : Nat := 107517999511977728899531

theorem tailTrace_1884515 : CollatzResearch.WordTrace tailWord_1884515 prefixEnd_1884515 107517999511977728899531 := by
  unfold tailWord_1884515
  simp only [CollatzResearch.WordTrace]
  refine ⟨68733908767731479383358999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45822605845154319588905999 68733908767731479383358999)
  ·
    refine ⟨103100863151597219075038499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68733908767731479383358999 103100863151597219075038499)
    ·
      refine ⟨154651294727395828612557749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103100863151597219075038499 154651294727395828612557749)
      ·
        refine ⟨14498558880693358932427289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154651294727395828612557749 14498558880693358932427289)
        ·
          refine ⟨10873919160520019199320467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498558880693358932427289 10873919160520019199320467)
          ·
            refine ⟨16310878740780028798980701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873919160520019199320467 16310878740780028798980701)
            ·
              refine ⟨6116579527792510799617763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16310878740780028798980701 6116579527792510799617763)
              ·
                refine ⟨9174869291688766199426645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6116579527792510799617763 9174869291688766199426645)
                ·
                  refine ⟨107517999511977728899531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9174869291688766199426645 107517999511977728899531)
                  ·
                    rfl

theorem cell23_1884515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 8].length) (baseStart_1884515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884515 prefixEnd_1884515 := by exact prefixLift 1884515
  have htrace : WordTrace (prefixWord ++ tailWord_1884515) baseStart_1884515 baseEnd_1884515 := by
    simpa [prefixWord, tailWord_1884515, baseEnd_1884515] using wordTrace_append hprefix tailTrace_1884515
  have hstable : (prefixWord ++ tailWord_1884515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884515).length < 2 ^ (prefixWord ++ tailWord_1884515).sum := by decide
  have hdescent : baseEnd_1884515 < baseStart_1884515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884519 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1884519 : Nat := 118140960795 + 1884519 * 2 ^ 59
def prefixEnd_1884519 : Nat := 4983230072969 + 3 ^ 40 * 1884519 * 2
def baseEnd_1884519 : Nat := 322554683176805848148587

theorem tailTrace_1884519 : CollatzResearch.WordTrace tailWord_1884519 prefixEnd_1884519 322554683176805848148587 := by
  unfold tailWord_1884519
  simp only [CollatzResearch.WordTrace]
  refine ⟨68734054659716988066504611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45822703106477992044336407 68734054659716988066504611)
  ·
    refine ⟨103101081989575482099756917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68734054659716988066504611 103101081989575482099756917)
    ·
      refine ⟨9665726436522701446852211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103101081989575482099756917 9665726436522701446852211)
      ·
        refine ⟨14498589654784052170278317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665726436522701446852211 14498589654784052170278317)
        ·
          refine ⟨5436971120544019563854369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14498589654784052170278317 5436971120544019563854369)
          ·
            refine ⟨4077728340408014672890777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436971120544019563854369 4077728340408014672890777)
            ·
              refine ⟨3058296255306011004668083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077728340408014672890777 3058296255306011004668083)
              ·
                refine ⟨4587444382959016507002125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058296255306011004668083 4587444382959016507002125)
                ·
                  refine ⟨1720291643609631190125797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4587444382959016507002125 1720291643609631190125797)
                  ·
                    refine ⟨322554683176805848148587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1720291643609631190125797 322554683176805848148587)
                    ·
                      rfl

theorem cell23_1884519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1884519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884519 prefixEnd_1884519 := by exact prefixLift 1884519
  have htrace : WordTrace (prefixWord ++ tailWord_1884519) baseStart_1884519 baseEnd_1884519 := by
    simpa [prefixWord, tailWord_1884519, baseEnd_1884519] using wordTrace_append hprefix tailTrace_1884519
  have hstable : (prefixWord ++ tailWord_1884519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884519).length < 2 ^ (prefixWord ++ tailWord_1884519).sum := by decide
  have hdescent : baseEnd_1884519 < baseStart_1884519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884569 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 2, 3, 2]
def baseStart_1884569 : Nat := 118140960795 + 1884569 * 2 ^ 59
def prefixEnd_1884569 : Nat := 4983230072969 + 3 ^ 40 * 1884569 * 2
def baseEnd_1884569 : Nat := 967689723563142348820531

theorem tailTrace_1884569 : CollatzResearch.WordTrace tailWord_1884569 prefixEnd_1884569 967689723563142348820531 := by
  unfold tailWord_1884569
  simp only [CollatzResearch.WordTrace]
  refine ⟨68735878309535846605824761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45823918873023897737216507 68735878309535846605824761)
  ·
    refine ⟨51551908732151884954368571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68735878309535846605824761 51551908732151884954368571)
    ·
      refine ⟨77327863098227827431552857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51551908732151884954368571 77327863098227827431552857)
      ·
        refine ⟨57995897323670870573664643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77327863098227827431552857 57995897323670870573664643)
        ·
          refine ⟨86993845985506305860496965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57995897323670870573664643 86993845985506305860496965)
          ·
            refine ⟨16311346122282432348843181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86993845985506305860496965 16311346122282432348843181)
            ·
              refine ⟨6116754795855912130816193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16311346122282432348843181 6116754795855912130816193)
              ·
                refine ⟨4587566096891934098112145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116754795855912130816193 4587566096891934098112145)
                ·
                  refine ⟨3440674572668950573584109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4587566096891934098112145 3440674572668950573584109)
                  ·
                    refine ⟨1290252964750856465094041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440674572668950573584109 1290252964750856465094041)
                    ·
                      refine ⟨967689723563142348820531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290252964750856465094041 967689723563142348820531)
                      ·
                        rfl

theorem cell23_1884569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_1884569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884569 prefixEnd_1884569 := by exact prefixLift 1884569
  have htrace : WordTrace (prefixWord ++ tailWord_1884569) baseStart_1884569 baseEnd_1884569 := by
    simpa [prefixWord, tailWord_1884569, baseEnd_1884569] using wordTrace_append hprefix tailTrace_1884569
  have hstable : (prefixWord ++ tailWord_1884569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884569).length < 2 ^ (prefixWord ++ tailWord_1884569).sum := by decide
  have hdescent : baseEnd_1884569 < baseStart_1884569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884576 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1884576 : Nat := 118140960795 + 1884576 * 2 ^ 59
def prefixEnd_1884576 : Nat := 4983230072969 + 3 ^ 40 * 1884576 * 2
def baseEnd_1884576 : Nat := 967693317927723821432999

theorem tailTrace_1884576 : CollatzResearch.WordTrace tailWord_1884576 prefixEnd_1884576 967693317927723821432999 := by
  unfold tailWord_1884576
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368066810255243400664791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45824089080340324534219721 34368066810255243400664791)
  ·
    refine ⟨51552100215382865100997187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34368066810255243400664791 51552100215382865100997187)
    ·
      refine ⟨77328150323074297651495781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51552100215382865100997187 77328150323074297651495781)
      ·
        refine ⟨14499028185576430809655459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77328150323074297651495781 14499028185576430809655459)
        ·
          refine ⟨21748542278364646214483189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14499028185576430809655459 21748542278364646214483189)
          ·
            refine ⟨2038925838596685582607799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21748542278364646214483189 2038925838596685582607799)
            ·
              refine ⟨3058388757895028373911699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038925838596685582607799 3058388757895028373911699)
              ·
                refine ⟨4587583136842542560867549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058388757895028373911699 4587583136842542560867549)
                ·
                  refine ⟨1720343676315953460325331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4587583136842542560867549 1720343676315953460325331)
                  ·
                    refine ⟨2580515514473930190487997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1720343676315953460325331 2580515514473930190487997)
                    ·
                      refine ⟨967693317927723821432999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580515514473930190487997 967693317927723821432999)
                      ·
                        rfl

theorem cell23_1884576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1884576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884576 prefixEnd_1884576 := by exact prefixLift 1884576
  have htrace : WordTrace (prefixWord ++ tailWord_1884576) baseStart_1884576 baseEnd_1884576 := by
    simpa [prefixWord, tailWord_1884576, baseEnd_1884576] using wordTrace_append hprefix tailTrace_1884576
  have hstable : (prefixWord ++ tailWord_1884576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884576).length < 2 ^ (prefixWord ++ tailWord_1884576).sum := by decide
  have hdescent : baseEnd_1884576 < baseStart_1884576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884599 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_1884599 : Nat := 118140960795 + 1884599 * 2 ^ 59
def prefixEnd_1884599 : Nat := 4983230072969 + 3 ^ 40 * 1884599 * 2
def baseEnd_1884599 : Nat := 967705127982777231445393

theorem tailTrace_1884599 : CollatzResearch.WordTrace tailWord_1884599 prefixEnd_1884599 967705127982777231445393 := by
  unfold tailWord_1884599
  simp only [CollatzResearch.WordTrace]
  refine ⟨68736972499427161729416851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45824648332951441152944567 68736972499427161729416851)
  ·
    refine ⟨103105458749140742594125277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68736972499427161729416851 103105458749140742594125277)
    ·
      refine ⟨38664547030927778472796979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103105458749140742594125277 38664547030927778472796979)
      ·
        refine ⟨57996820546391667709195469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38664547030927778472796979 57996820546391667709195469)
        ·
          refine ⟨21748807704896875390948301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57996820546391667709195469 21748807704896875390948301)
          ·
            refine ⟨8155802889336328271605613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21748807704896875390948301 8155802889336328271605613)
            ·
              refine ⟨3058426083501123101852105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8155802889336328271605613 3058426083501123101852105)
              ·
                refine ⟨2293819562625842326389079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058426083501123101852105 2293819562625842326389079)
                ·
                  refine ⟨3440729343938763489583619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293819562625842326389079 3440729343938763489583619)
                  ·
                    refine ⟨5161094015908145234375429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440729343938763489583619 5161094015908145234375429)
                    ·
                      refine ⟨967705127982777231445393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5161094015908145234375429 967705127982777231445393)
                      ·
                        rfl

theorem cell23_1884599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_1884599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884599 prefixEnd_1884599 := by exact prefixLift 1884599
  have htrace : WordTrace (prefixWord ++ tailWord_1884599) baseStart_1884599 baseEnd_1884599 := by
    simpa [prefixWord, tailWord_1884599, baseEnd_1884599] using wordTrace_append hprefix tailTrace_1884599
  have hstable : (prefixWord ++ tailWord_1884599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884599).length < 2 ^ (prefixWord ++ tailWord_1884599).sum := by decide
  have hdescent : baseEnd_1884599 < baseStart_1884599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884616 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_1884616 : Nat := 118140960795 + 1884616 * 2 ^ 59
def prefixEnd_1884616 : Nat := 4983230072969 + 3 ^ 40 * 1884616 * 2
def baseEnd_1884616 : Nat := 967713857153903664932815

theorem tailTrace_1884616 : CollatzResearch.WordTrace tailWord_1884616 prefixEnd_1884616 967713857153903664932815 := by
  unfold tailWord_1884616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368796270182786816392851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45825061693577049088523801 34368796270182786816392851)
  ·
    refine ⟨51553194405274180224589277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34368796270182786816392851 51553194405274180224589277)
    ·
      refine ⟨19332447901977817584220979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51553194405274180224589277 19332447901977817584220979)
      ·
        refine ⟨28998671852966726376331469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19332447901977817584220979 28998671852966726376331469)
        ·
          refine ⟨10874501944862522391124301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28998671852966726376331469 10874501944862522391124301)
          ·
            refine ⟨4077938229323445896671613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10874501944862522391124301 4077938229323445896671613)
            ·
              refine ⟨1529226835996292211251855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4077938229323445896671613 1529226835996292211251855)
              ·
                refine ⟨2293840253994438316877783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529226835996292211251855 2293840253994438316877783)
                ·
                  refine ⟨3440760380991657475316675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293840253994438316877783 3440760380991657475316675)
                  ·
                    refine ⟨5161140571487486212975013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440760380991657475316675 5161140571487486212975013)
                    ·
                      refine ⟨967713857153903664932815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5161140571487486212975013 967713857153903664932815)
                      ·
                        rfl

theorem cell23_1884616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_1884616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884616 prefixEnd_1884616 := by exact prefixLift 1884616
  have htrace : WordTrace (prefixWord ++ tailWord_1884616) baseStart_1884616 baseEnd_1884616 := by
    simpa [prefixWord, tailWord_1884616, baseEnd_1884616] using wordTrace_append hprefix tailTrace_1884616
  have hstable : (prefixWord ++ tailWord_1884616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884616).length < 2 ^ (prefixWord ++ tailWord_1884616).sum := by decide
  have hdescent : baseEnd_1884616 < baseStart_1884616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884632 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1884632 : Nat := 118140960795 + 1884632 * 2 ^ 59
def prefixEnd_1884632 : Nat := 4983230072969 + 3 ^ 40 * 1884632 * 2
def baseEnd_1884632 : Nat := 967722072844375602332741

theorem tailTrace_1884632 : CollatzResearch.WordTrace tailWord_1884632 prefixEnd_1884632 967722072844375602332741 := by
  unfold tailWord_1884632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34369088054153804182684075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45825450738871738910245433 34369088054153804182684075)
  ·
    refine ⟨51553632081230706274026113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34369088054153804182684075 51553632081230706274026113)
    ·
      refine ⟨38665224060923029705519585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51553632081230706274026113 38665224060923029705519585)
      ·
        refine ⟨28998918045692272279139689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38665224060923029705519585 28998918045692272279139689)
        ·
          refine ⟨21749188534269204209354767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28998918045692272279139689 21749188534269204209354767)
          ·
            refine ⟨32623782801403806314032151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21749188534269204209354767 32623782801403806314032151)
            ·
              refine ⟨48935674202105709471048227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32623782801403806314032151 48935674202105709471048227)
              ·
                refine ⟨73403511303158564206572341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48935674202105709471048227 73403511303158564206572341)
                ·
                  refine ⟨6881579184671115394366157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73403511303158564206572341 6881579184671115394366157)
                  ·
                    refine ⟨2580592194251668272887309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6881579184671115394366157 2580592194251668272887309)
                    ·
                      refine ⟨967722072844375602332741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580592194251668272887309 967722072844375602332741)
                      ·
                        rfl

theorem cell23_1884632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1884632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884632 prefixEnd_1884632 := by exact prefixLift 1884632
  have htrace : WordTrace (prefixWord ++ tailWord_1884632) baseStart_1884632 baseEnd_1884632 := by
    simpa [prefixWord, tailWord_1884632, baseEnd_1884632] using wordTrace_append hprefix tailTrace_1884632
  have hstable : (prefixWord ++ tailWord_1884632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884632).length < 2 ^ (prefixWord ++ tailWord_1884632).sum := by decide
  have hdescent : baseEnd_1884632 < baseStart_1884632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884633 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 1, 2, 2]
def baseStart_1884633 : Nat := 118140960795 + 1884633 * 2 ^ 59
def prefixEnd_1884633 : Nat := 4983230072969 + 3 ^ 40 * 1884633 * 2
def baseEnd_1884633 : Nat := 967722586325030098420237

theorem tailTrace_1884633 : CollatzResearch.WordTrace tailWord_1884633 prefixEnd_1884633 967722586325030098420237 := by
  unfold tailWord_1884633
  simp only [CollatzResearch.WordTrace]
  refine ⟨68738212581303985536154553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45825475054202657024103035 68738212581303985536154553)
  ·
    refine ⟨51553659435977989152115915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68738212581303985536154553 51553659435977989152115915)
    ·
      refine ⟨77330489153966983728173873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51553659435977989152115915 77330489153966983728173873)
      ·
        refine ⟨57997866865475237796130405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77330489153966983728173873 57997866865475237796130405)
        ·
          refine ⟨10874600037276607086774451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57997866865475237796130405 10874600037276607086774451)
          ·
            refine ⟨16311900055914910630161677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874600037276607086774451 16311900055914910630161677)
            ·
              refine ⟨6116962520968091486310629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16311900055914910630161677 6116962520968091486310629)
              ·
                refine ⟨1146930472681517153683243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6116962520968091486310629 1146930472681517153683243)
                ·
                  refine ⟨1720395709022275730524865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146930472681517153683243 1720395709022275730524865)
                  ·
                    refine ⟨1290296781766706797893649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1720395709022275730524865 1290296781766706797893649)
                    ·
                      refine ⟨967722586325030098420237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290296781766706797893649 967722586325030098420237)
                      ·
                        rfl

theorem cell23_1884633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_1884633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884633 prefixEnd_1884633 := by exact prefixLift 1884633
  have htrace : WordTrace (prefixWord ++ tailWord_1884633) baseStart_1884633 baseEnd_1884633 := by
    simpa [prefixWord, tailWord_1884633, baseEnd_1884633] using wordTrace_append hprefix tailTrace_1884633
  have hstable : (prefixWord ++ tailWord_1884633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884633).length < 2 ^ (prefixWord ++ tailWord_1884633).sum := by decide
  have hdescent : baseEnd_1884633 < baseStart_1884633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884659 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 2]
def baseStart_1884659 : Nat := 118140960795 + 1884659 * 2 ^ 59
def prefixEnd_1884659 : Nat := 4983230072969 + 3 ^ 40 * 1884659 * 2
def baseEnd_1884659 : Nat := 967735936822046996695117

theorem tailTrace_1884659 : CollatzResearch.WordTrace tailWord_1884659 prefixEnd_1884659 967735936822046996695117 := by
  unfold tailWord_1884659
  simp only [CollatzResearch.WordTrace]
  refine ⟨68739160879209791976601031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45826107252806527984400687 68739160879209791976601031)
  ·
    refine ⟨103108741318814687964901547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68739160879209791976601031 103108741318814687964901547)
    ·
      refine ⟨154663111978222031947352321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103108741318814687964901547 154663111978222031947352321)
      ·
        refine ⟨115997333983666523960514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154663111978222031947352321 115997333983666523960514241)
        ·
          refine ⟨86998000487749892970385681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115997333983666523960514241 86998000487749892970385681)
          ·
            refine ⟨65248500365812419727789261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86998000487749892970385681 65248500365812419727789261)
            ·
              refine ⟨24468187637179657397920973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65248500365812419727789261 24468187637179657397920973)
              ·
                refine ⟨9175570363942371524220365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24468187637179657397920973 9175570363942371524220365)
                ·
                  refine ⟨3440838886478389321582637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9175570363942371524220365 3440838886478389321582637)
                  ·
                    refine ⟨1290314582429395995593489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440838886478389321582637 1290314582429395995593489)
                    ·
                      refine ⟨967735936822046996695117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290314582429395995593489 967735936822046996695117)
                      ·
                        rfl

theorem cell23_1884659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 2].length) (baseStart_1884659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884659 prefixEnd_1884659 := by exact prefixLift 1884659
  have htrace : WordTrace (prefixWord ++ tailWord_1884659) baseStart_1884659 baseEnd_1884659 := by
    simpa [prefixWord, tailWord_1884659, baseEnd_1884659] using wordTrace_append hprefix tailTrace_1884659
  have hstable : (prefixWord ++ tailWord_1884659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884659).length < 2 ^ (prefixWord ++ tailWord_1884659).sum := by decide
  have hdescent : baseEnd_1884659 < baseStart_1884659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884682 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1884682 : Nat := 118140960795 + 1884682 * 2 ^ 59
def prefixEnd_1884682 : Nat := 4983230072969 + 3 ^ 40 * 1884682 * 2
def baseEnd_1884682 : Nat := 322582582292366802235837

theorem tailTrace_1884682 : CollatzResearch.WordTrace tailWord_1884682 prefixEnd_1884682 322582582292366802235837 := by
  unfold tailWord_1884682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184999939531616726172075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45826666505417644603125533 17184999939531616726172075)
  ·
    refine ⟨25777499909297425089258113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17184999939531616726172075 25777499909297425089258113)
    ·
      refine ⟨19333124931973068816943585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25777499909297425089258113 19333124931973068816943585)
      ·
        refine ⟨14499843698979801612707689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19333124931973068816943585 14499843698979801612707689)
        ·
          refine ⟨10874882774234851209530767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14499843698979801612707689 10874882774234851209530767)
          ·
            refine ⟨16312324161352276814296151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874882774234851209530767 16312324161352276814296151)
            ·
              refine ⟨24468486242028415221444227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16312324161352276814296151 24468486242028415221444227)
              ·
                refine ⟨36702729363042622832166341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24468486242028415221444227 36702729363042622832166341)
                ·
                  refine ⟨6881761755570491781031189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36702729363042622832166341 6881761755570491781031189)
                  ·
                    refine ⟨322582582292366802235837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6881761755570491781031189 322582582292366802235837)
                    ·
                      rfl

theorem cell23_1884682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1884682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884682 prefixEnd_1884682 := by exact prefixLift 1884682
  have htrace : WordTrace (prefixWord ++ tailWord_1884682) baseStart_1884682 baseEnd_1884682 := by
    simpa [prefixWord, tailWord_1884682, baseEnd_1884682] using wordTrace_append hprefix tailTrace_1884682
  have hstable : (prefixWord ++ tailWord_1884682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884682).length < 2 ^ (prefixWord ++ tailWord_1884682).sum := by decide
  have hdescent : baseEnd_1884682 < baseStart_1884682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884683 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 3]
def baseStart_1884683 : Nat := 118140960795 + 1884683 * 2 ^ 59
def prefixEnd_1884683 : Nat := 4983230072969 + 3 ^ 40 * 1884683 * 2
def baseEnd_1884683 : Nat := 967748260357754902795007

theorem tailTrace_1884683 : CollatzResearch.WordTrace tailWord_1884683 prefixEnd_1884683 967748260357754902795007 := by
  unfold tailWord_1884683
  simp only [CollatzResearch.WordTrace]
  refine ⟨68740036231122844075474703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45826690820748562716983135 68740036231122844075474703)
  ·
    refine ⟨103110054346684266113212055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68740036231122844075474703 103110054346684266113212055)
    ·
      refine ⟨154665081520026399169818083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103110054346684266113212055 154665081520026399169818083)
      ·
        refine ⟨231997622280039598754727125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154665081520026399169818083 231997622280039598754727125)
        ·
          refine ⟨5437444272188428095813917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 231997622280039598754727125 5437444272188428095813917)
          ·
            refine ⟨2039041602070660535930219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5437444272188428095813917 2039041602070660535930219)
            ·
              refine ⟨3058562403105990803895329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039041602070660535930219 3058562403105990803895329)
              ·
                refine ⟨2293921802329493102921497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058562403105990803895329 2293921802329493102921497)
                ·
                  refine ⟨1720441351747119827191123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2293921802329493102921497 1720441351747119827191123)
                  ·
                    refine ⟨2580662027620679740786685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1720441351747119827191123 2580662027620679740786685)
                    ·
                      refine ⟨967748260357754902795007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580662027620679740786685 967748260357754902795007)
                      ·
                        rfl

theorem cell23_1884683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 3].length) (baseStart_1884683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884683 prefixEnd_1884683 := by exact prefixLift 1884683
  have htrace : WordTrace (prefixWord ++ tailWord_1884683) baseStart_1884683 baseEnd_1884683 := by
    simpa [prefixWord, tailWord_1884683, baseEnd_1884683] using wordTrace_append hprefix tailTrace_1884683
  have hstable : (prefixWord ++ tailWord_1884683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884683).length < 2 ^ (prefixWord ++ tailWord_1884683).sum := by decide
  have hdescent : baseEnd_1884683 < baseStart_1884683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884726 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1884726 : Nat := 118140960795 + 1884726 * 2 ^ 59
def prefixEnd_1884726 : Nat := 4983230072969 + 3 ^ 40 * 1884726 * 2
def baseEnd_1884726 : Nat := 967770340025898234557309

theorem tailTrace_1884726 : CollatzResearch.WordTrace tailWord_1884726 prefixEnd_1884726 967770340025898234557309 := by
  unfold tailWord_1884726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296350285622941401205627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45827736379978041612860021 4296350285622941401205627)
  ·
    refine ⟨6444525428434412101808441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296350285622941401205627 6444525428434412101808441)
    ·
      refine ⟨4833394071325809076356331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6444525428434412101808441 4833394071325809076356331)
      ·
        refine ⟨7250091106988713614534497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833394071325809076356331 7250091106988713614534497)
        ·
          refine ⟨5437568330241535210900873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250091106988713614534497 5437568330241535210900873)
          ·
            refine ⟨4078176247681151408175655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5437568330241535210900873 4078176247681151408175655)
            ·
              refine ⟨6117264371521727112263483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078176247681151408175655 6117264371521727112263483)
              ·
                refine ⟨9175896557282590668395225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117264371521727112263483 9175896557282590668395225)
                ·
                  refine ⟨6881922417961943001296419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175896557282590668395225 6881922417961943001296419)
                  ·
                    refine ⟨10322883626942914501944629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881922417961943001296419 10322883626942914501944629)
                    ·
                      refine ⟨967770340025898234557309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10322883626942914501944629 967770340025898234557309)
                      ·
                        rfl

theorem cell23_1884726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1884726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884726 prefixEnd_1884726 := by exact prefixLift 1884726
  have htrace : WordTrace (prefixWord ++ tailWord_1884726) baseStart_1884726 baseEnd_1884726 := by
    simpa [prefixWord, tailWord_1884726, baseEnd_1884726] using wordTrace_append hprefix tailTrace_1884726
  have hstable : (prefixWord ++ tailWord_1884726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884726).length < 2 ^ (prefixWord ++ tailWord_1884726).sum := by decide
  have hdescent : baseEnd_1884726 < baseStart_1884726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884779 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 6, 2]
def baseStart_1884779 : Nat := 118140960795 + 1884779 * 2 ^ 59
def prefixEnd_1884779 : Nat := 4983230072969 + 3 ^ 40 * 1884779 * 2
def baseEnd_1884779 : Nat := 967797554500586527194565

theorem tailTrace_1884779 : CollatzResearch.WordTrace tailWord_1884779 prefixEnd_1884779 967797554500586527194565 := by
  unfold tailWord_1884779
  simp only [CollatzResearch.WordTrace]
  refine ⟨68743537638775052470969391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45829025092516701647312927 68743537638775052470969391)
  ·
    refine ⟨103115306458162578706454087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68743537638775052470969391 103115306458162578706454087)
    ·
      refine ⟨154672959687243868059681131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103115306458162578706454087 154672959687243868059681131)
      ·
        refine ⟨232009439530865802089521697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154672959687243868059681131 232009439530865802089521697)
        ·
          refine ⟨174007079648149351567141273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232009439530865802089521697 174007079648149351567141273)
          ·
            refine ⟨130505309736112013675355955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174007079648149351567141273 130505309736112013675355955)
            ·
              refine ⟨195757964604168020513033933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130505309736112013675355955 195757964604168020513033933)
              ·
                refine ⟨73409236726563007692387725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195757964604168020513033933 73409236726563007692387725)
                ·
                  refine ⟨27528463772461127884645397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73409236726563007692387725 27528463772461127884645397)
                  ·
                    refine ⟨1290396739334115369592753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27528463772461127884645397 1290396739334115369592753)
                    ·
                      refine ⟨967797554500586527194565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290396739334115369592753 967797554500586527194565)
                      ·
                        rfl

theorem cell23_1884779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6, 2].length) (baseStart_1884779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884779 prefixEnd_1884779 := by exact prefixLift 1884779
  have htrace : WordTrace (prefixWord ++ tailWord_1884779) baseStart_1884779 baseEnd_1884779 := by
    simpa [prefixWord, tailWord_1884779, baseEnd_1884779] using wordTrace_append hprefix tailTrace_1884779
  have hstable : (prefixWord ++ tailWord_1884779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884779).length < 2 ^ (prefixWord ++ tailWord_1884779).sum := by decide
  have hdescent : baseEnd_1884779 < baseStart_1884779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884792 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1884792 : Nat := 118140960795 + 1884792 * 2 ^ 59
def prefixEnd_1884792 : Nat := 4983230072969 + 3 ^ 40 * 1884792 * 2
def baseEnd_1884792 : Nat := 967804229749094976332005

theorem tailTrace_1884792 : CollatzResearch.WordTrace tailWord_1884792 prefixEnd_1884792 967804229749094976332005 := by
  unfold tailWord_1884792
  simp only [CollatzResearch.WordTrace]
  refine ⟨34372005893863977845596315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45829341191818637127461753 34372005893863977845596315)
  ·
    refine ⟨51558008840795966768394473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34372005893863977845596315 51558008840795966768394473)
    ·
      refine ⟨38668506630596975076295855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51558008840795966768394473 38668506630596975076295855)
      ·
        refine ⟨58002759945895462614443783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38668506630596975076295855 58002759945895462614443783)
        ·
          refine ⟨87004139918843193921665675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58002759945895462614443783 87004139918843193921665675)
          ·
            refine ⟨130506209878264790882498513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87004139918843193921665675 130506209878264790882498513)
            ·
              refine ⟨97879657408698593161873885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130506209878264790882498513 97879657408698593161873885)
              ·
                refine ⟨36704871528261972435702707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97879657408698593161873885 36704871528261972435702707)
                ·
                  refine ⟨55057307292392958653554061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36704871528261972435702707 55057307292392958653554061)
                  ·
                    refine ⟨20646490234647359495082773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55057307292392958653554061 20646490234647359495082773)
                    ·
                      refine ⟨967804229749094976332005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20646490234647359495082773 967804229749094976332005)
                      ·
                        rfl

theorem cell23_1884792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1884792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884792 prefixEnd_1884792 := by exact prefixLift 1884792
  have htrace : WordTrace (prefixWord ++ tailWord_1884792) baseStart_1884792 baseEnd_1884792 := by
    simpa [prefixWord, tailWord_1884792, baseEnd_1884792] using wordTrace_append hprefix tailTrace_1884792
  have hstable : (prefixWord ++ tailWord_1884792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884792).length < 2 ^ (prefixWord ++ tailWord_1884792).sum := by decide
  have hdescent : baseEnd_1884792 < baseStart_1884792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884799 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_1884799 : Nat := 118140960795 + 1884799 * 2 ^ 59
def prefixEnd_1884799 : Nat := 4983230072969 + 3 ^ 40 * 1884799 * 2
def baseEnd_1884799 : Nat := 967807824113676448944473

theorem tailTrace_1884799 : CollatzResearch.WordTrace tailWord_1884799 prefixEnd_1884799 967807824113676448944473 := by
  unfold tailWord_1884799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68744267098702595886697451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45829511399135063924464967 68744267098702595886697451)
  ·
    refine ⟨103116400648053893830046177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68744267098702595886697451 103116400648053893830046177)
    ·
      refine ⟨77337300486040420372534633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103116400648053893830046177 77337300486040420372534633)
      ·
        refine ⟨58002975364530315279400975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77337300486040420372534633 58002975364530315279400975)
        ·
          refine ⟨87004463046795472919101463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58002975364530315279400975 87004463046795472919101463)
          ·
            refine ⟨130506694570193209378652195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87004463046795472919101463 130506694570193209378652195)
            ·
              refine ⟨195760041855289814067978293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130506694570193209378652195 195760041855289814067978293)
              ·
                refine ⟨18352503923933420068872965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195760041855289814067978293 18352503923933420068872965)
                ·
                  refine ⟨3441094485737516262913681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18352503923933420068872965 3441094485737516262913681)
                  ·
                    refine ⟨2580820864303137197185261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441094485737516262913681 2580820864303137197185261)
                    ·
                      refine ⟨967807824113676448944473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580820864303137197185261 967807824113676448944473)
                      ·
                        rfl

theorem cell23_1884799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_1884799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884799 prefixEnd_1884799 := by exact prefixLift 1884799
  have htrace : WordTrace (prefixWord ++ tailWord_1884799) baseStart_1884799 baseEnd_1884799 := by
    simpa [prefixWord, tailWord_1884799, baseEnd_1884799] using wordTrace_append hprefix tailTrace_1884799
  have hstable : (prefixWord ++ tailWord_1884799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884799).length < 2 ^ (prefixWord ++ tailWord_1884799).sum := by decide
  have hdescent : baseEnd_1884799 < baseStart_1884799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884853 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 6]
def baseStart_1884853 : Nat := 118140960795 + 1884853 * 2 ^ 59
def prefixEnd_1884853 : Nat := 4983230072969 + 3 ^ 40 * 1884853 * 2
def baseEnd_1884853 : Nat := 107537283563224359741025

theorem tailTrace_1884853 : CollatzResearch.WordTrace tailWord_1884853 prefixEnd_1884853 107537283563224359741025 := by
  unfold tailWord_1884853
  simp only [CollatzResearch.WordTrace]
  refine ⟨68746236640506963109163213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45830824427004642072775475 68746236640506963109163213)
  ·
    refine ⟨25779838740190111165936205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68746236640506963109163213 25779838740190111165936205)
    ·
      refine ⟨9667439527571291687226077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25779838740190111165936205 9667439527571291687226077)
      ·
        refine ⟨3625289822839234382709779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9667439527571291687226077 3625289822839234382709779)
        ·
          refine ⟨5437934734258851574064669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625289822839234382709779 5437934734258851574064669)
          ·
            refine ⟨2039225525347069340274251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5437934734258851574064669 2039225525347069340274251)
            ·
              refine ⟨3058838288020604010411377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039225525347069340274251 3058838288020604010411377)
              ·
                refine ⟨2294128716015453007808533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058838288020604010411377 2294128716015453007808533)
                ·
                  refine ⟨107537283563224359741025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2294128716015453007808533 107537283563224359741025)
                  ·
                    rfl

theorem cell23_1884853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_1884853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884853 prefixEnd_1884853 := by exact prefixLift 1884853
  have htrace : WordTrace (prefixWord ++ tailWord_1884853) baseStart_1884853 baseEnd_1884853 := by
    simpa [prefixWord, tailWord_1884853, baseEnd_1884853] using wordTrace_append hprefix tailTrace_1884853
  have hstable : (prefixWord ++ tailWord_1884853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884853).length < 2 ^ (prefixWord ++ tailWord_1884853).sum := by decide
  have hdescent : baseEnd_1884853 < baseStart_1884853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884863 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 3]
def baseStart_1884863 : Nat := 118140960795 + 1884863 * 2 ^ 59
def prefixEnd_1884863 : Nat := 4983230072969 + 3 ^ 40 * 1884863 * 2
def baseEnd_1884863 : Nat := 967840686875564198544179

theorem tailTrace_1884863 : CollatzResearch.WordTrace tailWord_1884863 prefixEnd_1884863 967840686875564198544179 := by
  unfold tailWord_1884863
  simp only [CollatzResearch.WordTrace]
  refine ⟨68746601370470734817027243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45831067580313823211351495 68746601370470734817027243)
  ·
    refine ⟨103119902055706102225540865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68746601370470734817027243 103119902055706102225540865)
    ·
      refine ⟨77339926541779576669155649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103119902055706102225540865 77339926541779576669155649)
      ·
        refine ⟨58004944906334682501866737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77339926541779576669155649 58004944906334682501866737)
        ·
          refine ⟨43503708679751011876400053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58004944906334682501866737 43503708679751011876400053)
          ·
            refine ⟨4078472688726657363412505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43503708679751011876400053 4078472688726657363412505)
            ·
              refine ⟨3058854516544993022559379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4078472688726657363412505 3058854516544993022559379)
              ·
                refine ⟨4588281774817489533839069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058854516544993022559379 4588281774817489533839069)
                ·
                  refine ⟨1720605665556558575189651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4588281774817489533839069 1720605665556558575189651)
                  ·
                    refine ⟨2580908498334837862784477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1720605665556558575189651 2580908498334837862784477)
                    ·
                      refine ⟨967840686875564198544179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580908498334837862784477 967840686875564198544179)
                      ·
                        rfl

theorem cell23_1884863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_1884863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884863 prefixEnd_1884863 := by exact prefixLift 1884863
  have htrace : WordTrace (prefixWord ++ tailWord_1884863) baseStart_1884863 baseEnd_1884863 := by
    simpa [prefixWord, tailWord_1884863, baseEnd_1884863] using wordTrace_append hprefix tailTrace_1884863
  have hstable : (prefixWord ++ tailWord_1884863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884863).length < 2 ^ (prefixWord ++ tailWord_1884863).sum := by decide
  have hdescent : baseEnd_1884863 < baseStart_1884863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884889 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1884889 : Nat := 118140960795 + 1884889 * 2 ^ 59
def prefixEnd_1884889 : Nat := 4983230072969 + 3 ^ 40 * 1884889 * 2
def baseEnd_1884889 : Nat := 967854037372581096819059

theorem tailTrace_1884889 : CollatzResearch.WordTrace tailWord_1884889 prefixEnd_1884889 967854037372581096819059 := by
  unfold tailWord_1884889
  simp only [CollatzResearch.WordTrace]
  refine ⟨68747549668376541257473721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45831699778917694171649147 68747549668376541257473721)
  ·
    refine ⟨51560662251282405943105291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68747549668376541257473721 51560662251282405943105291)
    ·
      refine ⟨77340993376923608914657937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51560662251282405943105291 77340993376923608914657937)
      ·
        refine ⟨58005745032692706685993453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77340993376923608914657937 58005745032692706685993453)
        ·
          refine ⟨21752154387259765007247545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58005745032692706685993453 21752154387259765007247545)
          ·
            refine ⟨16314115790444823755435659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21752154387259765007247545 16314115790444823755435659)
            ·
              refine ⟨24471173685667235633153489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16314115790444823755435659 24471173685667235633153489)
              ·
                refine ⟨18353380264250426724865117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24471173685667235633153489 18353380264250426724865117)
                ·
                  refine ⟨6882517599093910021824419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18353380264250426724865117 6882517599093910021824419)
                  ·
                    refine ⟨10323776398640865032736629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882517599093910021824419 10323776398640865032736629)
                    ·
                      refine ⟨967854037372581096819059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10323776398640865032736629 967854037372581096819059)
                      ·
                        rfl

theorem cell23_1884889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1884889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884889 prefixEnd_1884889 := by exact prefixLift 1884889
  have htrace : WordTrace (prefixWord ++ tailWord_1884889) baseStart_1884889 baseEnd_1884889 := by
    simpa [prefixWord, tailWord_1884889, baseEnd_1884889] using wordTrace_append hprefix tailTrace_1884889
  have hstable : (prefixWord ++ tailWord_1884889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884889).length < 2 ^ (prefixWord ++ tailWord_1884889).sum := by decide
  have hdescent : baseEnd_1884889 < baseStart_1884889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884897 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_1884897 : Nat := 118140960795 + 1884897 * 2 ^ 59
def prefixEnd_1884897 : Nat := 4983230072969 + 3 ^ 40 * 1884897 * 2
def baseEnd_1884897 : Nat := 967858145217817065519023

theorem tailTrace_1884897 : CollatzResearch.WordTrace tailWord_1884897 prefixEnd_1884897 967858145217817065519023 := by
  unfold tailWord_1884897
  simp only [CollatzResearch.WordTrace]
  refine ⟨68747841452347558623764945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45831894301565039082509963 68747841452347558623764945)
  ·
    refine ⟨51560881089260668967823709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68747841452347558623764945 51560881089260668967823709)
    ·
      refine ⟨19335330408472750862933891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51560881089260668967823709 19335330408472750862933891)
      ·
        refine ⟨29002995612709126294400837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19335330408472750862933891 29002995612709126294400837)
        ·
          refine ⟨5438061677382961180200157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29002995612709126294400837 5438061677382961180200157)
          ·
            refine ⟨2039273129018610442575059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5438061677382961180200157 2039273129018610442575059)
            ·
              refine ⟨3058909693527915663862589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039273129018610442575059 3058909693527915663862589)
              ·
                refine ⟨1147091135072968373948471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3058909693527915663862589 1147091135072968373948471)
                ·
                  refine ⟨1720636702609452560922707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147091135072968373948471 1720636702609452560922707)
                  ·
                    refine ⟨2580955053914178841384061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1720636702609452560922707 2580955053914178841384061)
                    ·
                      refine ⟨967858145217817065519023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580955053914178841384061 967858145217817065519023)
                      ·
                        rfl

theorem cell23_1884897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_1884897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884897 prefixEnd_1884897 := by exact prefixLift 1884897
  have htrace : WordTrace (prefixWord ++ tailWord_1884897) baseStart_1884897 baseEnd_1884897 := by
    simpa [prefixWord, tailWord_1884897, baseEnd_1884897] using wordTrace_append hprefix tailTrace_1884897
  have hstable : (prefixWord ++ tailWord_1884897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884897).length < 2 ^ (prefixWord ++ tailWord_1884897).sum := by decide
  have hdescent : baseEnd_1884897 < baseStart_1884897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884906 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1884906 : Nat := 118140960795 + 1884906 * 2 ^ 59
def prefixEnd_1884906 : Nat := 4983230072969 + 3 ^ 40 * 1884906 * 2
def baseEnd_1884906 : Nat := 967862766543707530306481

theorem tailTrace_1884906 : CollatzResearch.WordTrace tailWord_1884906 prefixEnd_1884906 967862766543707530306481 := by
  unfold tailWord_1884906
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187042427328738290210643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45832113139543302107228381 17187042427328738290210643)
  ·
    refine ⟨25780563640993107435315965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17187042427328738290210643 25780563640993107435315965)
    ·
      refine ⟨9667711365372415288243487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25780563640993107435315965 9667711365372415288243487)
      ·
        refine ⟨14501567048058622932365231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9667711365372415288243487 14501567048058622932365231)
        ·
          refine ⟨21752350572087934398547847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14501567048058622932365231 21752350572087934398547847)
          ·
            refine ⟨32628525858131901597821771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21752350572087934398547847 32628525858131901597821771)
            ·
              refine ⟨48942788787197852396732657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32628525858131901597821771 48942788787197852396732657)
              ·
                refine ⟨36707091590398389297549493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48942788787197852396732657 36707091590398389297549493)
                ·
                  refine ⟨3441289836599848996645265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36707091590398389297549493 3441289836599848996645265)
                  ·
                    refine ⟨2580967377449886747483949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441289836599848996645265 2580967377449886747483949)
                    ·
                      refine ⟨967862766543707530306481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2580967377449886747483949 967862766543707530306481)
                      ·
                        rfl

theorem cell23_1884906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1884906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884906 prefixEnd_1884906 := by exact prefixLift 1884906
  have htrace : WordTrace (prefixWord ++ tailWord_1884906) baseStart_1884906 baseEnd_1884906 := by
    simpa [prefixWord, tailWord_1884906, baseEnd_1884906] using wordTrace_append hprefix tailTrace_1884906
  have hstable : (prefixWord ++ tailWord_1884906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884906).length < 2 ^ (prefixWord ++ tailWord_1884906).sum := by decide
  have hdescent : baseEnd_1884906 < baseStart_1884906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884926 : List Nat := [4, 2, 2, 1, 2, 1, 1, 10]
def baseStart_1884926 : Nat := 118140960795 + 1884926 * 2 ^ 59
def prefixEnd_1884926 : Nat := 4983230072969 + 3 ^ 40 * 1884926 * 2
def baseEnd_1884926 : Nat := 35847149487288794520607

theorem tailTrace_1884926 : CollatzResearch.WordTrace tailWord_1884926 prefixEnd_1884926 35847149487288794520607 := by
  unfold tailWord_1884926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8593612396155312072071329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45832599446161664384380421 8593612396155312072071329)
  ·
    refine ⟨6445209297116484054053497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8593612396155312072071329 6445209297116484054053497)
    ·
      refine ⟨4833906972837363040540123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6445209297116484054053497 4833906972837363040540123)
      ·
        refine ⟨7250860459256044560810185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833906972837363040540123 7250860459256044560810185)
        ·
          refine ⟨5438145344442033420607639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250860459256044560810185 5438145344442033420607639)
          ·
            refine ⟨8157218016663050130911459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438145344442033420607639 8157218016663050130911459)
            ·
              refine ⟨12235827024994575196367189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157218016663050130911459 12235827024994575196367189)
              ·
                refine ⟨35847149487288794520607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12235827024994575196367189 35847149487288794520607)
                ·
                  rfl

theorem cell23_1884926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_1884926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884926 prefixEnd_1884926 := by exact prefixLift 1884926
  have htrace : WordTrace (prefixWord ++ tailWord_1884926) baseStart_1884926 baseEnd_1884926 := by
    simpa [prefixWord, tailWord_1884926, baseEnd_1884926] using wordTrace_append hprefix tailTrace_1884926
  have hstable : (prefixWord ++ tailWord_1884926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884926).length < 2 ^ (prefixWord ++ tailWord_1884926).sum := by decide
  have hdescent : baseEnd_1884926 < baseStart_1884926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884929 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1884929 : Nat := 118140960795 + 1884929 * 2 ^ 59
def prefixEnd_1884929 : Nat := 4983230072969 + 3 ^ 40 * 1884929 * 2
def baseEnd_1884929 : Nat := 967874576598760940318875

theorem tailTrace_1884929 : CollatzResearch.WordTrace tailWord_1884929 prefixEnd_1884929 967874576598760940318875 := by
  unfold tailWord_1884929
  simp only [CollatzResearch.WordTrace]
  refine ⟨68749008588231628088929841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45832672392154418725953227 68749008588231628088929841)
  ·
    refine ⟨51561756441173721066697381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68749008588231628088929841 51561756441173721066697381)
    ·
      refine ⟨9667829332720072700005759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51561756441173721066697381 9667829332720072700005759)
      ·
        refine ⟨14501743999080109050008639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9667829332720072700005759 14501743999080109050008639)
        ·
          refine ⟨21752615998620163575012959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14501743999080109050008639 21752615998620163575012959)
          ·
            refine ⟨32628923997930245362519439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21752615998620163575012959 32628923997930245362519439)
            ·
              refine ⟨48943385996895368043779159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32628923997930245362519439 48943385996895368043779159)
              ·
                refine ⟨73415078995343052065668739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48943385996895368043779159 73415078995343052065668739)
                ·
                  refine ⟨110122618493014578098503109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73415078995343052065668739 110122618493014578098503109)
                  ·
                    refine ⟨20647990967440233393469333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110122618493014578098503109 20647990967440233393469333)
                    ·
                      refine ⟨967874576598760940318875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20647990967440233393469333 967874576598760940318875)
                      ·
                        rfl

theorem cell23_1884929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1884929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884929 prefixEnd_1884929 := by exact prefixLift 1884929
  have htrace : WordTrace (prefixWord ++ tailWord_1884929) baseStart_1884929 baseEnd_1884929 := by
    simpa [prefixWord, tailWord_1884929, baseEnd_1884929] using wordTrace_append hprefix tailTrace_1884929
  have hstable : (prefixWord ++ tailWord_1884929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884929).length < 2 ^ (prefixWord ++ tailWord_1884929).sum := by decide
  have hdescent : baseEnd_1884929 < baseStart_1884929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884930 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1884930 : Nat := 118140960795 + 1884930 * 2 ^ 59
def prefixEnd_1884930 : Nat := 4983230072969 + 3 ^ 40 * 1884930 * 2
def baseEnd_1884930 : Nat := 322625030026471812135457

theorem tailTrace_1884930 : CollatzResearch.WordTrace tailWord_1884930 prefixEnd_1884930 322625030026471812135457 := by
  unfold tailWord_1884930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187261265307001314929061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45832696707485336839810829 17187261265307001314929061)
  ·
    refine ⟨3222611487245062746549199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17187261265307001314929061 3222611487245062746549199)
    ·
      refine ⟨4833917230867594119823799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222611487245062746549199 4833917230867594119823799)
      ·
        refine ⟨7250875846301391179735699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833917230867594119823799 7250875846301391179735699)
        ·
          refine ⟨10876313769452086769603549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250875846301391179735699 10876313769452086769603549)
          ·
            refine ⟨4078617663544532538601331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10876313769452086769603549 4078617663544532538601331)
            ·
              refine ⟨6117926495316798807901997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078617663544532538601331 6117926495316798807901997)
              ·
                refine ⟨2294222435743799552963249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6117926495316798807901997 2294222435743799552963249)
                ·
                  refine ⟨1720666826807849664722437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2294222435743799552963249 1720666826807849664722437)
                  ·
                    refine ⟨322625030026471812135457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1720666826807849664722437 322625030026471812135457)
                    ·
                      rfl

theorem cell23_1884930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1884930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884930 prefixEnd_1884930 := by exact prefixLift 1884930
  have htrace : WordTrace (prefixWord ++ tailWord_1884930) baseStart_1884930 baseEnd_1884930 := by
    simpa [prefixWord, tailWord_1884930, baseEnd_1884930] using wordTrace_append hprefix tailTrace_1884930
  have hstable : (prefixWord ++ tailWord_1884930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884930).length < 2 ^ (prefixWord ++ tailWord_1884930).sum := by decide
  have hdescent : baseEnd_1884930 < baseStart_1884930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884957 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1884957 : Nat := 118140960795 + 1884957 * 2 ^ 59
def prefixEnd_1884957 : Nat := 4983230072969 + 3 ^ 40 * 1884957 * 2
def baseEnd_1884957 : Nat := 967888954057086830768747

theorem tailTrace_1884957 : CollatzResearch.WordTrace tailWord_1884957 prefixEnd_1884957 967888954057086830768747 := by
  unfold tailWord_1884957
  simp only [CollatzResearch.WordTrace]
  refine ⟨68750029832130188870949125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45833353221420125913966083 68750029832130188870949125)
  ·
    refine ⟨12890630593524410413302961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68750029832130188870949125 12890630593524410413302961)
    ·
      refine ⟨9667972945143307809977221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12890630593524410413302961 9667972945143307809977221)
      ·
        refine ⟨1812744927214370214370729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9667972945143307809977221 1812744927214370214370729)
        ·
          refine ⟨1359558695410777660778047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812744927214370214370729 1359558695410777660778047)
          ·
            refine ⟨2039338043116166491167071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359558695410777660778047 2039338043116166491167071)
            ·
              refine ⟨3059007064674249736750607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039338043116166491167071 3059007064674249736750607)
              ·
                refine ⟨4588510597011374605125911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059007064674249736750607 4588510597011374605125911)
                ·
                  refine ⟨6882765895517061907688867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588510597011374605125911 6882765895517061907688867)
                  ·
                    refine ⟨10324148843275592861533301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882765895517061907688867 10324148843275592861533301)
                    ·
                      refine ⟨967888954057086830768747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10324148843275592861533301 967888954057086830768747)
                      ·
                        rfl

theorem cell23_1884957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1884957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884957 prefixEnd_1884957 := by exact prefixLift 1884957
  have htrace : WordTrace (prefixWord ++ tailWord_1884957) baseStart_1884957 baseEnd_1884957 := by
    simpa [prefixWord, tailWord_1884957, baseEnd_1884957] using wordTrace_append hprefix tailTrace_1884957
  have hstable : (prefixWord ++ tailWord_1884957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884957).length < 2 ^ (prefixWord ++ tailWord_1884957).sum := by decide
  have hdescent : baseEnd_1884957 < baseStart_1884957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884969 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_1884969 : Nat := 118140960795 + 1884969 * 2 ^ 59
def prefixEnd_1884969 : Nat := 4983230072969 + 3 ^ 40 * 1884969 * 2
def baseEnd_1884969 : Nat := 322631705274980261272897

theorem tailTrace_1884969 : CollatzResearch.WordTrace tailWord_1884969 prefixEnd_1884969 322631705274980261272897 := by
  unfold tailWord_1884969
  simp only [CollatzResearch.WordTrace]
  refine ⟨68750467508086714920385961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45833645005391143280257307 68750467508086714920385961)
  ·
    refine ⟨51562850631065036190289471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68750467508086714920385961 51562850631065036190289471)
    ·
      refine ⟨77344275946597554285434207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51562850631065036190289471 77344275946597554285434207)
      ·
        refine ⟨116016413919896331428151311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77344275946597554285434207 116016413919896331428151311)
        ·
          refine ⟨174024620879844497142226967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116016413919896331428151311 174024620879844497142226967)
          ·
            refine ⟨261036931319766745713340451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174024620879844497142226967 261036931319766745713340451)
            ·
              refine ⟨391555396979650118570010677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261036931319766745713340451 391555396979650118570010677)
              ·
                refine ⟨36708318466842198615938501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391555396979650118570010677 36708318466842198615938501)
                ·
                  refine ⟨6882809712532912240488469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36708318466842198615938501 6882809712532912240488469)
                  ·
                    refine ⟨322631705274980261272897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6882809712532912240488469 322631705274980261272897)
                    ·
                      rfl

theorem cell23_1884969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_1884969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1884969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1884969 prefixEnd_1884969 := by exact prefixLift 1884969
  have htrace : WordTrace (prefixWord ++ tailWord_1884969) baseStart_1884969 baseEnd_1884969 := by
    simpa [prefixWord, tailWord_1884969, baseEnd_1884969] using wordTrace_append hprefix tailTrace_1884969
  have hstable : (prefixWord ++ tailWord_1884969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884969).length < 2 ^ (prefixWord ++ tailWord_1884969).sum := by decide
  have hdescent : baseEnd_1884969 < baseStart_1884969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885010 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_1885010 : Nat := 118140960795 + 1885010 * 2 ^ 59
def prefixEnd_1885010 : Nat := 4983230072969 + 3 ^ 40 * 1885010 * 2
def baseEnd_1885010 : Nat := 967916168531775123406003

theorem tailTrace_1885010 : CollatzResearch.WordTrace tailWord_1885010 prefixEnd_1885010 967916168531775123406003 := by
  unfold tailWord_1885010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187990725234544730657121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45834641933958785948418989 17187990725234544730657121)
  ·
    refine ⟨12890993043925908547992841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17187990725234544730657121 12890993043925908547992841)
    ·
      refine ⟨9668244782944431410994631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12890993043925908547992841 9668244782944431410994631)
      ·
        refine ⟨14502367174416647116491947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9668244782944431410994631 14502367174416647116491947)
        ·
          refine ⟨21753550761624970674737921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14502367174416647116491947 21753550761624970674737921)
          ·
            refine ⟨16315163071218728006053441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21753550761624970674737921 16315163071218728006053441)
            ·
              refine ⟨12236372303414046004540081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16315163071218728006053441 12236372303414046004540081)
              ·
                refine ⟨9177279227560534503405061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12236372303414046004540081 9177279227560534503405061)
                ·
                  refine ⟨1720739855167600219388449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9177279227560534503405061 1720739855167600219388449)
                  ·
                    refine ⟨1290554891375700164541337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1720739855167600219388449 1290554891375700164541337)
                    ·
                      refine ⟨967916168531775123406003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290554891375700164541337 967916168531775123406003)
                      ·
                        rfl

theorem cell23_1885010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_1885010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885010 prefixEnd_1885010 := by exact prefixLift 1885010
  have htrace : WordTrace (prefixWord ++ tailWord_1885010) baseStart_1885010 baseEnd_1885010 := by
    simpa [prefixWord, tailWord_1885010, baseEnd_1885010] using wordTrace_append hprefix tailTrace_1885010
  have hstable : (prefixWord ++ tailWord_1885010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885010).length < 2 ^ (prefixWord ++ tailWord_1885010).sum := by decide
  have hdescent : baseEnd_1885010 < baseStart_1885010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885019 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_1885019 : Nat := 118140960795 + 1885019 * 2 ^ 59
def prefixEnd_1885019 : Nat := 4983230072969 + 3 ^ 40 * 1885019 * 2
def baseEnd_1885019 : Nat := 967920789857665588193461

theorem tailTrace_1885019 : CollatzResearch.WordTrace tailWord_1885019 prefixEnd_1885019 967920789857665588193461 := by
  unfold tailWord_1885019
  simp only [CollatzResearch.WordTrace]
  refine ⟨68752291157905573459706111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45834860771937048973137407 68752291157905573459706111)
  ·
    refine ⟨103128436736858360189559167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68752291157905573459706111 103128436736858360189559167)
    ·
      refine ⟨154692655105287540284338751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103128436736858360189559167 154692655105287540284338751)
      ·
        refine ⟨232038982657931310426508127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154692655105287540284338751 232038982657931310426508127)
        ·
          refine ⟨348058473986896965639762191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232038982657931310426508127 348058473986896965639762191)
          ·
            refine ⟨522087710980345448459643287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348058473986896965639762191 522087710980345448459643287)
            ·
              refine ⟨783131566470518172689464931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522087710980345448459643287 783131566470518172689464931)
              ·
                refine ⟨1174697349705777259034197397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783131566470518172689464931 1174697349705777259034197397)
                ·
                  refine ⟨55063938267458309017228003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1174697349705777259034197397 55063938267458309017228003)
                  ·
                    refine ⟨82595907401187463525842005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55063938267458309017228003 82595907401187463525842005)
                    ·
                      refine ⟨967920789857665588193461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 82595907401187463525842005 967920789857665588193461)
                      ·
                        rfl

theorem cell23_1885019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_1885019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885019 prefixEnd_1885019 := by exact prefixLift 1885019
  have htrace : WordTrace (prefixWord ++ tailWord_1885019) baseStart_1885019 baseEnd_1885019 := by
    simpa [prefixWord, tailWord_1885019, baseEnd_1885019] using wordTrace_append hprefix tailTrace_1885019
  have hstable : (prefixWord ++ tailWord_1885019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885019).length < 2 ^ (prefixWord ++ tailWord_1885019).sum := by decide
  have hdescent : baseEnd_1885019 < baseStart_1885019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885027 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1885027 : Nat := 118140960795 + 1885027 * 2 ^ 59
def prefixEnd_1885027 : Nat := 4983230072969 + 3 ^ 40 * 1885027 * 2
def baseEnd_1885027 : Nat := 967924897702901556893425

theorem tailTrace_1885027 : CollatzResearch.WordTrace tailWord_1885027 prefixEnd_1885027 967924897702901556893425 := by
  unfold tailWord_1885027
  simp only [CollatzResearch.WordTrace]
  refine ⟨68752582941876590825997335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45835055294584393883998223 68752582941876590825997335)
  ·
    refine ⟨103128874412814886238996003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68752582941876590825997335 103128874412814886238996003)
    ·
      refine ⟨154693311619222329358494005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103128874412814886238996003 154693311619222329358494005)
      ·
        refine ⟨14502497964302093377358813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154693311619222329358494005 14502497964302093377358813)
        ·
          refine ⟨5438436736613285016509555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14502497964302093377358813 5438436736613285016509555)
          ·
            refine ⟨8157655104919927524764333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438436736613285016509555 8157655104919927524764333)
            ·
              refine ⟨3059120664344972821786625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8157655104919927524764333 3059120664344972821786625)
              ·
                refine ⟨2294340498258729616339969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059120664344972821786625 2294340498258729616339969)
                ·
                  refine ⟨1720755373694047212254977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2294340498258729616339969 1720755373694047212254977)
                  ·
                    refine ⟨1290566530270535409191233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1720755373694047212254977 1290566530270535409191233)
                    ·
                      refine ⟨967924897702901556893425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290566530270535409191233 967924897702901556893425)
                      ·
                        rfl

theorem cell23_1885027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1885027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885027 prefixEnd_1885027 := by exact prefixLift 1885027
  have htrace : WordTrace (prefixWord ++ tailWord_1885027) baseStart_1885027 baseEnd_1885027 := by
    simpa [prefixWord, tailWord_1885027, baseEnd_1885027] using wordTrace_append hprefix tailTrace_1885027
  have hstable : (prefixWord ++ tailWord_1885027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885027).length < 2 ^ (prefixWord ++ tailWord_1885027).sum := by decide
  have hdescent : baseEnd_1885027 < baseStart_1885027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885053 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_1885053 : Nat := 118140960795 + 1885053 * 2 ^ 59
def prefixEnd_1885053 : Nat := 4983230072969 + 3 ^ 40 * 1885053 * 2
def baseEnd_1885053 : Nat := 967938248199918455168305

theorem tailTrace_1885053 : CollatzResearch.WordTrace tailWord_1885053 prefixEnd_1885053 967938248199918455168305 := by
  unfold tailWord_1885053
  simp only [CollatzResearch.WordTrace]
  refine ⟨68753531239782397266443813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45835687493188264844295875 68753531239782397266443813)
  ·
    refine ⟨12891287107459199487458215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68753531239782397266443813 12891287107459199487458215)
    ·
      refine ⟨19336930661188799231187323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12891287107459199487458215 19336930661188799231187323)
      ·
        refine ⟨29005395991783198846780985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336930661188799231187323 29005395991783198846780985)
        ·
          refine ⟨21754046993837399135085739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29005395991783198846780985 21754046993837399135085739)
          ·
            refine ⟨32631070490756098702628609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21754046993837399135085739 32631070490756098702628609)
            ·
              refine ⟨24473302868067074026971457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32631070490756098702628609 24473302868067074026971457)
              ·
                refine ⟨18354977151050305520228593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24473302868067074026971457 18354977151050305520228593)
                ·
                  refine ⟨13766232863287729140171445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18354977151050305520228593 13766232863287729140171445)
                  ·
                    refine ⟨1290584330933224606891073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13766232863287729140171445 1290584330933224606891073)
                    ·
                      refine ⟨967938248199918455168305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290584330933224606891073 967938248199918455168305)
                      ·
                        rfl

theorem cell23_1885053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_1885053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885053 prefixEnd_1885053 := by exact prefixLift 1885053
  have htrace : WordTrace (prefixWord ++ tailWord_1885053) baseStart_1885053 baseEnd_1885053 := by
    simpa [prefixWord, tailWord_1885053, baseEnd_1885053] using wordTrace_append hprefix tailTrace_1885053
  have hstable : (prefixWord ++ tailWord_1885053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885053).length < 2 ^ (prefixWord ++ tailWord_1885053).sum := by decide
  have hdescent : baseEnd_1885053 < baseStart_1885053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885120 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1885120 : Nat := 118140960795 + 1885120 * 2 ^ 59
def prefixEnd_1885120 : Nat := 4983230072969 + 3 ^ 40 * 1885120 * 2
def baseEnd_1885120 : Nat := 967972651403769693030497

theorem tailTrace_1885120 : CollatzResearch.WordTrace tailWord_1885120 prefixEnd_1885120 967972651403769693030497 := by
  unfold tailWord_1885120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34377987465269833854566407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45837316620359778472755209 34377987465269833854566407)
  ·
    refine ⟨51566981197904750781849611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34377987465269833854566407 51566981197904750781849611)
    ·
      refine ⟨77350471796857126172774417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51566981197904750781849611 77350471796857126172774417)
      ·
        refine ⟨58012853847642844629580813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77350471796857126172774417 58012853847642844629580813)
        ·
          refine ⟨21754820192866066736092805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58012853847642844629580813 21754820192866066736092805)
          ·
            refine ⟨4079028786162387513017401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21754820192866066736092805 4079028786162387513017401)
            ·
              refine ⟨3059271589621790634763051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079028786162387513017401 3059271589621790634763051)
              ·
                refine ⟨4588907384432685952144577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059271589621790634763051 4588907384432685952144577)
                ·
                  refine ⟨3441680538324514464108433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588907384432685952144577 3441680538324514464108433)
                  ·
                    refine ⟨2581260403743385848081325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441680538324514464108433 2581260403743385848081325)
                    ·
                      refine ⟨967972651403769693030497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2581260403743385848081325 967972651403769693030497)
                      ·
                        rfl

theorem cell23_1885120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1885120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885120 prefixEnd_1885120 := by exact prefixLift 1885120
  have htrace : WordTrace (prefixWord ++ tailWord_1885120) baseStart_1885120 baseEnd_1885120 := by
    simpa [prefixWord, tailWord_1885120, baseEnd_1885120] using wordTrace_append hprefix tailTrace_1885120
  have hstable : (prefixWord ++ tailWord_1885120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885120).length < 2 ^ (prefixWord ++ tailWord_1885120).sum := by decide
  have hdescent : baseEnd_1885120 < baseStart_1885120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885140 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 6]
def baseStart_1885140 : Nat := 118140960795 + 1885140 * 2 ^ 59
def prefixEnd_1885140 : Nat := 4983230072969 + 3 ^ 40 * 1885140 * 2
def baseEnd_1885140 : Nat := 107553657890762179420045

theorem tailTrace_1885140 : CollatzResearch.WordTrace tailWord_1885140 prefixEnd_1885140 107553657890762179420045 := by
  unfold tailWord_1885140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34378352195233605562430437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45837802926978140749907249 34378352195233605562430437)
  ·
    refine ⟨6445941036606301042955707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34378352195233605562430437 6445941036606301042955707)
    ·
      refine ⟨9668911554909451564433561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445941036606301042955707 9668911554909451564433561)
      ·
        refine ⟨7251683666182088673325171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9668911554909451564433561 7251683666182088673325171)
        ·
          refine ⟨10877525499273133009987757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251683666182088673325171 10877525499273133009987757)
          ·
            refine ⟨4079072062227424878745409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10877525499273133009987757 4079072062227424878745409)
            ·
              refine ⟨3059304046670568659059057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079072062227424878745409 3059304046670568659059057)
              ·
                refine ⟨2294478035002926494294293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059304046670568659059057 2294478035002926494294293)
                ·
                  refine ⟨107553657890762179420045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2294478035002926494294293 107553657890762179420045)
                  ·
                    rfl

theorem cell23_1885140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_1885140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885140 prefixEnd_1885140 := by exact prefixLift 1885140
  have htrace : WordTrace (prefixWord ++ tailWord_1885140) baseStart_1885140 baseEnd_1885140 := by
    simpa [prefixWord, tailWord_1885140, baseEnd_1885140] using wordTrace_append hprefix tailTrace_1885140
  have hstable : (prefixWord ++ tailWord_1885140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885140).length < 2 ^ (prefixWord ++ tailWord_1885140).sum := by decide
  have hdescent : baseEnd_1885140 < baseStart_1885140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885144 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 1, 4]
def baseStart_1885144 : Nat := 118140960795 + 1885144 * 2 ^ 59
def prefixEnd_1885144 : Nat := 4983230072969 + 3 ^ 40 * 1885144 * 2
def baseEnd_1885144 : Nat := 322661658313159199710129

theorem tailTrace_1885144 : CollatzResearch.WordTrace tailWord_1885144 prefixEnd_1885144 322661658313159199710129 := by
  unfold tailWord_1885144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34378425141226359904003243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45837900188301813205337657 34378425141226359904003243)
  ·
    refine ⟨51567637711839539856004865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34378425141226359904003243 51567637711839539856004865)
    ·
      refine ⟨38675728283879654892003649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51567637711839539856004865 38675728283879654892003649)
      ·
        refine ⟨29006796212909741169002737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38675728283879654892003649 29006796212909741169002737)
        ·
          refine ⟨21755097159682305876752053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29006796212909741169002737 21755097159682305876752053)
          ·
            refine ⟨2039540358720216175945505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21755097159682305876752053 2039540358720216175945505)
            ·
              refine ⟨1529655269040162131959129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039540358720216175945505 1529655269040162131959129)
              ·
                refine ⟨1147241451780121598969347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529655269040162131959129 1147241451780121598969347)
                ·
                  refine ⟨1720862177670182398454021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147241451780121598969347 1720862177670182398454021)
                  ·
                    refine ⟨322661658313159199710129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1720862177670182398454021 322661658313159199710129)
                    ·
                      rfl

theorem cell23_1885144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_1885144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885144 prefixEnd_1885144 := by exact prefixLift 1885144
  have htrace : WordTrace (prefixWord ++ tailWord_1885144) baseStart_1885144 baseEnd_1885144 := by
    simpa [prefixWord, tailWord_1885144, baseEnd_1885144] using wordTrace_append hprefix tailTrace_1885144
  have hstable : (prefixWord ++ tailWord_1885144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885144).length < 2 ^ (prefixWord ++ tailWord_1885144).sum := by decide
  have hdescent : baseEnd_1885144 < baseStart_1885144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885160 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1885160 : Nat := 118140960795 + 1885160 * 2 ^ 59
def prefixEnd_1885160 : Nat := 4983230072969 + 3 ^ 40 * 1885160 * 2
def baseEnd_1885160 : Nat := 967993190629949536530313

theorem tailTrace_1885160 : CollatzResearch.WordTrace tailWord_1885160 prefixEnd_1885160 967993190629949536530313 := by
  unfold tailWord_1885160
  simp only [CollatzResearch.WordTrace]
  refine ⟨34378716925197377270294467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45838289233596503027059289 34378716925197377270294467)
  ·
    refine ⟨51568075387796065905441701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34378716925197377270294467 51568075387796065905441701)
    ·
      refine ⟨9669014135211762357270319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51568075387796065905441701 9669014135211762357270319)
      ·
        refine ⟨14503521202817643535905479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9669014135211762357270319 14503521202817643535905479)
        ·
          refine ⟨21755281804226465303858219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14503521202817643535905479 21755281804226465303858219)
          ·
            refine ⟨32632922706339697955787329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21755281804226465303858219 32632922706339697955787329)
            ·
              refine ⟨24474692029754773466840497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32632922706339697955787329 24474692029754773466840497)
              ·
                refine ⟨18356019022316080100130373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24474692029754773466840497 18356019022316080100130373)
                ·
                  refine ⟨3441753566684265018774445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18356019022316080100130373 3441753566684265018774445)
                  ·
                    refine ⟨1290657587506599382040417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441753566684265018774445 1290657587506599382040417)
                    ·
                      refine ⟨967993190629949536530313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290657587506599382040417 967993190629949536530313)
                      ·
                        rfl

theorem cell23_1885160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1885160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885160 prefixEnd_1885160 := by exact prefixLift 1885160
  have htrace : WordTrace (prefixWord ++ tailWord_1885160) baseStart_1885160 baseEnd_1885160 := by
    simpa [prefixWord, tailWord_1885160, baseEnd_1885160] using wordTrace_append hprefix tailTrace_1885160
  have hstable : (prefixWord ++ tailWord_1885160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885160).length < 2 ^ (prefixWord ++ tailWord_1885160).sum := by decide
  have hdescent : baseEnd_1885160 < baseStart_1885160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885220 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1885220 : Nat := 118140960795 + 1885220 * 2 ^ 59
def prefixEnd_1885220 : Nat := 4983230072969 + 3 ^ 40 * 1885220 * 2
def baseEnd_1885220 : Nat := 968023999469219301780037

theorem tailTrace_1885220 : CollatzResearch.WordTrace tailWord_1885220 prefixEnd_1885220 968023999469219301780037 := by
  unfold tailWord_1885220
  simp only [CollatzResearch.WordTrace]
  refine ⟨34379811115088692393886557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45839748153451589858515409 34379811115088692393886557)
  ·
    refine ⟨12892429168158259647707459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34379811115088692393886557 12892429168158259647707459)
    ·
      refine ⟨19338643752237389471561189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892429168158259647707459 19338643752237389471561189)
      ·
        refine ⟨3625995703544510525917723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19338643752237389471561189 3625995703544510525917723)
        ·
          refine ⟨5438993555316765788876585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625995703544510525917723 5438993555316765788876585)
          ·
            refine ⟨4079245166487574341657439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5438993555316765788876585 4079245166487574341657439)
            ·
              refine ⟨6118867749731361512486159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079245166487574341657439 6118867749731361512486159)
              ·
                refine ⟨9178301624597042268729239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118867749731361512486159 9178301624597042268729239)
                ·
                  refine ⟨13767452436895563403093859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9178301624597042268729239 13767452436895563403093859)
                  ·
                    refine ⟨20651178655343345104640789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13767452436895563403093859 20651178655343345104640789)
                    ·
                      refine ⟨968023999469219301780037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20651178655343345104640789 968023999469219301780037)
                      ·
                        rfl

theorem cell23_1885220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1885220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885220 prefixEnd_1885220 := by exact prefixLift 1885220
  have htrace : WordTrace (prefixWord ++ tailWord_1885220) baseStart_1885220 baseEnd_1885220 := by
    simpa [prefixWord, tailWord_1885220, baseEnd_1885220] using wordTrace_append hprefix tailTrace_1885220
  have hstable : (prefixWord ++ tailWord_1885220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885220).length < 2 ^ (prefixWord ++ tailWord_1885220).sum := by decide
  have hdescent : baseEnd_1885220 < baseStart_1885220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885241 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1885241 : Nat := 118140960795 + 1885241 * 2 ^ 59
def prefixEnd_1885241 : Nat := 4983230072969 + 3 ^ 40 * 1885241 * 2
def baseEnd_1885241 : Nat := 968034782562963719617441

theorem tailTrace_1885241 : CollatzResearch.WordTrace tailWord_1885241 prefixEnd_1885241 968034782562963719617441 := by
  unfold tailWord_1885241
  simp only [CollatzResearch.WordTrace]
  refine ⟨68760388163101305374287577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45840258775400870249525051 68760388163101305374287577)
  ·
    refine ⟨51570291122325979030715683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68760388163101305374287577 51570291122325979030715683)
    ·
      refine ⟨77355436683488968546073525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51570291122325979030715683 77355436683488968546073525)
      ·
        refine ⟨7252072189077090801194393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77355436683488968546073525 7252072189077090801194393)
        ·
          refine ⟨5439054141807818100895795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7252072189077090801194393 5439054141807818100895795)
          ·
            refine ⟨8158581212711727151343693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439054141807818100895795 8158581212711727151343693)
            ·
              refine ⟨3059467954766897681753885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8158581212711727151343693 3059467954766897681753885)
              ·
                refine ⟨1147300483037586630657707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059467954766897681753885 1147300483037586630657707)
                ·
                  refine ⟨1720950724556379945986561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147300483037586630657707 1720950724556379945986561)
                  ·
                    refine ⟨1290713043417284959489921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1720950724556379945986561 1290713043417284959489921)
                    ·
                      refine ⟨968034782562963719617441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290713043417284959489921 968034782562963719617441)
                      ·
                        rfl

theorem cell23_1885241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1885241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885241 prefixEnd_1885241 := by exact prefixLift 1885241
  have htrace : WordTrace (prefixWord ++ tailWord_1885241) baseStart_1885241 baseEnd_1885241 := by
    simpa [prefixWord, tailWord_1885241, baseEnd_1885241] using wordTrace_append hprefix tailTrace_1885241
  have hstable : (prefixWord ++ tailWord_1885241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885241).length < 2 ^ (prefixWord ++ tailWord_1885241).sum := by decide
  have hdescent : baseEnd_1885241 < baseStart_1885241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885278 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1885278 : Nat := 118140960795 + 1885278 * 2 ^ 59
def prefixEnd_1885278 : Nat := 4983230072969 + 3 ^ 40 * 1885278 * 2
def baseEnd_1885278 : Nat := 968053781347180074854771

theorem tailTrace_1885278 : CollatzResearch.WordTrace tailWord_1885278 prefixEnd_1885278 968053781347180074854771 := by
  unfold tailWord_1885278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595217207995907586673061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45841158442644840462256325 8595217207995907586673061)
  ·
    refine ⟨1611603226499232672501199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8595217207995907586673061 1611603226499232672501199)
    ·
      refine ⟨2417404839748849008751799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611603226499232672501199 2417404839748849008751799)
      ·
        refine ⟨3626107259623273513127699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417404839748849008751799 3626107259623273513127699)
        ·
          refine ⟨5439160889434910269691549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626107259623273513127699 5439160889434910269691549)
          ·
            refine ⟨2039685333538091351134331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5439160889434910269691549 2039685333538091351134331)
            ·
              refine ⟨3059528000307137026701497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039685333538091351134331 3059528000307137026701497)
              ·
                refine ⟨2294646000230352770026123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059528000307137026701497 2294646000230352770026123)
                ·
                  refine ⟨3441969000345529155039185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294646000230352770026123 3441969000345529155039185)
                  ·
                    refine ⟨2581476750259146866279389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441969000345529155039185 2581476750259146866279389)
                    ·
                      refine ⟨968053781347180074854771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2581476750259146866279389 968053781347180074854771)
                      ·
                        rfl

theorem cell23_1885278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1885278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885278 prefixEnd_1885278 := by exact prefixLift 1885278
  have htrace : WordTrace (prefixWord ++ tailWord_1885278) baseStart_1885278 baseEnd_1885278 := by
    simpa [prefixWord, tailWord_1885278, baseEnd_1885278] using wordTrace_append hprefix tailTrace_1885278
  have hstable : (prefixWord ++ tailWord_1885278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885278).length < 2 ^ (prefixWord ++ tailWord_1885278).sum := by decide
  have hdescent : baseEnd_1885278 < baseStart_1885278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885297 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_1885297 : Nat := 118140960795 + 1885297 * 2 ^ 59
def prefixEnd_1885297 : Nat := 4983230072969 + 3 ^ 40 * 1885297 * 2
def baseEnd_1885297 : Nat := 968063537479615500517183

theorem tailTrace_1885297 : CollatzResearch.WordTrace tailWord_1885297 prefixEnd_1885297 968063537479615500517183 := by
  unfold tailWord_1885297
  simp only [CollatzResearch.WordTrace]
  refine ⟨68762430650898426938326145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45841620433932284625550763 68762430650898426938326145)
  ·
    refine ⟨51571822988173820203744609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68762430650898426938326145 51571822988173820203744609)
    ·
      refine ⟨38678867241130365152808457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51571822988173820203744609 38678867241130365152808457)
      ·
        refine ⟨29009150430847773864606343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38678867241130365152808457 29009150430847773864606343)
        ·
          refine ⟨43513725646271660796909515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29009150430847773864606343 43513725646271660796909515)
          ·
            refine ⟨65270588469407491195364273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43513725646271660796909515 65270588469407491195364273)
            ·
              refine ⟨48952941352055618396523205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65270588469407491195364273 48952941352055618396523205)
              ·
                refine ⟨9178676503510428449348101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48952941352055618396523205 9178676503510428449348101)
                ·
                  refine ⟨1721001844408205334252769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9178676503510428449348101 1721001844408205334252769)
                  ·
                    refine ⟨1290751383306154000689577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721001844408205334252769 1290751383306154000689577)
                    ·
                      refine ⟨968063537479615500517183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290751383306154000689577 968063537479615500517183)
                      ·
                        rfl

theorem cell23_1885297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_1885297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885297 prefixEnd_1885297 := by exact prefixLift 1885297
  have htrace : WordTrace (prefixWord ++ tailWord_1885297) baseStart_1885297 baseEnd_1885297 := by
    simpa [prefixWord, tailWord_1885297, baseEnd_1885297] using wordTrace_append hprefix tailTrace_1885297
  have hstable : (prefixWord ++ tailWord_1885297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885297).length < 2 ^ (prefixWord ++ tailWord_1885297).sum := by decide
  have hdescent : baseEnd_1885297 < baseStart_1885297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885354 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_1885354 : Nat := 118140960795 + 1885354 * 2 ^ 59
def prefixEnd_1885354 : Nat := 4983230072969 + 3 ^ 40 * 1885354 * 2
def baseEnd_1885354 : Nat := 107565867319657975278269

theorem tailTrace_1885354 : CollatzResearch.WordTrace tailWord_1885354 prefixEnd_1885354 107565867319657975278269 := by
  unfold tailWord_1885354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191127402922981418287779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45843006407794617115434077 17191127402922981418287779)
  ·
    refine ⟨25786691104384472127431669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17191127402922981418287779 25786691104384472127431669)
    ·
      refine ⟨2417502291036044261946719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25786691104384472127431669 2417502291036044261946719)
      ·
        refine ⟨3626253436554066392920079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417502291036044261946719 3626253436554066392920079)
        ·
          refine ⟨5439380154831099589380119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626253436554066392920079 5439380154831099589380119)
          ·
            refine ⟨8159070232246649384070179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439380154831099589380119 8159070232246649384070179)
            ·
              refine ⟨12238605348369974076105269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159070232246649384070179 12238605348369974076105269)
              ·
                refine ⟨1147369251409685069634869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12238605348369974076105269 1147369251409685069634869)
                ·
                  refine ⟨107565867319657975278269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147369251409685069634869 107565867319657975278269)
                  ·
                    rfl

theorem cell23_1885354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_1885354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885354 prefixEnd_1885354 := by exact prefixLift 1885354
  have htrace : WordTrace (prefixWord ++ tailWord_1885354) baseStart_1885354 baseEnd_1885354 := by
    simpa [prefixWord, tailWord_1885354, baseEnd_1885354] using wordTrace_append hprefix tailTrace_1885354
  have hstable : (prefixWord ++ tailWord_1885354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885354).length < 2 ^ (prefixWord ++ tailWord_1885354).sum := by decide
  have hdescent : baseEnd_1885354 < baseStart_1885354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885370 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1885370 : Nat := 118140960795 + 1885370 * 2 ^ 59
def prefixEnd_1885370 : Nat := 4983230072969 + 3 ^ 40 * 1885370 * 2
def baseEnd_1885370 : Nat := 968101021567393714904347

theorem tailTrace_1885370 : CollatzResearch.WordTrace tailWord_1885370 prefixEnd_1885370 968101021567393714904347 := by
  unfold tailWord_1885370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191273294908490101433391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45843395453089306937155709 17191273294908490101433391)
  ·
    refine ⟨25786909942362735152150087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17191273294908490101433391 25786909942362735152150087)
    ·
      refine ⟨38680364913544102728225131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25786909942362735152150087 38680364913544102728225131)
      ·
        refine ⟨58020547370316154092337697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38680364913544102728225131 58020547370316154092337697)
        ·
          refine ⟨43515410527737115569253273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58020547370316154092337697 43515410527737115569253273)
          ·
            refine ⟨32636557895802836676939955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43515410527737115569253273 32636557895802836676939955)
            ·
              refine ⟨48954836843704255015409933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32636557895802836676939955 48954836843704255015409933)
              ·
                refine ⟨18358063816389095630778725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48954836843704255015409933 18358063816389095630778725)
                ·
                  refine ⟨3442136965572955430771011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18358063816389095630778725 3442136965572955430771011)
                  ·
                    refine ⟨5163205448359433146156517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3442136965572955430771011 5163205448359433146156517)
                    ·
                      refine ⟨968101021567393714904347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5163205448359433146156517 968101021567393714904347)
                      ·
                        rfl

theorem cell23_1885370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1885370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885370 prefixEnd_1885370 := by exact prefixLift 1885370
  have htrace : WordTrace (prefixWord ++ tailWord_1885370) baseStart_1885370 baseEnd_1885370 := by
    simpa [prefixWord, tailWord_1885370, baseEnd_1885370] using wordTrace_append hprefix tailTrace_1885370
  have hstable : (prefixWord ++ tailWord_1885370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885370).length < 2 ^ (prefixWord ++ tailWord_1885370).sum := by decide
  have hdescent : baseEnd_1885370 < baseStart_1885370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885382 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1885382 : Nat := 118140960795 + 1885382 * 2 ^ 59
def prefixEnd_1885382 : Nat := 4983230072969 + 3 ^ 40 * 1885382 * 2
def baseEnd_1885382 : Nat := 968107183335247667954293

theorem tailTrace_1885382 : CollatzResearch.WordTrace tailWord_1885382 prefixEnd_1885382 968107183335247667954293 := by
  unfold tailWord_1885382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148922839237202701724075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45843687237060324303446933 2148922839237202701724075)
  ·
    refine ⟨3223384258855804052586113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148922839237202701724075 3223384258855804052586113)
    ·
      refine ⟨2417538194141853039439585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3223384258855804052586113 2417538194141853039439585)
      ·
        refine ⟨1813153645606389779579689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2417538194141853039439585 1813153645606389779579689)
        ·
          refine ⟨1359865234204792334684767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1813153645606389779579689 1359865234204792334684767)
          ·
            refine ⟨2039797851307188502027151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359865234204792334684767 2039797851307188502027151)
            ·
              refine ⟨3059696776960782753040727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039797851307188502027151 3059696776960782753040727)
              ·
                refine ⟨4589545165441174129561091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059696776960782753040727 4589545165441174129561091)
                ·
                  refine ⟨6884317748161761194341637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589545165441174129561091 6884317748161761194341637)
                  ·
                    refine ⟨1290809577780330223939057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884317748161761194341637 1290809577780330223939057)
                    ·
                      refine ⟨968107183335247667954293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290809577780330223939057 968107183335247667954293)
                      ·
                        rfl

theorem cell23_1885382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1885382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885382 prefixEnd_1885382 := by exact prefixLift 1885382
  have htrace : WordTrace (prefixWord ++ tailWord_1885382) baseStart_1885382 baseEnd_1885382 := by
    simpa [prefixWord, tailWord_1885382, baseEnd_1885382] using wordTrace_append hprefix tailTrace_1885382
  have hstable : (prefixWord ++ tailWord_1885382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885382).length < 2 ^ (prefixWord ++ tailWord_1885382).sum := by decide
  have hdescent : baseEnd_1885382 < baseStart_1885382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885440 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_1885440 : Nat := 118140960795 + 1885440 * 2 ^ 59
def prefixEnd_1885440 : Nat := 4983230072969 + 3 ^ 40 * 1885440 * 2
def baseEnd_1885440 : Nat := 322712321737736147009675

theorem tailTrace_1885440 : CollatzResearch.WordTrace tailWord_1885440 prefixEnd_1885440 322712321737736147009675 := by
  unfold tailWord_1885440
  simp only [CollatzResearch.WordTrace]
  refine ⟨34383823144690181180390887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45845097526253574907187849 34383823144690181180390887)
  ·
    refine ⟨51575734717035271770586331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34383823144690181180390887 51575734717035271770586331)
    ·
      refine ⟨77363602075552907655879497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51575734717035271770586331 77363602075552907655879497)
      ·
        refine ⟨58022701556664680741909623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77363602075552907655879497 58022701556664680741909623)
        ·
          refine ⟨87034052334997021112864435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58022701556664680741909623 87034052334997021112864435)
          ·
            refine ⟨130551078502495531669296653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87034052334997021112864435 130551078502495531669296653)
            ·
              refine ⟨48956654438435824375986245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130551078502495531669296653 48956654438435824375986245)
              ·
                refine ⟨9179372707206717070497421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48956654438435824375986245 9179372707206717070497421)
                ·
                  refine ⟨3442264765202518901436533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9179372707206717070497421 3442264765202518901436533)
                  ·
                    refine ⟨322712321737736147009675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3442264765202518901436533 322712321737736147009675)
                    ·
                      rfl

theorem cell23_1885440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_1885440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885440 prefixEnd_1885440 := by exact prefixLift 1885440
  have htrace : WordTrace (prefixWord ++ tailWord_1885440) baseStart_1885440 baseEnd_1885440 := by
    simpa [prefixWord, tailWord_1885440, baseEnd_1885440] using wordTrace_append hprefix tailTrace_1885440
  have hstable : (prefixWord ++ tailWord_1885440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885440).length < 2 ^ (prefixWord ++ tailWord_1885440).sum := by decide
  have hdescent : baseEnd_1885440 < baseStart_1885440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885444 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 6]
def baseStart_1885444 : Nat := 118140960795 + 1885444 * 2 ^ 59
def prefixEnd_1885444 : Nat := 4983230072969 + 3 ^ 40 * 1885444 * 2
def baseEnd_1885444 : Nat := 107571002126202936153223

theorem tailTrace_1885444 : CollatzResearch.WordTrace tailWord_1885444 prefixEnd_1885444 107571002126202936153223 := by
  unfold tailWord_1885444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34383896090682935521963693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45845194787577247362618257 34383896090682935521963693)
  ·
    refine ⟨12893961034006100820736385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34383896090682935521963693 12893961034006100820736385)
    ·
      refine ⟨9670470775504575615552289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12893961034006100820736385 9670470775504575615552289)
      ·
        refine ⟨7252853081628431711664217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9670470775504575615552289 7252853081628431711664217)
        ·
          refine ⟨5439639811221323783748163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7252853081628431711664217 5439639811221323783748163)
          ·
            refine ⟨8159459716831985675622245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439639811221323783748163 8159459716831985675622245)
            ·
              refine ⟨1529898696905997314179171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8159459716831985675622245 1529898696905997314179171)
              ·
                refine ⟨2294848045358995971268757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529898696905997314179171 2294848045358995971268757)
                ·
                  refine ⟨107571002126202936153223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2294848045358995971268757 107571002126202936153223)
                  ·
                    rfl

theorem cell23_1885444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_1885444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885444 prefixEnd_1885444 := by exact prefixLift 1885444
  have htrace : WordTrace (prefixWord ++ tailWord_1885444) baseStart_1885444 baseEnd_1885444 := by
    simpa [prefixWord, tailWord_1885444, baseEnd_1885444] using wordTrace_append hprefix tailTrace_1885444
  have hstable : (prefixWord ++ tailWord_1885444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885444).length < 2 ^ (prefixWord ++ tailWord_1885444).sum := by decide
  have hdescent : baseEnd_1885444 < baseStart_1885444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885458 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1885458 : Nat := 118140960795 + 1885458 * 2 ^ 59
def prefixEnd_1885458 : Nat := 4983230072969 + 3 ^ 40 * 1885458 * 2
def baseEnd_1885458 : Nat := 968146207864989370603943

theorem tailTrace_1885458 : CollatzResearch.WordTrace tailWord_1885458 prefixEnd_1885458 968146207864989370603943 := by
  unfold tailWord_1885458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17192075700828787858734257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45845535202210100956624685 17192075700828787858734257)
  ·
    refine ⟨12894056775621590894050693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17192075700828787858734257 12894056775621590894050693)
    ·
      refine ⟨2417635645429048292634505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12894056775621590894050693 2417635645429048292634505)
      ·
        refine ⟨1813226734071786219475879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2417635645429048292634505 1813226734071786219475879)
        ·
          refine ⟨2719840101107679329213819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813226734071786219475879 2719840101107679329213819)
          ·
            refine ⟨4079760151661518993820729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719840101107679329213819 4079760151661518993820729)
            ·
              refine ⟨3059820113746139245365547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079760151661518993820729 3059820113746139245365547)
              ·
                refine ⟨4589730170619208868048321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059820113746139245365547 4589730170619208868048321)
                ·
                  refine ⟨3442297627964406651036241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4589730170619208868048321 3442297627964406651036241)
                  ·
                    refine ⟨2581723220973304988277181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3442297627964406651036241 2581723220973304988277181)
                    ·
                      refine ⟨968146207864989370603943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2581723220973304988277181 968146207864989370603943)
                      ·
                        rfl

theorem cell23_1885458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1885458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885458 prefixEnd_1885458 := by exact prefixLift 1885458
  have htrace : WordTrace (prefixWord ++ tailWord_1885458) baseStart_1885458 baseEnd_1885458 := by
    simpa [prefixWord, tailWord_1885458, baseEnd_1885458] using wordTrace_append hprefix tailTrace_1885458
  have hstable : (prefixWord ++ tailWord_1885458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885458).length < 2 ^ (prefixWord ++ tailWord_1885458).sum := by decide
  have hdescent : baseEnd_1885458 < baseStart_1885458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885464 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_1885464 : Nat := 118140960795 + 1885464 * 2 ^ 59
def prefixEnd_1885464 : Nat := 4983230072969 + 3 ^ 40 * 1885464 * 2
def baseEnd_1885464 : Nat := 968149288748916347128915

theorem tailTrace_1885464 : CollatzResearch.WordTrace tailWord_1885464 prefixEnd_1885464 968149288748916347128915 := by
  unfold tailWord_1885464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34384260820646707229827723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45845681094195609639770297 34384260820646707229827723)
  ·
    refine ⟨51576391230970060844741585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34384260820646707229827723 51576391230970060844741585)
    ·
      refine ⟨38682293423227545633556189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51576391230970060844741585 38682293423227545633556189)
      ·
        refine ⟨14505860033710329612583571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38682293423227545633556189 14505860033710329612583571)
        ·
          refine ⟨21758790050565494418875357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14505860033710329612583571 21758790050565494418875357)
          ·
            refine ⟨8159546268962060407078259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21758790050565494418875357 8159546268962060407078259)
            ·
              refine ⟨12239319403443090610617389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159546268962060407078259 12239319403443090610617389)
              ·
                refine ⟨4589744776291158978981521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12239319403443090610617389 4589744776291158978981521)
                ·
                  refine ⟨3442308582218369234236141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4589744776291158978981521 3442308582218369234236141)
                  ·
                    refine ⟨1290865718331888462838553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442308582218369234236141 1290865718331888462838553)
                    ·
                      refine ⟨968149288748916347128915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290865718331888462838553 968149288748916347128915)
                      ·
                        rfl

theorem cell23_1885464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_1885464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885464 prefixEnd_1885464 := by exact prefixLift 1885464
  have htrace : WordTrace (prefixWord ++ tailWord_1885464) baseStart_1885464 baseEnd_1885464 := by
    simpa [prefixWord, tailWord_1885464, baseEnd_1885464] using wordTrace_append hprefix tailTrace_1885464
  have hstable : (prefixWord ++ tailWord_1885464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885464).length < 2 ^ (prefixWord ++ tailWord_1885464).sum := by decide
  have hdescent : baseEnd_1885464 < baseStart_1885464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885511 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_1885511 : Nat := 118140960795 + 1885511 * 2 ^ 59
def prefixEnd_1885511 : Nat := 4983230072969 + 3 ^ 40 * 1885511 * 2
def baseEnd_1885511 : Nat := 968173422339677663241199

theorem tailTrace_1885511 : CollatzResearch.WordTrace tailWord_1885511 prefixEnd_1885511 968173422339677663241199 := by
  unfold tailWord_1885511
  simp only [CollatzResearch.WordTrace]
  refine ⟨68770235872123141486616387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45846823914748760991077591 68770235872123141486616387)
  ·
    refine ⟨103155353808184712229924581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68770235872123141486616387 103155353808184712229924581)
    ·
      refine ⟨19341628839034633543110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103155353808184712229924581 19341628839034633543110859)
      ·
        refine ⟨29012443258551950314666289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19341628839034633543110859 29012443258551950314666289)
        ·
          refine ⟨21759332443913962735999717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29012443258551950314666289 21759332443913962735999717)
          ·
            refine ⟨4079874833233868012999947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21759332443913962735999717 4079874833233868012999947)
            ·
              refine ⟨6119812249850802019499921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079874833233868012999947 6119812249850802019499921)
              ·
                refine ⟨4589859187388101514624941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119812249850802019499921 4589859187388101514624941)
                ·
                  refine ⟨1721197195270538067984353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4589859187388101514624941 1721197195270538067984353)
                  ·
                    refine ⟨1290897896452903550988265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721197195270538067984353 1290897896452903550988265)
                    ·
                      refine ⟨968173422339677663241199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290897896452903550988265 968173422339677663241199)
                      ·
                        rfl

theorem cell23_1885511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_1885511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885511 prefixEnd_1885511 := by exact prefixLift 1885511
  have htrace : WordTrace (prefixWord ++ tailWord_1885511) baseStart_1885511 baseEnd_1885511 := by
    simpa [prefixWord, tailWord_1885511, baseEnd_1885511] using wordTrace_append hprefix tailTrace_1885511
  have hstable : (prefixWord ++ tailWord_1885511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885511).length < 2 ^ (prefixWord ++ tailWord_1885511).sum := by decide
  have hdescent : baseEnd_1885511 < baseStart_1885511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885528 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 1, 2, 2]
def baseStart_1885528 : Nat := 118140960795 + 1885528 * 2 ^ 59
def prefixEnd_1885528 : Nat := 4983230072969 + 3 ^ 40 * 1885528 * 2
def baseEnd_1885528 : Nat := 968182151510804096728621

theorem tailTrace_1885528 : CollatzResearch.WordTrace tailWord_1885528 prefixEnd_1885528 968182151510804096728621 := by
  unfold tailWord_1885528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385427956530776694992619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45847237275374368926656825 34385427956530776694992619)
  ·
    refine ⟨51578141934796165042488929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34385427956530776694992619 51578141934796165042488929)
    ·
      refine ⟨38683606451097123781866697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51578141934796165042488929 38683606451097123781866697)
      ·
        refine ⟨29012704838322842836400023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38683606451097123781866697 29012704838322842836400023)
        ·
          refine ⟨43519057257484264254600035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29012704838322842836400023 43519057257484264254600035)
          ·
            refine ⟨65278585886226396381900053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43519057257484264254600035 65278585886226396381900053)
            ·
              refine ⟨3059933713416862330401565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65278585886226396381900053 3059933713416862330401565)
              ·
                refine ⟨1147475142531323373900587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059933713416862330401565 1147475142531323373900587)
                ·
                  refine ⟨1721212713796985060850881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147475142531323373900587 1721212713796985060850881)
                  ·
                    refine ⟨1290909535347738795638161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721212713796985060850881 1290909535347738795638161)
                    ·
                      refine ⟨968182151510804096728621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290909535347738795638161 968182151510804096728621)
                      ·
                        rfl

theorem cell23_1885528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_1885528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885528 prefixEnd_1885528 := by exact prefixLift 1885528
  have htrace : WordTrace (prefixWord ++ tailWord_1885528) baseStart_1885528 baseEnd_1885528 := by
    simpa [prefixWord, tailWord_1885528, baseEnd_1885528] using wordTrace_append hprefix tailTrace_1885528
  have hstable : (prefixWord ++ tailWord_1885528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885528).length < 2 ^ (prefixWord ++ tailWord_1885528).sum := by decide
  have hdescent : baseEnd_1885528 < baseStart_1885528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885571 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 1, 3, 2]
def baseStart_1885571 : Nat := 118140960795 + 1885571 * 2 ^ 59
def prefixEnd_1885571 : Nat := 4983230072969 + 3 ^ 40 * 1885571 * 2
def baseEnd_1885571 : Nat := 968204231178947428490923

theorem tailTrace_1885571 : CollatzResearch.WordTrace tailWord_1885571 prefixEnd_1885571 968204231178947428490923 := by
  unfold tailWord_1885571
  simp only [CollatzResearch.WordTrace]
  refine ⟨68772424251905771733800567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45848282834603847822533711 68772424251905771733800567)
  ·
    refine ⟨103158636377858657600700851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68772424251905771733800567 103158636377858657600700851)
    ·
      refine ⟨154737954566787986401051277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103158636377858657600700851 154737954566787986401051277)
      ·
        refine ⟨58026732962545494900394229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154737954566787986401051277 58026732962545494900394229)
        ·
          refine ⟨5440006215238640146911959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58026732962545494900394229 5440006215238640146911959)
          ·
            refine ⟨8160009322857960220367939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440006215238640146911959 8160009322857960220367939)
            ·
              refine ⟨12240013984286940330551909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160009322857960220367939 12240013984286940330551909)
              ·
                refine ⟨2295002622053801311978483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12240013984286940330551909 2295002622053801311978483)
                ·
                  refine ⟨3442503933080701967967725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295002622053801311978483 3442503933080701967967725)
                  ·
                    refine ⟨1290938974905263237987897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442503933080701967967725 1290938974905263237987897)
                    ·
                      refine ⟨968204231178947428490923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290938974905263237987897 968204231178947428490923)
                      ·
                        rfl

theorem cell23_1885571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_1885571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885571 prefixEnd_1885571 := by exact prefixLift 1885571
  have htrace : WordTrace (prefixWord ++ tailWord_1885571) baseStart_1885571 baseEnd_1885571 := by
    simpa [prefixWord, tailWord_1885571, baseEnd_1885571] using wordTrace_append hprefix tailTrace_1885571
  have hstable : (prefixWord ++ tailWord_1885571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885571).length < 2 ^ (prefixWord ++ tailWord_1885571).sum := by decide
  have hdescent : baseEnd_1885571 < baseStart_1885571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885588 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1885588 : Nat := 118140960795 + 1885588 * 2 ^ 59
def prefixEnd_1885588 : Nat := 4983230072969 + 3 ^ 40 * 1885588 * 2
def baseEnd_1885588 : Nat := 968212960350073861978345

theorem tailTrace_1885588 : CollatzResearch.WordTrace tailWord_1885588 prefixEnd_1885588 968212960350073861978345 := by
  unfold tailWord_1885588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386522146422091818584709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45848696195229455758112945 34386522146422091818584709)
  ·
    refine ⟨6447472902454142215984633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34386522146422091818584709 6447472902454142215984633)
    ·
      refine ⟨4835604676840606661988475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6447472902454142215984633 4835604676840606661988475)
      ·
        refine ⟨7253407015260909992982713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835604676840606661988475 7253407015260909992982713)
        ·
          refine ⟨5440055261445682494737035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7253407015260909992982713 5440055261445682494737035)
          ·
            refine ⟨8160082892168523742105553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440055261445682494737035 8160082892168523742105553)
            ·
              refine ⟨6120062169126392806579165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8160082892168523742105553 6120062169126392806579165)
              ·
                refine ⟨2295023313422397302467187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6120062169126392806579165 2295023313422397302467187)
                ·
                  refine ⟨3442534970133595953700781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295023313422397302467187 3442534970133595953700781)
                  ·
                    refine ⟨1290950613800098482637793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3442534970133595953700781 1290950613800098482637793)
                    ·
                      refine ⟨968212960350073861978345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1290950613800098482637793 968212960350073861978345)
                      ·
                        rfl

theorem cell23_1885588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1885588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885588 prefixEnd_1885588 := by exact prefixLift 1885588
  have htrace : WordTrace (prefixWord ++ tailWord_1885588) baseStart_1885588 baseEnd_1885588 := by
    simpa [prefixWord, tailWord_1885588, baseEnd_1885588] using wordTrace_append hprefix tailTrace_1885588
  have hstable : (prefixWord ++ tailWord_1885588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885588).length < 2 ^ (prefixWord ++ tailWord_1885588).sum := by decide
  have hdescent : baseEnd_1885588 < baseStart_1885588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885647 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_1885647 : Nat := 118140960795 + 1885647 * 2 ^ 59
def prefixEnd_1885647 : Nat := 4983230072969 + 3 ^ 40 * 1885647 * 2
def baseEnd_1885647 : Nat := 968243255708689131140573

theorem tailTrace_1885647 : CollatzResearch.WordTrace tailWord_1885647 prefixEnd_1885647 968243255708689131140573 := by
  unfold tailWord_1885647
  simp only [CollatzResearch.WordTrace]
  refine ⟨68775196199630436713567195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45850130799753624475711463 68775196199630436713567195)
  ·
    refine ⟨103162794299445655070350793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68775196199630436713567195 103162794299445655070350793)
    ·
      refine ⟨77372095724584241302763095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103162794299445655070350793 77372095724584241302763095)
      ·
        refine ⟨116058143586876361954144643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77372095724584241302763095 116058143586876361954144643)
        ·
          refine ⟨174087215380314542931216965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116058143586876361954144643 174087215380314542931216965)
          ·
            refine ⟨32641352883808976799603181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174087215380314542931216965 32641352883808976799603181)
            ·
              refine ⟨12240507331428366299851193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32641352883808976799603181 12240507331428366299851193)
              ·
                refine ⟨9180380498571274724888395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12240507331428366299851193 9180380498571274724888395)
                ·
                  refine ⟨13770570747856912087332593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180380498571274724888395 13770570747856912087332593)
                  ·
                    refine ⟨10327928060892684065499445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13770570747856912087332593 10327928060892684065499445)
                    ·
                      refine ⟨968243255708689131140573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10327928060892684065499445 968243255708689131140573)
                      ·
                        rfl

theorem cell23_1885647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_1885647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885647 prefixEnd_1885647 := by exact prefixLift 1885647
  have htrace : WordTrace (prefixWord ++ tailWord_1885647) baseStart_1885647 baseEnd_1885647 := by
    simpa [prefixWord, tailWord_1885647, baseEnd_1885647] using wordTrace_append hprefix tailTrace_1885647
  have hstable : (prefixWord ++ tailWord_1885647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885647).length < 2 ^ (prefixWord ++ tailWord_1885647).sum := by decide
  have hdescent : baseEnd_1885647 < baseStart_1885647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885658 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_1885658 : Nat := 118140960795 + 1885658 * 2 ^ 59
def prefixEnd_1885658 : Nat := 4983230072969 + 3 ^ 40 * 1885658 * 2
def baseEnd_1885658 : Nat := 107583211555098732011447

theorem tailTrace_1885658 : CollatzResearch.WordTrace tailWord_1885658 prefixEnd_1885658 107583211555098732011447 := by
  unfold tailWord_1885658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193899350647646398054407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45850398268393723728145085 17193899350647646398054407)
  ·
    refine ⟨25790849025971469597081611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17193899350647646398054407 25790849025971469597081611)
    ·
      refine ⟨38686273538957204395622417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25790849025971469597081611 38686273538957204395622417)
      ·
        refine ⟨29014705154217903296716813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38686273538957204395622417 29014705154217903296716813)
        ·
          refine ⟨10880514432831713736268805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29014705154217903296716813 10880514432831713736268805)
          ·
            refine ⟨2040096456155946325550401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10880514432831713736268805 2040096456155946325550401)
            ·
              refine ⟨1530072342116959744162801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040096456155946325550401 1530072342116959744162801)
              ·
                refine ⟨1147554256587719808122101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530072342116959744162801 1147554256587719808122101)
                ·
                  refine ⟨107583211555098732011447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147554256587719808122101 107583211555098732011447)
                  ·
                    rfl

theorem cell23_1885658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_1885658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885658 prefixEnd_1885658 := by exact prefixLift 1885658
  have htrace : WordTrace (prefixWord ++ tailWord_1885658) baseStart_1885658 baseEnd_1885658 := by
    simpa [prefixWord, tailWord_1885658, baseEnd_1885658] using wordTrace_append hprefix tailTrace_1885658
  have hstable : (prefixWord ++ tailWord_1885658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885658).length < 2 ^ (prefixWord ++ tailWord_1885658).sum := by decide
  have hdescent : baseEnd_1885658 < baseStart_1885658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885661 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1885661 : Nat := 118140960795 + 1885661 * 2 ^ 59
def prefixEnd_1885661 : Nat := 4983230072969 + 3 ^ 40 * 1885661 * 2
def baseEnd_1885661 : Nat := 968250444437852076365509

theorem tailTrace_1885661 : CollatzResearch.WordTrace tailWord_1885661 prefixEnd_1885661 968250444437852076365509 := by
  unfold tailWord_1885661
  simp only [CollatzResearch.WordTrace]
  refine ⟨68775706821579717104576837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45850471214386478069717891 68775706821579717104576837)
  ·
    refine ⟨12895445029046196957108157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68775706821579717104576837 12895445029046196957108157)
    ·
      refine ⟨4835791885892323858915559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12895445029046196957108157 4835791885892323858915559)
      ·
        refine ⟨7253687828838485788373339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835791885892323858915559 7253687828838485788373339)
        ·
          refine ⟨10880531743257728682560009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253687828838485788373339 10880531743257728682560009)
          ·
            refine ⟨8160398807443296511920007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10880531743257728682560009 8160398807443296511920007)
            ·
              refine ⟨12240598211164944767880011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160398807443296511920007 12240598211164944767880011)
              ·
                refine ⟨18360897316747417151820017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240598211164944767880011 18360897316747417151820017)
                ·
                  refine ⟨13770672987560562863865013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18360897316747417151820017 13770672987560562863865013)
                  ·
                    refine ⟨1291000592583802768487345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13770672987560562863865013 1291000592583802768487345)
                    ·
                      refine ⟨968250444437852076365509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291000592583802768487345 968250444437852076365509)
                      ·
                        rfl

theorem cell23_1885661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1885661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885661 prefixEnd_1885661 := by exact prefixLift 1885661
  have htrace : WordTrace (prefixWord ++ tailWord_1885661) baseStart_1885661 baseEnd_1885661 := by
    simpa [prefixWord, tailWord_1885661, baseEnd_1885661] using wordTrace_append hprefix tailTrace_1885661
  have hstable : (prefixWord ++ tailWord_1885661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885661).length < 2 ^ (prefixWord ++ tailWord_1885661).sum := by decide
  have hdescent : baseEnd_1885661 < baseStart_1885661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885687 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1885687 : Nat := 118140960795 + 1885687 * 2 ^ 59
def prefixEnd_1885687 : Nat := 4983230072969 + 3 ^ 40 * 1885687 * 2
def baseEnd_1885687 : Nat := 968263794934868974640389

theorem tailTrace_1885687 : CollatzResearch.WordTrace tailWord_1885687 prefixEnd_1885687 968263794934868974640389 := by
  unfold tailWord_1885687
  simp only [CollatzResearch.WordTrace]
  refine ⟨68776655119485523545023315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45851103412990349030015543 68776655119485523545023315)
  ·
    refine ⟨103164982679228285317534973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68776655119485523545023315 103164982679228285317534973)
    ·
      refine ⟨38686868504710606994075615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103164982679228285317534973 38686868504710606994075615)
      ·
        refine ⟨58030302757065910491113423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38686868504710606994075615 58030302757065910491113423)
        ·
          refine ⟨87045454135598865736670135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58030302757065910491113423 87045454135598865736670135)
          ·
            refine ⟨130568181203398298605005203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87045454135598865736670135 130568181203398298605005203)
            ·
              refine ⟨195852271805097447907507805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130568181203398298605005203 195852271805097447907507805)
              ·
                refine ⟨73444601926911542965315427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195852271805097447907507805 73444601926911542965315427)
                ·
                  refine ⟨110166902890367314447973141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73444601926911542965315427 110166902890367314447973141)
                  ·
                    refine ⟨5164073572985967864748741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110166902890367314447973141 5164073572985967864748741)
                    ·
                      refine ⟨968263794934868974640389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5164073572985967864748741 968263794934868974640389)
                      ·
                        rfl

theorem cell23_1885687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1885687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885687 prefixEnd_1885687 := by exact prefixLift 1885687
  have htrace : WordTrace (prefixWord ++ tailWord_1885687) baseStart_1885687 baseEnd_1885687 := by
    simpa [prefixWord, tailWord_1885687, baseEnd_1885687] using wordTrace_append hprefix tailTrace_1885687
  have hstable : (prefixWord ++ tailWord_1885687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885687).length < 2 ^ (prefixWord ++ tailWord_1885687).sum := by decide
  have hdescent : baseEnd_1885687 < baseStart_1885687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885751 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_1885751 : Nat := 118140960795 + 1885751 * 2 ^ 59
def prefixEnd_1885751 : Nat := 4983230072969 + 3 ^ 40 * 1885751 * 2
def baseEnd_1885751 : Nat := 968296657696756724240095

theorem tailTrace_1885751 : CollatzResearch.WordTrace tailWord_1885751 prefixEnd_1885751 968296657696756724240095 := by
  unfold tailWord_1885751
  simp only [CollatzResearch.WordTrace]
  refine ⟨68778989391253662475353107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45852659594169108316902071 68778989391253662475353107)
  ·
    refine ⟨103168484086880493713029661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68778989391253662475353107 103168484086880493713029661)
    ·
      refine ⟨38688181532580185142386123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103168484086880493713029661 38688181532580185142386123)
      ·
        refine ⟨58032272298870277713579185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38688181532580185142386123 58032272298870277713579185)
        ·
          refine ⟨43524204224152708285184389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58032272298870277713579185 43524204224152708285184389)
          ·
            refine ⟨8160788292028632803472073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43524204224152708285184389 8160788292028632803472073)
            ·
              refine ⟨6120591219021474602604055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8160788292028632803472073 6120591219021474602604055)
              ·
                refine ⟨9180886828532211903906083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120591219021474602604055 9180886828532211903906083)
                ·
                  refine ⟨13771330242798317855859125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180886828532211903906083 13771330242798317855859125)
                  ·
                    refine ⟨1291062210262342298986793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13771330242798317855859125 1291062210262342298986793)
                    ·
                      refine ⟨968296657696756724240095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291062210262342298986793 968296657696756724240095)
                      ·
                        rfl

theorem cell23_1885751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_1885751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885751 prefixEnd_1885751 := by exact prefixLift 1885751
  have htrace : WordTrace (prefixWord ++ tailWord_1885751) baseStart_1885751 baseEnd_1885751 := by
    simpa [prefixWord, tailWord_1885751, baseEnd_1885751] using wordTrace_append hprefix tailTrace_1885751
  have hstable : (prefixWord ++ tailWord_1885751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885751).length < 2 ^ (prefixWord ++ tailWord_1885751).sum := by decide
  have hdescent : baseEnd_1885751 < baseStart_1885751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885761 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1885761 : Nat := 118140960795 + 1885761 * 2 ^ 59
def prefixEnd_1885761 : Nat := 4983230072969 + 3 ^ 40 * 1885761 * 2
def baseEnd_1885761 : Nat := 322767264167767228371683

theorem tailTrace_1885761 : CollatzResearch.WordTrace tailWord_1885761 prefixEnd_1885761 322767264167767228371683 := by
  unfold tailWord_1885761
  simp only [CollatzResearch.WordTrace]
  refine ⟨68779354121217434183217137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45852902747478289455478091 68779354121217434183217137)
  ·
    refine ⟨51584515590913075637412853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68779354121217434183217137 51584515590913075637412853)
    ·
      refine ⟨4836048336648100841007455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51584515590913075637412853 4836048336648100841007455)
      ·
        refine ⟨7254072504972151261511183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836048336648100841007455 7254072504972151261511183)
        ·
          refine ⟨10881108757458226892266775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254072504972151261511183 10881108757458226892266775)
          ·
            refine ⟨16321663136187340338400163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10881108757458226892266775 16321663136187340338400163)
            ·
              refine ⟨24482494704281010507600245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16321663136187340338400163 24482494704281010507600245)
              ·
                refine ⟨2295233878526344735087523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24482494704281010507600245 2295233878526344735087523)
                ·
                  refine ⟨3442850817789517102631285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295233878526344735087523 3442850817789517102631285)
                  ·
                    refine ⟨322767264167767228371683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3442850817789517102631285 322767264167767228371683)
                    ·
                      rfl

theorem cell23_1885761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1885761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885761 prefixEnd_1885761 := by exact prefixLift 1885761
  have htrace : WordTrace (prefixWord ++ tailWord_1885761) baseStart_1885761 baseEnd_1885761 := by
    simpa [prefixWord, tailWord_1885761, baseEnd_1885761] using wordTrace_append hprefix tailTrace_1885761
  have hstable : (prefixWord ++ tailWord_1885761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885761).length < 2 ^ (prefixWord ++ tailWord_1885761).sum := by decide
  have hdescent : baseEnd_1885761 < baseStart_1885761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885784 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1885784 : Nat := 118140960795 + 1885784 * 2 ^ 59
def prefixEnd_1885784 : Nat := 4983230072969 + 3 ^ 40 * 1885784 * 2
def baseEnd_1885784 : Nat := 968313602558355095127443

theorem tailTrace_1885784 : CollatzResearch.WordTrace tailWord_1885784 prefixEnd_1885784 968313602558355095127443 := by
  unfold tailWord_1885784
  simp only [CollatzResearch.WordTrace]
  refine ⟨34390096500067054555652203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45853462000089406074202937 34390096500067054555652203)
  ·
    refine ⟨51585144750100581833478305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34390096500067054555652203 51585144750100581833478305)
    ·
      refine ⟨38688858562575436375108729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51585144750100581833478305 38688858562575436375108729)
      ·
        refine ⟨29016643921931577281331547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38688858562575436375108729 29016643921931577281331547)
        ·
          refine ⟨43524965882897365921997321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29016643921931577281331547 43524965882897365921997321)
          ·
            refine ⟨32643724412173024441497991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43524965882897365921997321 32643724412173024441497991)
            ·
              refine ⟨48965586618259536662246987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32643724412173024441497991 48965586618259536662246987)
              ·
                refine ⟨73448379927389304993370481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48965586618259536662246987 73448379927389304993370481)
                ·
                  refine ⟨55086284945541978745027861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73448379927389304993370481 55086284945541978745027861)
                  ·
                    refine ⟨2582169606822280253673181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55086284945541978745027861 2582169606822280253673181)
                    ·
                      refine ⟨968313602558355095127443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2582169606822280253673181 968313602558355095127443)
                      ·
                        rfl

theorem cell23_1885784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1885784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885784 prefixEnd_1885784 := by exact prefixLift 1885784
  have htrace : WordTrace (prefixWord ++ tailWord_1885784) baseStart_1885784 baseEnd_1885784 := by
    simpa [prefixWord, tailWord_1885784, baseEnd_1885784] using wordTrace_append hprefix tailTrace_1885784
  have hstable : (prefixWord ++ tailWord_1885784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885784).length < 2 ^ (prefixWord ++ tailWord_1885784).sum := by decide
  have hdescent : baseEnd_1885784 < baseStart_1885784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885815 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 1, 2, 2]
def baseStart_1885815 : Nat := 118140960795 + 1885815 * 2 ^ 59
def prefixEnd_1885815 : Nat := 4983230072969 + 3 ^ 40 * 1885815 * 2
def baseEnd_1885815 : Nat := 968329520458644473839801

theorem tailTrace_1885815 : CollatzResearch.WordTrace tailWord_1885815 prefixEnd_1885815 968329520458644473839801 := by
  unfold tailWord_1885815
  simp only [CollatzResearch.WordTrace]
  refine ⟨68781323663021801405682899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45854215775347867603788599 68781323663021801405682899)
  ·
    refine ⟨103171985494532702108524349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68781323663021801405682899 103171985494532702108524349)
    ·
      refine ⟨38689494560449763290696631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103171985494532702108524349 38689494560449763290696631)
      ·
        refine ⟨58034241840674644936044947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38689494560449763290696631 58034241840674644936044947)
        ·
          refine ⟨87051362761011967404067421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58034241840674644936044947 87051362761011967404067421)
          ·
            refine ⟨32644261035379487776525283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87051362761011967404067421 32644261035379487776525283)
            ·
              refine ⟨48966391553069231664787925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32644261035379487776525283 48966391553069231664787925)
              ·
                refine ⟨1147649802025060117143467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48966391553069231664787925 1147649802025060117143467)
                ·
                  refine ⟨1721474703037590175715201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147649802025060117143467 1721474703037590175715201)
                  ·
                    refine ⟨1291106027278192631786401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721474703037590175715201 1291106027278192631786401)
                    ·
                      refine ⟨968329520458644473839801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291106027278192631786401 968329520458644473839801)
                      ·
                        rfl

theorem cell23_1885815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_1885815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885815 prefixEnd_1885815 := by exact prefixLift 1885815
  have htrace : WordTrace (prefixWord ++ tailWord_1885815) baseStart_1885815 baseEnd_1885815 := by
    simpa [prefixWord, tailWord_1885815, baseEnd_1885815] using wordTrace_append hprefix tailTrace_1885815
  have hstable : (prefixWord ++ tailWord_1885815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885815).length < 2 ^ (prefixWord ++ tailWord_1885815).sum := by decide
  have hdescent : baseEnd_1885815 < baseStart_1885815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885848 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1885848 : Nat := 118140960795 + 1885848 * 2 ^ 59
def prefixEnd_1885848 : Nat := 4983230072969 + 3 ^ 40 * 1885848 * 2
def baseEnd_1885848 : Nat := 968346465320242844727149

theorem tailTrace_1885848 : CollatzResearch.WordTrace tailWord_1885848 prefixEnd_1885848 968346465320242844727149 := by
  unfold tailWord_1885848
  simp only [CollatzResearch.WordTrace]
  refine ⟨34391263635951124020817099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45855018181268165361089465 34391263635951124020817099)
  ·
    refine ⟨51586895453926686031225649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34391263635951124020817099 51586895453926686031225649)
    ·
      refine ⟨38690171590445014523419237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51586895453926686031225649 38690171590445014523419237)
      ·
        refine ⟨7254407173208440223141107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38690171590445014523419237 7254407173208440223141107)
        ·
          refine ⟨10881610759812660334711661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254407173208440223141107 10881610759812660334711661)
          ·
            refine ⟨4080604034929747625516873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10881610759812660334711661 4080604034929747625516873)
            ·
              refine ⟨3060453026197310719137655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4080604034929747625516873 3060453026197310719137655)
              ·
                refine ⟨4590679539295966078706483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060453026197310719137655 4590679539295966078706483)
                ·
                  refine ⟨6886019308943949118059725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590679539295966078706483 6886019308943949118059725)
                  ·
                    refine ⟨2582257240853980919272397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6886019308943949118059725 2582257240853980919272397)
                    ·
                      refine ⟨968346465320242844727149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2582257240853980919272397 968346465320242844727149)
                      ·
                        rfl

theorem cell23_1885848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1885848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885848 prefixEnd_1885848 := by exact prefixLift 1885848
  have htrace : WordTrace (prefixWord ++ tailWord_1885848) baseStart_1885848 baseEnd_1885848 := by
    simpa [prefixWord, tailWord_1885848, baseEnd_1885848] using wordTrace_append hprefix tailTrace_1885848
  have hstable : (prefixWord ++ tailWord_1885848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885848).length < 2 ^ (prefixWord ++ tailWord_1885848).sum := by decide
  have hdescent : baseEnd_1885848 < baseStart_1885848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885905 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_1885905 : Nat := 118140960795 + 1885905 * 2 ^ 59
def prefixEnd_1885905 : Nat := 4983230072969 + 3 ^ 40 * 1885905 * 2
def baseEnd_1885905 : Nat := 968375733717549121714387

theorem tailTrace_1885905 : CollatzResearch.WordTrace tailWord_1885905 prefixEnd_1885905 968375733717549121714387 := by
  unfold tailWord_1885905
  simp only [CollatzResearch.WordTrace]
  refine ⟨68784606232695746776459169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45856404155130497850972779 68784606232695746776459169)
  ·
    refine ⟨51588454674521810082344377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68784606232695746776459169 51588454674521810082344377)
    ·
      refine ⟨38691341005891357561758283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51588454674521810082344377 38691341005891357561758283)
      ·
        refine ⟨58037011508837036342637425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38691341005891357561758283 58037011508837036342637425)
        ·
          refine ⟨43527758631627777256978069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58037011508837036342637425 43527758631627777256978069)
          ·
            refine ⟨2040363685857552058920847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43527758631627777256978069 2040363685857552058920847)
            ·
              refine ⟨3060545528786328088381271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040363685857552058920847 3060545528786328088381271)
              ·
                refine ⟨4590818293179492132571907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060545528786328088381271 4590818293179492132571907)
                ·
                  refine ⟨6886227439769238198857861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590818293179492132571907 6886227439769238198857861)
                  ·
                    refine ⟨1291167644956732162285849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886227439769238198857861 1291167644956732162285849)
                    ·
                      refine ⟨968375733717549121714387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291167644956732162285849 968375733717549121714387)
                      ·
                        rfl

theorem cell23_1885905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_1885905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885905 prefixEnd_1885905 := by exact prefixLift 1885905
  have htrace : WordTrace (prefixWord ++ tailWord_1885905) baseStart_1885905 baseEnd_1885905 := by
    simpa [prefixWord, tailWord_1885905, baseEnd_1885905] using wordTrace_append hprefix tailTrace_1885905
  have hstable : (prefixWord ++ tailWord_1885905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885905).length < 2 ^ (prefixWord ++ tailWord_1885905).sum := by decide
  have hdescent : baseEnd_1885905 < baseStart_1885905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885948 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_1885948 : Nat := 118140960795 + 1885948 * 2 ^ 59
def prefixEnd_1885948 : Nat := 4983230072969 + 3 ^ 40 * 1885948 * 2
def baseEnd_1885948 : Nat := 968397813385692453476689

theorem tailTrace_1885948 : CollatzResearch.WordTrace tailWord_1885948 prefixEnd_1885948 968397813385692453476689 := by
  unfold tailWord_1885948
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393087285769982560137249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45857449714359976746849665 34393087285769982560137249)
  ·
    refine ⟨25794815464327486920102937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34393087285769982560137249 25794815464327486920102937)
    ·
      refine ⟨19346111598245615190077203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25794815464327486920102937 19346111598245615190077203)
      ·
        refine ⟨29019167397368422785115805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19346111598245615190077203 29019167397368422785115805)
        ·
          refine ⟨10882187774013158544418427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29019167397368422785115805 10882187774013158544418427)
          ·
            refine ⟨16323281661019737816627641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882187774013158544418427 16323281661019737816627641)
            ·
              refine ⟨12242461245764803362470731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16323281661019737816627641 12242461245764803362470731)
              ·
                refine ⟨18363691868647205043706097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12242461245764803362470731 18363691868647205043706097)
                ·
                  refine ⟨13772768901485403782779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18363691868647205043706097 13772768901485403782779573)
                  ·
                    refine ⟨1291197084514256604635585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13772768901485403782779573 1291197084514256604635585)
                    ·
                      refine ⟨968397813385692453476689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291197084514256604635585 968397813385692453476689)
                      ·
                        rfl

theorem cell23_1885948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_1885948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885948 prefixEnd_1885948 := by exact prefixLift 1885948
  have htrace : WordTrace (prefixWord ++ tailWord_1885948) baseStart_1885948 baseEnd_1885948 := by
    simpa [prefixWord, tailWord_1885948, baseEnd_1885948] using wordTrace_append hprefix tailTrace_1885948
  have hstable : (prefixWord ++ tailWord_1885948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885948).length < 2 ^ (prefixWord ++ tailWord_1885948).sum := by decide
  have hdescent : baseEnd_1885948 < baseStart_1885948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885961 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_1885961 : Nat := 118140960795 + 1885961 * 2 ^ 59
def prefixEnd_1885961 : Nat := 4983230072969 + 3 ^ 40 * 1885961 * 2
def baseEnd_1885961 : Nat := 968404488634200902614129

theorem tailTrace_1885961 : CollatzResearch.WordTrace tailWord_1885961 prefixEnd_1885961 968404488634200902614129 := by
  unfold tailWord_1885961
  simp only [CollatzResearch.WordTrace]
  refine ⟨68786648720492868340497737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45857765813661912226998491 68786648720492868340497737)
  ·
    refine ⟨51589986540369651255373303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68786648720492868340497737 51589986540369651255373303)
    ·
      refine ⟨77384979810554476883059955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51589986540369651255373303 77384979810554476883059955)
      ·
        refine ⟨116077469715831715324589933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77384979810554476883059955 116077469715831715324589933)
        ·
          refine ⟨43529051143436893246721225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116077469715831715324589933 43529051143436893246721225)
          ·
            refine ⟨32646788357577669935040919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43529051143436893246721225 32646788357577669935040919)
            ·
              refine ⟨48970182536366504902561379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32646788357577669935040919 48970182536366504902561379)
              ·
                refine ⟨73455273804549757353842069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48970182536366504902561379 73455273804549757353842069)
                ·
                  refine ⟨3443215959588269875961347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73455273804549757353842069 3443215959588269875961347)
                  ·
                    refine ⟨5164823939382404813942021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443215959588269875961347 5164823939382404813942021)
                    ·
                      refine ⟨968404488634200902614129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5164823939382404813942021 968404488634200902614129)
                      ·
                        rfl

theorem cell23_1885961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_1885961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885961 prefixEnd_1885961 := by exact prefixLift 1885961
  have htrace : WordTrace (prefixWord ++ tailWord_1885961) baseStart_1885961 baseEnd_1885961 := by
    simpa [prefixWord, tailWord_1885961, baseEnd_1885961] using wordTrace_append hprefix tailTrace_1885961
  have hstable : (prefixWord ++ tailWord_1885961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885961).length < 2 ^ (prefixWord ++ tailWord_1885961).sum := by decide
  have hdescent : baseEnd_1885961 < baseStart_1885961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885978 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1885978 : Nat := 118140960795 + 1885978 * 2 ^ 59
def prefixEnd_1885978 : Nat := 4983230072969 + 3 ^ 40 * 1885978 * 2
def baseEnd_1885978 : Nat := 968413217805327336101551

theorem tailTrace_1885978 : CollatzResearch.WordTrace tailWord_1885978 prefixEnd_1885978 968413217805327336101551 := by
  unfold tailWord_1885978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17196817190357820060966647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45858179174287520162577725 17196817190357820060966647)
  ·
    refine ⟨25795225785536730091449971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17196817190357820060966647 25795225785536730091449971)
    ·
      refine ⟨38692838678305095137174957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25795225785536730091449971 38692838678305095137174957)
      ·
        refine ⟨14509814504364410676440609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38692838678305095137174957 14509814504364410676440609)
        ·
          refine ⟨10882360878273308007330457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14509814504364410676440609 10882360878273308007330457)
          ·
            refine ⟨8161770658704981005497843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10882360878273308007330457 8161770658704981005497843)
            ·
              refine ⟨12242655988057471508246765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161770658704981005497843 12242655988057471508246765)
              ·
                refine ⟨4590995995521551815592537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12242655988057471508246765 4590995995521551815592537)
                ·
                  refine ⟨3443246996641163861694403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4590995995521551815592537 3443246996641163861694403)
                  ·
                    refine ⟨5164870494961745792541605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443246996641163861694403 5164870494961745792541605)
                    ·
                      refine ⟨968413217805327336101551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5164870494961745792541605 968413217805327336101551)
                      ·
                        rfl

theorem cell23_1885978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1885978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1885978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1885978 prefixEnd_1885978 := by exact prefixLift 1885978
  have htrace : WordTrace (prefixWord ++ tailWord_1885978) baseStart_1885978 baseEnd_1885978 := by
    simpa [prefixWord, tailWord_1885978, baseEnd_1885978] using wordTrace_append hprefix tailTrace_1885978
  have hstable : (prefixWord ++ tailWord_1885978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885978).length < 2 ^ (prefixWord ++ tailWord_1885978).sum := by decide
  have hdescent : baseEnd_1885978 < baseStart_1885978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886022 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1886022 : Nat := 118140960795 + 1886022 * 2 ^ 59
def prefixEnd_1886022 : Nat := 4983230072969 + 3 ^ 40 * 1886022 * 2
def baseEnd_1886022 : Nat := 322811936984708387983783

theorem tailTrace_1886022 : CollatzResearch.WordTrace tailWord_1886022 prefixEnd_1886022 322811936984708387983783 := by
  unfold tailWord_1886022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149652299164746117452135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45859249048847917172312213 2149652299164746117452135)
  ·
    refine ⟨3224478448747119176178203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149652299164746117452135 3224478448747119176178203)
    ·
      refine ⟨4836717673120678764267305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224478448747119176178203 4836717673120678764267305)
      ·
        refine ⟨3627538254840509073200479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4836717673120678764267305 3627538254840509073200479)
        ·
          refine ⟨5441307382260763609800719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627538254840509073200479 5441307382260763609800719)
          ·
            refine ⟨8161961073391145414701079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441307382260763609800719 8161961073391145414701079)
            ·
              refine ⟨12242941610086718122051619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161961073391145414701079 12242941610086718122051619)
              ·
                refine ⟨18364412415130077183077429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12242941610086718122051619 18364412415130077183077429)
                ·
                  refine ⟨1721663663918444735913509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18364412415130077183077429 1721663663918444735913509)
                  ·
                    refine ⟨322811936984708387983783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1721663663918444735913509 322811936984708387983783)
                    ·
                      rfl

theorem cell23_1886022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1886022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886022 prefixEnd_1886022 := by exact prefixLift 1886022
  have htrace : WordTrace (prefixWord ++ tailWord_1886022) baseStart_1886022 baseEnd_1886022 := by
    simpa [prefixWord, tailWord_1886022, baseEnd_1886022] using wordTrace_append hprefix tailTrace_1886022
  have hstable : (prefixWord ++ tailWord_1886022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886022).length < 2 ^ (prefixWord ++ tailWord_1886022).sum := by decide
  have hdescent : baseEnd_1886022 < baseStart_1886022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886052 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 6]
def baseStart_1886052 : Nat := 118140960795 + 1886052 * 2 ^ 59
def prefixEnd_1886052 : Nat := 4983230072969 + 3 ^ 40 * 1886052 * 2
def baseEnd_1886052 : Nat := 107605690597084449619579

theorem tailTrace_1886052 : CollatzResearch.WordTrace tailWord_1886052 prefixEnd_1886052 107605690597084449619579 := by
  unfold tailWord_1886052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34394983881581595441030205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45859978508775460588040273 34394983881581595441030205)
  ·
    refine ⟨12898118955593098290386327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34394983881581595441030205 12898118955593098290386327)
    ·
      refine ⟨19347178433389647435579491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12898118955593098290386327 19347178433389647435579491)
      ·
        refine ⟨29020767650084471153369237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19347178433389647435579491 29020767650084471153369237)
        ·
          refine ⟨1360348483597709585314183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29020767650084471153369237 1360348483597709585314183)
          ·
            refine ⟨2040522725396564377971275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360348483597709585314183 2040522725396564377971275)
            ·
              refine ⟨3060784088094846566956913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040522725396564377971275 3060784088094846566956913)
              ·
                refine ⟨2295588066071134925217685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060784088094846566956913 2295588066071134925217685)
                ·
                  refine ⟨107605690597084449619579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2295588066071134925217685 107605690597084449619579)
                  ·
                    rfl

theorem cell23_1886052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_1886052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886052 prefixEnd_1886052 := by exact prefixLift 1886052
  have htrace : WordTrace (prefixWord ++ tailWord_1886052) baseStart_1886052 baseEnd_1886052 := by
    simpa [prefixWord, tailWord_1886052, baseEnd_1886052] using wordTrace_append hprefix tailTrace_1886052
  have hstable : (prefixWord ++ tailWord_1886052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886052).length < 2 ^ (prefixWord ++ tailWord_1886052).sum := by decide
  have hdescent : baseEnd_1886052 < baseStart_1886052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886055 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_1886055 : Nat := 118140960795 + 1886055 * 2 ^ 59
def prefixEnd_1886055 : Nat := 4983230072969 + 3 ^ 40 * 1886055 * 2
def baseEnd_1886055 : Nat := 968452755815723534838697

theorem tailTrace_1886055 : CollatzResearch.WordTrace tailWord_1886055 prefixEnd_1886055 968452755815723534838697 := by
  unfold tailWord_1886055
  simp only [CollatzResearch.WordTrace]
  refine ⟨68790077182152322394419619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45860051454768214929613079 68790077182152322394419619)
  ·
    refine ⟨103185115773228483591629429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68790077182152322394419619 103185115773228483591629429)
    ·
      refine ⟨9673604603740170336715259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103185115773228483591629429 9673604603740170336715259)
      ·
        refine ⟨14510406905610255505072889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9673604603740170336715259 14510406905610255505072889)
        ·
          refine ⟨10882805179207691628804667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14510406905610255505072889 10882805179207691628804667)
          ·
            refine ⟨16324207768811537443207001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882805179207691628804667 16324207768811537443207001)
            ·
              refine ⟨12243155826608653082405251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16324207768811537443207001 12243155826608653082405251)
              ·
                refine ⟨18364733739912979623607877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243155826608653082405251 18364733739912979623607877)
                ·
                  refine ⟨3443387576233683679426477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18364733739912979623607877 3443387576233683679426477)
                  ·
                    refine ⟨1291270341087631379784929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3443387576233683679426477 1291270341087631379784929)
                    ·
                      refine ⟨968452755815723534838697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291270341087631379784929 968452755815723534838697)
                      ·
                        rfl

theorem cell23_1886055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_1886055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886055 prefixEnd_1886055 := by exact prefixLift 1886055
  have htrace : WordTrace (prefixWord ++ tailWord_1886055) baseStart_1886055 baseEnd_1886055 := by
    simpa [prefixWord, tailWord_1886055, baseEnd_1886055] using wordTrace_append hprefix tailTrace_1886055
  have hstable : (prefixWord ++ tailWord_1886055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886055).length < 2 ^ (prefixWord ++ tailWord_1886055).sum := by decide
  have hdescent : baseEnd_1886055 < baseStart_1886055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886062 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1886062 : Nat := 118140960795 + 1886062 * 2 ^ 59
def prefixEnd_1886062 : Nat := 4983230072969 + 3 ^ 40 * 1886062 * 2
def baseEnd_1886062 : Nat := 968456350180305007451165

theorem tailTrace_1886062 : CollatzResearch.WordTrace tailWord_1886062 prefixEnd_1886062 968456350180305007451165 := by
  unfold tailWord_1886062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598791561640870323740555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45860221662084641726616293 8598791561640870323740555)
  ·
    refine ⟨12898187342461305485610833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8598791561640870323740555 12898187342461305485610833)
    ·
      refine ⟨9673640506845979114208125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12898187342461305485610833 9673640506845979114208125)
      ·
        refine ⟨3627615190067242167828047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9673640506845979114208125 3627615190067242167828047)
        ·
          refine ⟨5441422785100863251742071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627615190067242167828047 5441422785100863251742071)
          ·
            refine ⟨8162134177651294877613107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441422785100863251742071 8162134177651294877613107)
            ·
              refine ⟨12243201266476942316419661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162134177651294877613107 12243201266476942316419661)
              ·
                refine ⟨4591200474928853368657373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12243201266476942316419661 4591200474928853368657373)
                ·
                  refine ⟨1721700178098320013246515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4591200474928853368657373 1721700178098320013246515)
                  ·
                    refine ⟨2582550267147480019869773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1721700178098320013246515 2582550267147480019869773)
                    ·
                      refine ⟨968456350180305007451165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2582550267147480019869773 968456350180305007451165)
                      ·
                        rfl

theorem cell23_1886062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1886062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886062 prefixEnd_1886062 := by exact prefixLift 1886062
  have htrace : WordTrace (prefixWord ++ tailWord_1886062) baseStart_1886062 baseEnd_1886062 := by
    simpa [prefixWord, tailWord_1886062, baseEnd_1886062] using wordTrace_append hprefix tailTrace_1886062
  have hstable : (prefixWord ++ tailWord_1886062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886062).length < 2 ^ (prefixWord ++ tailWord_1886062).sum := by decide
  have hdescent : baseEnd_1886062 < baseStart_1886062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886085 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_1886085 : Nat := 118140960795 + 1886085 * 2 ^ 59
def prefixEnd_1886085 : Nat := 4983230072969 + 3 ^ 40 * 1886085 * 2
def baseEnd_1886085 : Nat := 968468160235358417463559

theorem tailTrace_1886085 : CollatzResearch.WordTrace tailWord_1886085 prefixEnd_1886085 968468160235358417463559 := by
  unfold tailWord_1886085
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791171372043637518011709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45860780914695758345341139 68791171372043637518011709)
  ·
    refine ⟨25796689264516364069254391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68791171372043637518011709 25796689264516364069254391)
    ·
      refine ⟨38695033896774546103881587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25796689264516364069254391 38695033896774546103881587)
      ·
        refine ⟨58042550845161819155822381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38695033896774546103881587 58042550845161819155822381)
        ·
          refine ⟨21765956566935682183433393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58042550845161819155822381 21765956566935682183433393)
          ·
            refine ⟨16324467425201761637575045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21765956566935682183433393 16324467425201761637575045)
            ·
              refine ⟨3060837642225330307045321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16324467425201761637575045 3060837642225330307045321)
              ·
                refine ⟨2295628231668997730283991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060837642225330307045321 2295628231668997730283991)
                ·
                  refine ⟨3443442347503496595425987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295628231668997730283991 3443442347503496595425987)
                  ·
                    refine ⟨5165163521255244893138981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443442347503496595425987 5165163521255244893138981)
                    ·
                      refine ⟨968468160235358417463559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5165163521255244893138981 968468160235358417463559)
                      ·
                        rfl

theorem cell23_1886085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_1886085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886085 prefixEnd_1886085 := by exact prefixLift 1886085
  have htrace : WordTrace (prefixWord ++ tailWord_1886085) baseStart_1886085 baseEnd_1886085 := by
    simpa [prefixWord, tailWord_1886085, baseEnd_1886085] using wordTrace_append hprefix tailTrace_1886085
  have hstable : (prefixWord ++ tailWord_1886085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886085).length < 2 ^ (prefixWord ++ tailWord_1886085).sum := by decide
  have hdescent : baseEnd_1886085 < baseStart_1886085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886105 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_1886105 : Nat := 118140960795 + 1886105 * 2 ^ 59
def prefixEnd_1886105 : Nat := 4983230072969 + 3 ^ 40 * 1886105 * 2
def baseEnd_1886105 : Nat := 968478429848448339213467

theorem tailTrace_1886105 : CollatzResearch.WordTrace tailWord_1886105 prefixEnd_1886105 968478429848448339213467 := by
  unfold tailWord_1886105
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791900831971180933739769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45861267221314120622493179 68791900831971180933739769)
  ·
    refine ⟨51593925623978385700304827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68791900831971180933739769 51593925623978385700304827)
    ·
      refine ⟨77390888435967578550457241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51593925623978385700304827 77390888435967578550457241)
      ·
        refine ⟨58043166326975683912842931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77390888435967578550457241 58043166326975683912842931)
        ·
          refine ⟨87064749490463525869264397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58043166326975683912842931 87064749490463525869264397)
          ·
            refine ⟨32649281058923822200974149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87064749490463525869264397 32649281058923822200974149)
            ·
              refine ⟨6121740198548216662682653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32649281058923822200974149 6121740198548216662682653)
              ·
                refine ⟨2295652574455581248505995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6121740198548216662682653 2295652574455581248505995)
                ·
                  refine ⟨3443478861683371872758993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295652574455581248505995 3443478861683371872758993)
                  ·
                    refine ⟨2582609146262528904569245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3443478861683371872758993 2582609146262528904569245)
                    ·
                      refine ⟨968478429848448339213467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2582609146262528904569245 968478429848448339213467)
                      ·
                        rfl

theorem cell23_1886105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_1886105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886105 prefixEnd_1886105 := by exact prefixLift 1886105
  have htrace : WordTrace (prefixWord ++ tailWord_1886105) baseStart_1886105 baseEnd_1886105 := by
    simpa [prefixWord, tailWord_1886105, baseEnd_1886105] using wordTrace_append hprefix tailTrace_1886105
  have hstable : (prefixWord ++ tailWord_1886105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886105).length < 2 ^ (prefixWord ++ tailWord_1886105).sum := by decide
  have hdescent : baseEnd_1886105 < baseStart_1886105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886108 : List Nat := [2, 2, 3, 3, 1, 1, 11]
def baseStart_1886108 : Nat := 118140960795 + 1886108 * 2 ^ 59
def prefixEnd_1886108 : Nat := 4983230072969 + 3 ^ 40 * 1886108 * 2
def baseEnd_1886108 : Nat := 11956542843091504042913

theorem tailTrace_1886108 : CollatzResearch.WordTrace tailWord_1886108 prefixEnd_1886108 11956542843091504042913 := by
  unfold tailWord_1886108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396005125480156223049489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45861340167306874964065985 34396005125480156223049489)
  ·
    refine ⟨25797003844110117167287117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34396005125480156223049489 25797003844110117167287117)
    ·
      refine ⟨9673876441541293937732669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25797003844110117167287117 9673876441541293937732669)
      ·
        refine ⟨3627703665577985226649751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9673876441541293937732669 3627703665577985226649751)
        ·
          refine ⟨5441555498366977839974627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627703665577985226649751 5441555498366977839974627)
          ·
            refine ⟨8162333247550466759961941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441555498366977839974627 8162333247550466759961941)
            ·
              refine ⟨11956542843091504042913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8162333247550466759961941 11956542843091504042913)
              ·
                rfl

theorem cell23_1886108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 11].length) (baseStart_1886108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886108 prefixEnd_1886108 := by exact prefixLift 1886108
  have htrace : WordTrace (prefixWord ++ tailWord_1886108) baseStart_1886108 baseEnd_1886108 := by
    simpa [prefixWord, tailWord_1886108, baseEnd_1886108] using wordTrace_append hprefix tailTrace_1886108
  have hstable : (prefixWord ++ tailWord_1886108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886108).length < 2 ^ (prefixWord ++ tailWord_1886108).sum := by decide
  have hdescent : baseEnd_1886108 < baseStart_1886108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886119 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1886119 : Nat := 118140960795 + 1886119 * 2 ^ 59
def prefixEnd_1886119 : Nat := 4983230072969 + 3 ^ 40 * 1886119 * 2
def baseEnd_1886119 : Nat := 968485618577611284438403

theorem tailTrace_1886119 : CollatzResearch.WordTrace tailWord_1886119 prefixEnd_1886119 968485618577611284438403 := by
  unfold tailWord_1886119
  simp only [CollatzResearch.WordTrace]
  refine ⟨68792411453920461324749411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45861607635946974216499607 68792411453920461324749411)
  ·
    refine ⟨103188617180880691987124117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68792411453920461324749411 103188617180880691987124117)
    ·
      refine ⟨4836966430353782436896443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103188617180880691987124117 4836966430353782436896443)
      ·
        refine ⟨7255449645530673655344665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836966430353782436896443 7255449645530673655344665)
        ·
          refine ⟨5441587234148005241508499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255449645530673655344665 5441587234148005241508499)
          ·
            refine ⟨8162380851222007862262749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441587234148005241508499 8162380851222007862262749)
            ·
              refine ⟨3060892819208252948348531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8162380851222007862262749 3060892819208252948348531)
              ·
                refine ⟨4591339228812379422522797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060892819208252948348531 4591339228812379422522797)
                ·
                  refine ⟨1721752210804642283446049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4591339228812379422522797 1721752210804642283446049)
                  ·
                    refine ⟨1291314158103481712584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721752210804642283446049 1291314158103481712584537)
                    ·
                      refine ⟨968485618577611284438403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291314158103481712584537 968485618577611284438403)
                      ·
                        rfl

theorem cell23_1886119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1886119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886119 prefixEnd_1886119 := by exact prefixLift 1886119
  have htrace : WordTrace (prefixWord ++ tailWord_1886119) baseStart_1886119 baseEnd_1886119 := by
    simpa [prefixWord, tailWord_1886119, baseEnd_1886119] using wordTrace_append hprefix tailTrace_1886119
  have hstable : (prefixWord ++ tailWord_1886119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886119).length < 2 ^ (prefixWord ++ tailWord_1886119).sum := by decide
  have hdescent : baseEnd_1886119 < baseStart_1886119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886129 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 2, 4]
def baseStart_1886129 : Nat := 118140960795 + 1886129 * 2 ^ 59
def prefixEnd_1886129 : Nat := 4983230072969 + 3 ^ 40 * 1886129 * 2
def baseEnd_1886129 : Nat := 322830251128052081771119

theorem tailTrace_1886129 : CollatzResearch.WordTrace tailWord_1886129 prefixEnd_1886129 322830251128052081771119 := by
  unfold tailWord_1886129
  simp only [CollatzResearch.WordTrace]
  refine ⟨68792776183884233032613441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45861850789256155355075627 68792776183884233032613441)
  ·
    refine ⟨51594582137913174774460081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68792776183884233032613441 51594582137913174774460081)
    ·
      refine ⟨38695936603434881080845061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51594582137913174774460081 38695936603434881080845061)
      ·
        refine ⟨7255488113144040202658449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38695936603434881080845061 7255488113144040202658449)
        ·
          refine ⟨5441616084858030151993837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255488113144040202658449 5441616084858030151993837)
          ·
            refine ⟨2040606031821761306997689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5441616084858030151993837 2040606031821761306997689)
            ·
              refine ⟨1530454523866320980248267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040606031821761306997689 1530454523866320980248267)
              ·
                refine ⟨2295681785799481470372401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530454523866320980248267 2295681785799481470372401)
                ·
                  refine ⟨1721761339349611102779301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295681785799481470372401 1721761339349611102779301)
                  ·
                    refine ⟨322830251128052081771119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1721761339349611102779301 322830251128052081771119)
                    ·
                      rfl

theorem cell23_1886129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_1886129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886129 prefixEnd_1886129 := by exact prefixLift 1886129
  have htrace : WordTrace (prefixWord ++ tailWord_1886129) baseStart_1886129 baseEnd_1886129 := by
    simpa [prefixWord, tailWord_1886129, baseEnd_1886129] using wordTrace_append hprefix tailTrace_1886129
  have hstable : (prefixWord ++ tailWord_1886129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886129).length < 2 ^ (prefixWord ++ tailWord_1886129).sum := by decide
  have hdescent : baseEnd_1886129 < baseStart_1886129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886168 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_1886168 : Nat := 118140960795 + 1886168 * 2 ^ 59
def prefixEnd_1886168 : Nat := 4983230072969 + 3 ^ 40 * 1886168 * 2
def baseEnd_1886168 : Nat := 322836926376560530908559

theorem tailTrace_1886168 : CollatzResearch.WordTrace tailWord_1886168 prefixEnd_1886168 322836926376560530908559 := by
  unfold tailWord_1886168
  simp only [CollatzResearch.WordTrace]
  refine ⟨34397099315371471346641579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45862799087161961795522105 34397099315371471346641579)
  ·
    refine ⟨51595648973057207019962369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34397099315371471346641579 51595648973057207019962369)
    ·
      refine ⟨38696736729792905264971777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51595648973057207019962369 38696736729792905264971777)
      ·
        refine ⟨29022552547344678948728833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38696736729792905264971777 29022552547344678948728833)
        ·
          refine ⟨21766914410508509211546625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29022552547344678948728833 21766914410508509211546625)
          ·
            refine ⟨16325185807881381908659969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21766914410508509211546625 16325185807881381908659969)
            ·
              refine ⟨12243889355911036431494977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16325185807881381908659969 12243889355911036431494977)
              ·
                refine ⟨9182917016933277323621233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243889355911036431494977 9182917016933277323621233)
                ·
                  refine ⟨6887187762699957992715925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182917016933277323621233 6887187762699957992715925)
                  ·
                    refine ⟨322836926376560530908559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6887187762699957992715925 322836926376560530908559)
                    ·
                      rfl

theorem cell23_1886168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_1886168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886168 prefixEnd_1886168 := by exact prefixLift 1886168
  have htrace : WordTrace (prefixWord ++ tailWord_1886168) baseStart_1886168 baseEnd_1886168 := by
    simpa [prefixWord, tailWord_1886168, baseEnd_1886168] using wordTrace_append hprefix tailTrace_1886168
  have hstable : (prefixWord ++ tailWord_1886168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886168).length < 2 ^ (prefixWord ++ tailWord_1886168).sum := by decide
  have hdescent : baseEnd_1886168 < baseStart_1886168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886169 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 3]
def baseStart_1886169 : Nat := 118140960795 + 1886169 * 2 ^ 59
def prefixEnd_1886169 : Nat := 4983230072969 + 3 ^ 40 * 1886169 * 2
def baseEnd_1886169 : Nat := 968511292610336088813173

theorem tailTrace_1886169 : CollatzResearch.WordTrace tailWord_1886169 prefixEnd_1886169 968511292610336088813173 := by
  unfold tailWord_1886169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68794235103739319864069561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45862823402492879909379707 68794235103739319864069561)
  ·
    refine ⟨51595676327804489898052171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68794235103739319864069561 51595676327804489898052171)
    ·
      refine ⟨77393514491706734847078257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51595676327804489898052171 77393514491706734847078257)
      ·
        refine ⟨58045135868780051135308693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77393514491706734847078257 58045135868780051135308693)
        ·
          refine ⟨2720865743849064896967595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58045135868780051135308693 2720865743849064896967595)
          ·
            refine ⟨4081298615773597345451393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720865743849064896967595 4081298615773597345451393)
            ·
              refine ⟨3060973961830198009088545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081298615773597345451393 3060973961830198009088545)
              ·
                refine ⟨2295730471372648506816409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060973961830198009088545 2295730471372648506816409)
                ·
                  refine ⟨1721797853529486380112307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295730471372648506816409 1721797853529486380112307)
                  ·
                    refine ⟨2582696780294229570168461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1721797853529486380112307 2582696780294229570168461)
                    ·
                      refine ⟨968511292610336088813173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2582696780294229570168461 968511292610336088813173)
                      ·
                        rfl

theorem cell23_1886169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_1886169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886169 prefixEnd_1886169 := by exact prefixLift 1886169
  have htrace : WordTrace (prefixWord ++ tailWord_1886169) baseStart_1886169 baseEnd_1886169 := by
    simpa [prefixWord, tailWord_1886169, baseEnd_1886169] using wordTrace_append hprefix tailTrace_1886169
  have hstable : (prefixWord ++ tailWord_1886169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886169).length < 2 ^ (prefixWord ++ tailWord_1886169).sum := by decide
  have hdescent : baseEnd_1886169 < baseStart_1886169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886170 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2]
def baseStart_1886170 : Nat := 118140960795 + 1886170 * 2 ^ 59
def prefixEnd_1886170 : Nat := 4983230072969 + 3 ^ 40 * 1886170 * 2
def baseEnd_1886170 : Nat := 968511806090990584900669

theorem tailTrace_1886170 : CollatzResearch.WordTrace tailWord_1886170 prefixEnd_1886170 968511806090990584900669 := by
  unfold tailWord_1886170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198567894183924258713991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45862847717823798023237309 17198567894183924258713991)
  ·
    refine ⟨25797851841275886388070987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17198567894183924258713991 25797851841275886388070987)
    ·
      refine ⟨38696777761913829582106481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25797851841275886388070987 38696777761913829582106481)
      ·
        refine ⟨29022583321435372186579861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38696777761913829582106481 29022583321435372186579861)
        ·
          refine ⟨1360433593192283071245931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29022583321435372186579861 1360433593192283071245931)
          ·
            refine ⟨2040650389788424606868897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360433593192283071245931 2040650389788424606868897)
            ·
              refine ⟨1530487792341318455151673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040650389788424606868897 1530487792341318455151673)
              ·
                refine ⟨1147865844255988841363755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530487792341318455151673 1147865844255988841363755)
                ·
                  refine ⟨1721798766383983262045633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147865844255988841363755 1721798766383983262045633)
                  ·
                    refine ⟨1291349074787987446534225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1721798766383983262045633 1291349074787987446534225)
                    ·
                      refine ⟨968511806090990584900669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291349074787987446534225 968511806090990584900669)
                      ·
                        rfl

theorem cell23_1886170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_1886170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886170 prefixEnd_1886170 := by exact prefixLift 1886170
  have htrace : WordTrace (prefixWord ++ tailWord_1886170) baseStart_1886170 baseEnd_1886170 := by
    simpa [prefixWord, tailWord_1886170, baseEnd_1886170] using wordTrace_append hprefix tailTrace_1886170
  have hstable : (prefixWord ++ tailWord_1886170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886170).length < 2 ^ (prefixWord ++ tailWord_1886170).sum := by decide
  have hdescent : baseEnd_1886170 < baseStart_1886170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886235 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 5, 2]
def baseStart_1886235 : Nat := 118140960795 + 1886235 * 2 ^ 59
def prefixEnd_1886235 : Nat := 4983230072969 + 3 ^ 40 * 1886235 * 2
def baseEnd_1886235 : Nat := 968545182333532830587869

theorem tailTrace_1886235 : CollatzResearch.WordTrace tailWord_1886235 prefixEnd_1886235 968545182333532830587869 := by
  unfold tailWord_1886235
  simp only [CollatzResearch.WordTrace]
  refine ⟨68796642321500213135972159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45864428214333475423981439 68796642321500213135972159)
  ·
    refine ⟨103194963482250319703958239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68796642321500213135972159 103194963482250319703958239)
    ·
      refine ⟨154792445223375479555937359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103194963482250319703958239 154792445223375479555937359)
      ·
        refine ⟨232188667835063219333906039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154792445223375479555937359 232188667835063219333906039)
        ·
          refine ⟨348283001752594829000859059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232188667835063219333906039 348283001752594829000859059)
          ·
            refine ⟨522424502628892243501288589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348283001752594829000859059 522424502628892243501288589)
            ·
              refine ⟨195909188485834591312983221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522424502628892243501288589 195909188485834591312983221)
              ·
                refine ⟨18366486420546992935592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195909188485834591312983221 18366486420546992935592177)
                ·
                  refine ⟨13774864815410244701694133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18366486420546992935592177 13774864815410244701694133)
                  ·
                    refine ⟨1291393576444710440783825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13774864815410244701694133 1291393576444710440783825)
                    ·
                      refine ⟨968545182333532830587869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291393576444710440783825 968545182333532830587869)
                      ·
                        rfl

theorem cell23_1886235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5, 2].length) (baseStart_1886235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886235 prefixEnd_1886235 := by exact prefixLift 1886235
  have htrace : WordTrace (prefixWord ++ tailWord_1886235) baseStart_1886235 baseEnd_1886235 := by
    simpa [prefixWord, tailWord_1886235, baseEnd_1886235] using wordTrace_append hprefix tailTrace_1886235
  have hstable : (prefixWord ++ tailWord_1886235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886235).length < 2 ^ (prefixWord ++ tailWord_1886235).sum := by decide
  have hdescent : baseEnd_1886235 < baseStart_1886235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886262 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1886262 : Nat := 118140960795 + 1886262 * 2 ^ 59
def prefixEnd_1886262 : Nat := 4983230072969 + 3 ^ 40 * 1886262 * 2
def baseEnd_1886262 : Nat := 322853015437068074983415

theorem tailTrace_1886262 : CollatzResearch.WordTrace tailWord_1886262 prefixEnd_1886262 322853015437068074983415 := by
  unfold tailWord_1886262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299851693275149796700315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45865084728268264498136693 4299851693275149796700315)
  ·
    refine ⟨6449777539912724695050473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299851693275149796700315 6449777539912724695050473)
    ·
      refine ⟨4837333154934543521287855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6449777539912724695050473 4837333154934543521287855)
      ·
        refine ⟨7255999732401815281931783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837333154934543521287855 7255999732401815281931783)
        ·
          refine ⟨10883999598602722922897675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255999732401815281931783 10883999598602722922897675)
          ·
            refine ⟨16325999397904084384346513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10883999598602722922897675 16325999397904084384346513)
            ·
              refine ⟨12244499548428063288259885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16325999397904084384346513 12244499548428063288259885)
              ·
                refine ⟨4591687330660523733097457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12244499548428063288259885 4591687330660523733097457)
                ·
                  refine ⟨3443765497995392799823093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591687330660523733097457 3443765497995392799823093)
                  ·
                    refine ⟨322853015437068074983415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3443765497995392799823093 322853015437068074983415)
                    ·
                      rfl

theorem cell23_1886262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1886262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886262 prefixEnd_1886262 := by exact prefixLift 1886262
  have htrace : WordTrace (prefixWord ++ tailWord_1886262) baseStart_1886262 baseEnd_1886262 := by
    simpa [prefixWord, tailWord_1886262, baseEnd_1886262] using wordTrace_append hprefix tailTrace_1886262
  have hstable : (prefixWord ++ tailWord_1886262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886262).length < 2 ^ (prefixWord ++ tailWord_1886262).sum := by decide
  have hdescent : baseEnd_1886262 < baseStart_1886262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886425 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_1886425 : Nat := 118140960795 + 1886425 * 2 ^ 59
def prefixEnd_1886425 : Nat := 4983230072969 + 3 ^ 40 * 1886425 * 2
def baseEnd_1886425 : Nat := 322880914552629029070665

theorem tailTrace_1886425 : CollatzResearch.WordTrace tailWord_1886425 prefixEnd_1886425 322880914552629029070665 := by
  unfold tailWord_1886425
  simp only [CollatzResearch.WordTrace]
  refine ⟨68803572190811875585388729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45869048127207917056925819 68803572190811875585388729)
  ·
    refine ⟨51602679143108906689041547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68803572190811875585388729 51602679143108906689041547)
    ·
      refine ⟨77404018714663360033562321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51602679143108906689041547 77404018714663360033562321)
      ·
        refine ⟨58053014035997520025171741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77404018714663360033562321 58053014035997520025171741)
        ·
          refine ⟨21769880263499070009439403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58053014035997520025171741 21769880263499070009439403)
          ·
            refine ⟨32654820395248605014159105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21769880263499070009439403 32654820395248605014159105)
            ·
              refine ⟨24491115296436453760619329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32654820395248605014159105 24491115296436453760619329)
              ·
                refine ⟨18368336472327340320464497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24491115296436453760619329 18368336472327340320464497)
                ·
                  refine ⟨13776252354245505240348373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18368336472327340320464497 13776252354245505240348373)
                  ·
                    refine ⟨322880914552629029070665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13776252354245505240348373 322880914552629029070665)
                    ·
                      rfl

theorem cell23_1886425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_1886425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886425 prefixEnd_1886425 := by exact prefixLift 1886425
  have htrace : WordTrace (prefixWord ++ tailWord_1886425) baseStart_1886425 baseEnd_1886425 := by
    simpa [prefixWord, tailWord_1886425, baseEnd_1886425] using wordTrace_append hprefix tailTrace_1886425
  have hstable : (prefixWord ++ tailWord_1886425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886425).length < 2 ^ (prefixWord ++ tailWord_1886425).sum := by decide
  have hdescent : baseEnd_1886425 < baseStart_1886425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886429 : List Nat := [1, 4, 3, 2, 1, 1, 4, 7]
def baseStart_1886429 : Nat := 118140960795 + 1886429 * 2 ^ 59
def prefixEnd_1886429 : Nat := 4983230072969 + 3 ^ 40 * 1886429 * 2
def baseEnd_1886429 : Nat := 35875733243722410057851

theorem tailTrace_1886429 : CollatzResearch.WordTrace tailWord_1886429 prefixEnd_1886429 35875733243722410057851 := by
  unfold tailWord_1886429
  simp only [CollatzResearch.WordTrace]
  refine ⟨68803718082797384268534341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45869145388531589512356227 68803718082797384268534341)
  ·
    refine ⟨12900697140524509550350189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68803718082797384268534341 12900697140524509550350189)
    ·
      refine ⟨4837761427696691081381321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12900697140524509550350189 4837761427696691081381321)
      ·
        refine ⟨3628321070772518311035991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837761427696691081381321 3628321070772518311035991)
        ·
          refine ⟨5442481606158777466553987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628321070772518311035991 5442481606158777466553987)
          ·
            refine ⟨8163722409238166199830981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442481606158777466553987 8163722409238166199830981)
            ·
              refine ⟨1530697951732156162468309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8163722409238166199830981 1530697951732156162468309)
              ·
                refine ⟨35875733243722410057851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1530697951732156162468309 35875733243722410057851)
                ·
                  rfl

theorem cell23_1886429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 7].length) (baseStart_1886429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886429 prefixEnd_1886429 := by exact prefixLift 1886429
  have htrace : WordTrace (prefixWord ++ tailWord_1886429) baseStart_1886429 baseEnd_1886429 := by
    simpa [prefixWord, tailWord_1886429, baseEnd_1886429] using wordTrace_append hprefix tailTrace_1886429
  have hstable : (prefixWord ++ tailWord_1886429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886429).length < 2 ^ (prefixWord ++ tailWord_1886429).sum := by decide
  have hdescent : baseEnd_1886429 < baseStart_1886429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
